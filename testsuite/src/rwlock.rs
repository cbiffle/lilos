// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use core::pin::pin;

use lilos_rwlock::RwLock;

use crate::{poll_and_assert_not_ready, poll_and_assert_ready};

pub async fn test_create_drop() {
    let _a_lock = pin!(RwLock::new(0u32));
}

pub async fn test_uncontended_try_lock_shared() {
    let a_lock = pin!(RwLock::new(0u32));
    let a_lock = a_lock.into_ref();
    let guard1 = a_lock.try_lock_shared()
        .expect("uncontended lock should succeed");
    assert!(a_lock.try_lock_exclusive().is_err());
    let guard2 = a_lock.try_lock_shared()
        .expect("second reader lock should succeed");

    assert_eq!(*guard1, *guard2);
    drop(guard1);
    assert!(a_lock.try_lock_exclusive().is_err());
    drop(guard2);
    assert!(a_lock.try_lock_exclusive().is_ok());
}

pub async fn test_uncontended_try_lock_exclusive() {
    let a_lock = pin!(RwLock::new(0u32));
    let a_lock = a_lock.into_ref();
    let guard1 = a_lock.try_lock_exclusive()
        .expect("uncontended lock-exclusive should succeed");

    assert!(a_lock.try_lock_exclusive().is_err());
    assert!(a_lock.try_lock_shared().is_err());

    guard1.perform(|value| *value += 1);

    a_lock.try_lock_exclusive()
        .expect("lock should now be free")
        .perform(|value| assert_eq!(*value, 1));
}

pub async fn test_blocking() {
    let a_lock = pin!(RwLock::new(0u32));
    let a_lock = a_lock.into_ref();

    let guard1 = a_lock.lock_shared().await;
    let guard2 = a_lock.lock_shared().await;

    {
        let mut exc = pin!(a_lock.lock_exclusive());
        // Exclusive lock should not complete while shared locks are
        // outstanding.
        assert!(futures::poll!(exc.as_mut()).is_pending());
        // Even on the second poll (since this is a different code path).
        assert!(futures::poll!(exc.as_mut()).is_pending());

        // Now that that exclusive lock is queued, we must not be able to lock
        // shared, either.
        assert!(a_lock.try_lock_shared().is_err());
    }

    drop(guard1);

    {
        let mut exc = pin!(a_lock.lock_exclusive());
        // Exclusive lock should not complete while shared locks are
        // outstanding.
        assert!(futures::poll!(exc.as_mut()).is_pending());
        // Even on the second poll (since this is a different code path).
        assert!(futures::poll!(exc.as_mut()).is_pending());
    }

    drop(guard2);

    let eguard = a_lock.lock_exclusive().await;

    {
        let mut sh = pin!(a_lock.lock_shared());
        // Shared lock should not complete while exclusive locks are
        // outstanding.
        assert!(futures::poll!(sh.as_mut()).is_pending());
        // Even on the second poll (since this is a different code path).
        assert!(futures::poll!(sh.as_mut()).is_pending());
    }

    drop(eguard);

    let _ = a_lock.lock_shared().await;
}

/// Verify that claims are granted in the order they are received, and that
/// shared claims are always coalesced even if they were once separated by an
/// exclusive claim, since-cancelled.
pub async fn test_fairness() {
    let a_lock = pin!(RwLock::new(0u32));
    let a_lock = a_lock.into_ref();

    // E1 S1 S2 E2 S3 S4 E3 S5
    //          ^--- will be removed

    // Acquire the lock exclusively so that we can have some shared claims pile
    // up.
    let guard_e1 = a_lock.lock_exclusive().await;

    // The order of _creation_ here is a little counter-intuitive: first we'll
    // create all the futures that will eventually resolve, and _then_ we'll
    // create the one being cancelled. This lets us drop the cancelled one when
    // it needs to be dropped. Recall that the order of _creation_ of the
    // futures is immaterial, only the time of first poll matters to the list
    // ordering.

    let mut s1 = pin!(a_lock.lock_shared());
    let mut s2 = pin!(a_lock.lock_shared());
    let mut s3 = pin!(a_lock.lock_shared());
    let mut s4 = pin!(a_lock.lock_shared());
    let mut s5 = pin!(a_lock.lock_shared());

    let mut e3 = pin!(a_lock.lock_exclusive());

    let guard_s1;
    let guard_s2;
    {
        // Okay, now finally create the e2 future, inside a nested scope so that
        // it can be dropped easily.
        let mut e2 = pin!(a_lock.lock_exclusive());

        // Pile up those shared claims.
        poll_and_assert_not_ready!(s1);
        poll_and_assert_not_ready!(s2);
        // Insert one exclusive claim.
        poll_and_assert_not_ready!(e2);
        // Two more shared.
        poll_and_assert_not_ready!(s3);
        poll_and_assert_not_ready!(s4);
        // Finally the stragglers.
        poll_and_assert_not_ready!(e3);
        poll_and_assert_not_ready!(s5);

        // We now release the first exclusive claim, causing S1/S2 to be
        // granted. We check them in reverse order to ensure that order doesn't
        // matter.
        drop(guard_e1);
        guard_s2 = poll_and_assert_ready!(s2);
        guard_s1 = poll_and_assert_ready!(s1);

        // Now we will drop the intervening exclusive claim.
    }
    // s3/s4 should have been automatically granted.
    let guard_s4 = poll_and_assert_ready!(s4);
    let guard_s3 = poll_and_assert_ready!(s3);
    // But not the stragglers.
    poll_and_assert_not_ready!(e3);
    poll_and_assert_not_ready!(s5);

    drop((guard_s1, guard_s2, guard_s3, guard_s4));

    let guard_e3 = poll_and_assert_ready!(e3);
    poll_and_assert_not_ready!(s5);
    drop(guard_e3);
    let _ = poll_and_assert_ready!(s5);
}

/*
pub async fn test_acquire() {
    create_semaphore!(a_semaphore, 10);
    a_semaphore.acquire().await;
    assert_eq!(a_semaphore.permits_available(), 9);
}

pub async fn test_release() {
    create_semaphore!(a_semaphore, 10);
    a_semaphore.release();
    assert_eq!(a_semaphore.permits_available(), 11);
}

pub async fn test_exhaustion() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    a_semaphore.acquire().await;

    // Ensure that we can't get a second one.
    {
        let acq = pin!(a_semaphore.acquire());
        if futures::poll!(acq).is_ready() {
            panic!("acquire resolved and shouldn't've");
        };
    }
    // But not forever.
    a_semaphore.release();
    a_semaphore.acquire().await;
}

pub async fn test_fairness() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    a_semaphore.acquire().await;

    // Try and take it twice more.
    let mut first_acq = pin!(a_semaphore.acquire());
    let mut second_acq = pin!(a_semaphore.acquire());

    // Neither of these futures should complete yet.
    assert!(futures::poll!(first_acq.as_mut()).is_pending());
    assert!(futures::poll!(second_acq.as_mut()).is_pending());

    // Yield a permit.
    a_semaphore.release();

    // A third challenger appears!
    let mut third_acq = pin!(a_semaphore.acquire());
    assert!(futures::poll!(third_acq.as_mut()).is_pending());

    // The _second_ waiter should still not complete, even if called first.
    assert!(futures::poll!(second_acq.as_mut()).is_pending());
    // Nor the third.
    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    // But the first should.
    assert!(futures::poll!(first_acq.as_mut()).is_ready(),
        "first taker should have completed now");

    // This should cause no changes to the others.
    assert!(futures::poll!(second_acq.as_mut()).is_pending());
    assert!(futures::poll!(third_acq.as_mut()).is_pending());

    // Alright, now let's unwind the other two.
    a_semaphore.release();
    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    assert!(futures::poll!(second_acq.as_mut()).is_ready(),
        "second taker should have completed now");

    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    a_semaphore.release();
    assert!(futures::poll!(third_acq.as_mut()).is_ready(),
        "third taker should have completed now");
}

pub async fn test_cancellation() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    a_semaphore.acquire().await;

    assert_eq!(a_semaphore.permits_available(), 0);

    {
        let mut acq = pin!(a_semaphore.acquire());
        // poll it to join the waitlist.
        assert!(futures::poll!(acq.as_mut()).is_pending());

        assert_eq!(a_semaphore.permits_available(), 0);

        a_semaphore.release();

        // Still zero because the permit was directly transferred.
        assert_eq!(a_semaphore.permits_available(), 0);

        // acquiring future gets dropped before being polled
    }

    assert_eq!(a_semaphore.permits_available(), 1);
}

// Scoped semaphore tests start here.
//
// Because ScopedSemaphore is a thin wrapper around Semaphore, I don't feel the
// need to do detailed testing of things like cancel semantics and fairness,
// which should Just Work. So, just gonna do basics:

pub async fn test_scoped_create_drop() {
    create_scoped_semaphore!(_a_semaphore, 10);
}

pub async fn test_scoped_acquire() {
    create_scoped_semaphore!(a_semaphore, 10);
    let _permit = a_semaphore.acquire().await;
    assert_eq!(a_semaphore.permits_available(), 9);
}

pub async fn test_scoped_release() {
    create_scoped_semaphore!(a_semaphore, 10);
    a_semaphore.out_of_band_release(1);
    assert_eq!(a_semaphore.permits_available(), 11);
}

pub async fn test_scoped_exhaustion() {
    // Start out with a permit.
    create_scoped_semaphore!(a_semaphore, 1);

    // Take it.
    let _permit = a_semaphore.acquire().await;

    // Ensure that we can't get a second one.
    {
        let acq = pin!(a_semaphore.acquire());
        if futures::poll!(acq).is_ready() {
            panic!("acquire resolved and shouldn't've");
        };
    }
    // But not forever.
    drop(_permit);
    let _ = a_semaphore.acquire().await;
}
*/

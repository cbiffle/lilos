// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use core::pin::pin;

use lilos_semaphore::{Semaphore, ScopedSemaphore};

pub async fn test_create_drop() {
    let _a_semaphore = pin!(Semaphore::new(10));
    let _a_semaphore = _a_semaphore.into_ref();
}

pub async fn test_acquire() {
    let a_semaphore = pin!(Semaphore::new(10));
    let a_semaphore = a_semaphore.into_ref();
    a_semaphore.acquire().await;
    assert_eq!(a_semaphore.permits_available(), 9);
}

pub async fn test_release() {
    let a_semaphore = pin!(Semaphore::new(10));
    let a_semaphore = a_semaphore.into_ref();
    a_semaphore.release();
    assert_eq!(a_semaphore.permits_available(), 11);
}

pub async fn test_exhaustion() {
    // Start out with a permit.
    let a_semaphore = pin!(Semaphore::new(1));
    let a_semaphore = a_semaphore.into_ref();

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
    let a_semaphore = pin!(Semaphore::new(1));
    let a_semaphore = a_semaphore.into_ref();

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
    let a_semaphore = pin!(Semaphore::new(1));
    let a_semaphore = a_semaphore.into_ref();

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
    let _a_semaphore = pin!(ScopedSemaphore::new(10));
    let _a_semaphore = _a_semaphore.into_ref();
}

pub async fn test_scoped_acquire() {
    let a_semaphore = pin!(ScopedSemaphore::new(10));
    let a_semaphore = a_semaphore.into_ref();
    let _permit = a_semaphore.acquire().await;
    assert_eq!(a_semaphore.permits_available(), 9);
}

pub async fn test_scoped_release() {
    let a_semaphore = pin!(ScopedSemaphore::new(10));
    let a_semaphore = a_semaphore.into_ref();
    a_semaphore.out_of_band_release(1);
    assert_eq!(a_semaphore.permits_available(), 11);
}

pub async fn test_scoped_exhaustion() {
    // Start out with a permit.
    let a_semaphore = pin!(ScopedSemaphore::new(1));
    let a_semaphore = a_semaphore.into_ref();

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

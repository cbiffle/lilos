use core::pin::Pin;
use core::task::Poll;

use lilos::{create_mutex, create_static_mutex, mutex::Mutex, mutex::CancelSafe};
use crate::A_BIT;

pub async fn test_stack() {
    create_mutex!(mutex, CancelSafe(42_usize));
    test_mutex_wherever(mutex).await
}

pub async fn test_static() {
    let mutex = create_static_mutex!(CancelSafe<usize>, CancelSafe(42_usize));
    test_mutex_wherever(mutex).await
}

async fn test_mutex_wherever(mutex: Pin<&Mutex<CancelSafe<usize>>>) {
    futures::join!(
        async {
            let mut g = mutex.lock_assuming_cancel_safe().await;
            // Sleep a bit to ensure that the mutex experiences contention.
            lilos::time::sleep_for(&lilos::time::SysTickTimer, A_BIT).await;
            *g += 1;
        },
        async {
            let mut g = mutex.lock_assuming_cancel_safe().await;
            lilos::time::sleep_for(&lilos::time::SysTickTimer, A_BIT).await;
            *g += 2;
        },
        async {
            mutex.lock().await.perform(|x| x.0 += 5)
        },
    );

    assert_eq!(mutex.lock().await.perform(|x| x.0), 42 + 2 + 1 + 5);
}

pub async fn test_lock_cancel_before_poll() {
    create_mutex!(mutex, CancelSafe(()));
    drop(mutex.lock());

    // Ensure that we can lock it again
    mutex.lock().await;
}

pub async fn test_lock_cancel_while_blocked() {
    create_mutex!(mutex, CancelSafe(()));

    // Lock the by-definition-uncontended mutex.
    let held = mutex.lock().await;

    {
        // Now, try and lock it with contention.
        let contender = mutex.lock();
        futures::pin_mut!(contender);
        // Should not get the mutex.
        assert!(matches!(futures::poll!(contender), Poll::Pending));
        // Cancel it before it succeeds.
    }

    // Now, unlock the mutex.
    drop(held);

    // Ensure that we can lock it again
    mutex.lock().await;
}

/// Ensure that the mutex is acquired in the order that the lock futures are
/// initially polled, independent of the order of polling after that point.
pub async fn test_fairness() {
    create_mutex!(mutex, CancelSafe(()));

    // Initially lock the mutex.
    let held = mutex.lock().await;

    let waiter1 = mutex.lock();
    futures::pin_mut!(waiter1);
    let _ = futures::poll!(waiter1.as_mut());

    let waiter2 = mutex.lock();
    futures::pin_mut!(waiter2);
    let _ = futures::poll!(waiter2.as_mut());

    // Release initial lock...
    drop(held);
    // Introduce a new waiter, who never sees the initial lock. They still
    // should not be able to acquire the mutex.
    let waiter3 = mutex.lock();
    futures::pin_mut!(waiter3);
    // Poll everybody _but_ the one who should have the mutex
    assert!(matches!(futures::poll!(waiter3.as_mut()), Poll::Pending));
    assert!(matches!(futures::poll!(waiter2.as_mut()), Poll::Pending));

    // but waiter1 should get it.
    let locked1 = waiter1.await;
    drop(locked1);

    // waiter3 should still be waiter-ing
    assert!(matches!(futures::poll!(waiter3.as_mut()), Poll::Pending));
    // and waiter2 is now first in line.
    let locked2 = waiter2.await;
    drop(locked2);

    // Only now does waiter3 get it.
    waiter3.await;
}

/// Ensure that a future that acquires the mutex but is dropped before being
/// polled passes it on to the next waiter.
pub async fn test_rewake_on_cancel() {
    create_mutex!(mutex, CancelSafe(()));

    // Initially lock the mutex.
    let held = mutex.lock().await;

    // lock() itself has no side effects, so we're going to create the waiter
    // futures in the reverse order that we want to drop them. Otherwise it's
    // hard to drop a pinned value.
    let waiter2 = mutex.lock();
    futures::pin_mut!(waiter2);
    {
        let waiter1 = mutex.lock();
        futures::pin_mut!(waiter1);

        // waiter1 blocks on the mutex.
        let _ = futures::poll!(waiter1.as_mut());
        // waiter2 blocks on the mutex
        let _ = futures::poll!(waiter2.as_mut());

        // Release initial lock...
        drop(held);

        // waiter1 now holds the mutex but doesn't know it yet. And they never
        // will! Mwa ha ha ha!
    }
    // waiter2 should now have the mutex.
    let w2r = futures::poll!(waiter2);
    assert!(matches!(w2r, Poll::Ready(_)));
}

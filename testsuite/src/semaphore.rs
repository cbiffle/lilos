use core::{pin::pin, task::Poll};

use lilos_semaphore::create_semaphore;

pub async fn test_create_drop() {
    create_semaphore!(_a_semaphore, 10);
}

pub async fn test_acquire_release() {
    create_semaphore!(a_semaphore, 10);

    let permit = a_semaphore.acquire().await;
    drop(permit);
}

pub async fn test_exhaustion() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    let permit = a_semaphore.acquire().await;

    // Ensure that we can't get a second one.
    {
        let acq = pin!(a_semaphore.acquire());
        if let Poll::Ready(_) = futures::poll!(acq) {
            panic!("acquire resolved and shouldn't've");
        };
    }
    // But not forever.
    drop(permit);
    let _permit = a_semaphore.acquire().await;
}

pub async fn test_fairness() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    let permit = a_semaphore.acquire().await;

    // Try and take it twice more.
    let mut first_acq = pin!(a_semaphore.acquire());
    let mut second_acq = pin!(a_semaphore.acquire());

    // Neither of these futures should complete yet.
    assert!(futures::poll!(first_acq.as_mut()).is_pending());
    assert!(futures::poll!(second_acq.as_mut()).is_pending());

    // Yield a permit.
    drop(permit);

    // A third challenger appears!
    let mut third_acq = pin!(a_semaphore.acquire());
    assert!(futures::poll!(third_acq.as_mut()).is_pending());

    // The _second_ waiter should still not complete, even if called first.
    assert!(futures::poll!(second_acq.as_mut()).is_pending());
    // Nor the third.
    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    // But the first should.
    let Poll::Ready(permit) = futures::poll!(first_acq.as_mut()) else {
        panic!("first taker should have completed now");
    };
    // This should cause no changes to the others.
    assert!(futures::poll!(second_acq.as_mut()).is_pending());
    assert!(futures::poll!(third_acq.as_mut()).is_pending());

    // Alright, now let's unwind the other two.
    drop(permit);
    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    let Poll::Ready(permit) = futures::poll!(second_acq.as_mut()) else {
        panic!("second taker should have completed now");
    };
    assert!(futures::poll!(third_acq.as_mut()).is_pending());
    drop(permit);
    let Poll::Ready(_) = futures::poll!(third_acq.as_mut()) else {
        panic!("third taker should have completed now");
    };
}

pub async fn test_cancellation() {
    // Start out with a permit.
    create_semaphore!(a_semaphore, 1);

    // Take it.
    let permit = a_semaphore.acquire().await;

    assert_eq!(a_semaphore.permits_available(), 0);

    {
        let mut acq = pin!(a_semaphore.acquire());
        // poll it to join the waitlist.
        assert!(futures::poll!(acq.as_mut()).is_pending());

        assert_eq!(a_semaphore.permits_available(), 0);

        drop(permit);

        // Still zero because the permit was directly transferred.
        assert_eq!(a_semaphore.permits_available(), 0);
    }

    assert_eq!(a_semaphore.permits_available(), 1);
}

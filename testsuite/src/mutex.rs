use core::pin::Pin;

use lilos::{create_mutex, create_static_mutex, mutex::Mutex};
use crate::A_BIT;

pub async fn test_stack() {
    create_mutex!(mutex, 42_usize);
    test_mutex_wherever(mutex).await
}

pub async fn test_static() {
    let mutex = create_static_mutex!(usize, 42_usize);
    test_mutex_wherever(mutex).await
}

async fn test_mutex_wherever(mutex: Pin<&Mutex<usize>>) {
    futures::join!(
        async {
            let mut g = mutex.lock().await;
            // Sleep a bit to ensure that the mutex experiences contention.
            lilos::exec::sleep_for(A_BIT).await;
            *g += 1;
        },
        async {
            let mut g = mutex.lock().await;
            lilos::exec::sleep_for(A_BIT).await;
            *g += 2;
        },
    );

    assert_eq!(*mutex.lock().await, 42 + 2 + 1);
}


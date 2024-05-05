use core::pin::pin;

use lilos_watch::Watch;

use crate::{poll_and_assert_not_ready, poll_and_assert_ready};

pub async fn test_receive_only() {
    let w = Watch::new(123_u32);
    
    let mut receiver = w.subscribe();

    receiver.glimpse(|&value| assert_eq!(value, 123_u32));

    {
        let mut change_fut = pin!(receiver.changed());
        poll_and_assert_not_ready!(change_fut.as_mut());
        poll_and_assert_not_ready!(change_fut.as_mut());
    }

    receiver.mark_as_unseen();

    {
        let mut change_fut = pin!(receiver.changed());
        poll_and_assert_ready!(change_fut.as_mut());
    }
}

pub async fn test_send_receive() {
    let w = Watch::new(123_u32);
    
    let sender = w.sender();
    let mut receiver = w.subscribe();

    poll_and_assert_not_ready!(pin!(receiver.changed()));

    sender.send(456_u32);

    poll_and_assert_ready!(pin!(receiver.changed()));
    receiver.glimpse(|&value| assert_eq!(value, 456_u32));
}

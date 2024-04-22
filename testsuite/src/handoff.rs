use lilos_handoff::Handoff;

pub async fn test_create_drop() {
    let handoff = Handoff::<usize>::new(); 
    drop(handoff);
}

pub async fn test_split_drop() {
    let mut handoff = Handoff::<usize>::new(); 
    {
        let (_push, _pop) = handoff.split();
    }
    drop(handoff);
}

pub async fn test_push_pop() {
    let mut handoff = Handoff::<usize>::new(); 
    let (mut push, mut pop) = handoff.split();

    let mut xfer_val = None;
    futures::join! {
        async {
            push.push(42).await;
        },
        async {
            xfer_val = Some(pop.pop().await);
        },
    };

    assert_eq!(xfer_val, Some(42));
}

pub async fn test_push_cancel() {
    let mut handoff = Handoff::<usize>::new(); 
    let (mut push, _pop) = handoff.split();

    drop(push.push(42));
    // Checks in Push and Handoff should not fire
}

pub async fn test_push_cancel_after_block() {
    let mut handoff = Handoff::<usize>::new(); 
    let (mut push, _pop) = handoff.split();

    let pp = push.push(42);
    futures::pin_mut!(pp);
    // Push future gets polled. No peer is available. It now knows to block.
    let _ = futures::poll!(pp);

    // As it gets dropped, it should unblock, checks should not fire.
}

pub async fn test_push_cancel_after_success() {
    let mut handoff = Handoff::<usize>::new(); 
    let (mut push, mut pop) = handoff.split();

    let pp = push.push(42);
    futures::pin_mut!(pp);
    // Push future gets polled. No peer is available. It now knows to block.
    let _ = futures::poll!(pp);

    // Pop comes along and empties it.
    assert_eq!(pop.pop().await, 42);

    // Now before getting polled, we cancel it.
    // As it gets dropped, it should unblock, checks should not fire.
}

pub async fn test_pop_cancel() {
    let mut handoff = Handoff::<usize>::new(); 
    let (_push, mut pop) = handoff.split();

    drop(pop.pop());
    // Checks in Pop and Handoff should not fire
}

pub async fn test_pop_cancel_after_block() {
    let mut handoff = Handoff::<usize>::new(); 
    let (_push, mut pop) = handoff.split();

    let pp = pop.pop();
    futures::pin_mut!(pp);
    // Pop future gets polled. No peer is available. It now knows to block.
    let _ = futures::poll!(pp);

    // As it gets dropped, it should unblock, checks should not fire.
}

pub async fn test_pop_cancel_after_success() {
    let mut handoff = Handoff::<usize>::new(); 
    let (mut push, mut pop) = handoff.split();

    let pp = pop.pop();
    futures::pin_mut!(pp);
    // Pop future gets polled. No peer is available. It now knows to block.
    let _ = futures::poll!(pp);

    // Push comes along and feeds it.
    push.push(42).await;

    // Now before getting polled, we cancel it.
    // As it gets dropped, it should unblock, checks should not fire.
}

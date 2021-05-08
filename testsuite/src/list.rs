use core::pin::Pin;
use core::cell::Cell;

use lilos::{create_list, create_node};
use lilos::list::{List, Node};

pub async fn test_node_basics() {
    create_node!(node, (), lilos::exec::noop_waker());
    // Node type is what we expect?
    let node: Pin<&mut Node<()>> = node;
    
    assert!(node.is_detached());
    node.as_ref().detach();
    assert!(node.is_detached());

    // And, detached node drop
}

pub async fn test_list_basics() {
    create_list!(list);
    // List type is what we expect?
    let list: Pin<&mut List<()>> = list;

    // Make sure these don't, like, assert on an empty list or anything
    list.as_ref().wake_all();
    list.as_ref().wake_one();

    // And, detached list drop.
}

pub async fn test_insert_and_wait() {
    create_list!(list);
    create_node!(node, (), lilos::exec::noop_waker());

    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    futures::join! {
        async {
            // Check that we can insert...
            list.insert_and_wait(node.as_mut()).await;
            assert!(node.is_detached());
        },
        async {
            // Check that we discover the node and wake it.
            loop {
                if list.wake_one() { break; }
                lilos::exec::yield_cpu().await;
            }
        },
    };

    // Let's check my assertion about cancel behavior, shall we?
    let fut = list.insert_and_wait(node.as_mut());
    drop(fut); // never polled, never woken
    assert!(node.is_detached());

    // And just for funsies
    {
        let fut = list.insert_and_wait(node.as_mut());
        pin_utils::pin_mut!(fut);
        let _ = futures::poll!(fut); // polled exactly once but not woken
    }
    assert!(node.is_detached()); // still works?
}

pub async fn test_insert_and_wait_with_cleanup() {
    create_list!(list);
    create_node!(node, (), lilos::exec::noop_waker());

    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    let cleanup_called = Cell::new(false);
    let fut = list.insert_and_wait_with_cleanup(
        node.as_mut(),
        || cleanup_called.set(true),
    );
    assert!(!cleanup_called.get());
    drop(fut);
    // Should not be called if the node was detached at drop.
    assert!(!cleanup_called.get());

    // Try again, this time with detachin'
    let fut = list.insert_and_wait_with_cleanup(
        node.as_mut(),
        || cleanup_called.set(true),
    );
    assert!(list.wake_one());
    assert!(!cleanup_called.get()); // not yet
    drop(fut); // never polled
    assert!(cleanup_called.get()); // now
}

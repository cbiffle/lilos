//! Tests for the `List` and `Node` types.

#![allow(clippy::bool_assert_comparison)]

use core::pin::{Pin, pin};
use core::cell::Cell;

use lilos::{create_list, create_node};
use lilos::list::{List, Node};

pub async fn test_node_basics() {
    create_node!(node, (), lilos::exec::noop_waker());
    // Node type is what we expect?
    let node: Pin<&mut Node<()>> = node;
    
    assert!(node.is_detached(), "node must begin as detached");

    // Detach must be safe to call on an already-detached node (idempotent).
    node.as_ref().detach();

    assert!(node.is_detached(), "node must remain detached if not inserted");

    // And, detached node drop -- mostly just checks to see if it inadvertently
    // panics!
}

pub async fn test_list_basics() {
    create_list!(list);
    // List type is what we expect?
    let list: Pin<&mut List<()>> = list;

    // Make sure these don't, like, assert on an empty list or anything
    list.as_ref().wake_all();
    assert_eq!(list.as_ref().wake_one(), false,
        "wake_one on an empty list must return false");

    // And, detached list drop.
}

pub async fn test_insert_and_wait_not_eager() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());

    // Insertion must not happen eagerly, it must wait for the insert future to
    // be pinned and polled.
    {
        let _fut = list.insert_and_wait(node.as_mut());
        // Should not be able to wake it!
        assert_eq!(list.wake_one(), false);
    }

    assert_eq!(node.is_detached(), true);
}

pub async fn test_insert_and_wait_wake_one() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());

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
}

pub async fn test_insert_and_wait_cancel_behavior() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());

    // Let's check my assertion about cancel behavior, shall we?
    let fut = list.insert_and_wait(node.as_mut());
    drop(fut); // never polled, never woken
    assert!(node.is_detached());

    // And just for funsies
    {
        let fut = pin!(list.insert_and_wait(node.as_mut()));
        let _ = futures::poll!(fut); // polled exactly once but not woken
    }
    assert!(node.is_detached()); // still works?
}

pub async fn test_iawwc_no_fire_if_never_polled() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());
    let cleanup_called = Cell::new(false);

    let fut = list.insert_and_wait_with_cleanup(
        node.as_mut(),
        || cleanup_called.set(true),
    );
    assert!(!cleanup_called.get());
    drop(fut);
    // Should not be called if the node was detached at drop.
    assert!(!cleanup_called.get());
}

pub async fn test_iawwc_no_fire_if_polled_after_detach() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());
    let cleanup_called = Cell::new(false);

    {
        let mut fut = pin!(list.insert_and_wait_with_cleanup(
            node.as_mut(),
            || cleanup_called.set(true),
        ));
        assert!(!cleanup_called.get());
        // Poll so that the node attaches itself.
        let _ = futures::poll!(fut.as_mut());
        // Cause the node to become detached...
        assert!(list.wake_one());
        // ...and make it aware of this.
        let _ = futures::poll!(fut);
        // dropped
    }
    // Should not be called if the node was polled after detach.
    assert!(!cleanup_called.get());
}

pub async fn test_iawwc_fire() {
    create_list!(list);
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    create_node!(node, (), lilos::exec::noop_waker());
    let cleanup_called = Cell::new(false);

    // Testing the cleanup behavior is slightly subtle: we need to activate the
    // logic for the case where...
    // - The node has successfully been inserted
    // - And then detached
    // - But hasn't been polled to discover this.
    //
    // Once the node has been pinned it becomes hard to drop explicitly, but we
    // can do it with a scope:
    {
        let mut fut = pin!(list.insert_and_wait_with_cleanup(
                node.as_mut(),
                || cleanup_called.set(true),
                ));
        // Poll the insert future to cause the node to link up.
        let _ = futures::poll!(fut.as_mut());
        assert_eq!(cleanup_called.get(), false); // not yet
                                                 // Detach it from the list.
        assert!(list.wake_one());
        assert_eq!(cleanup_called.get(), false); // not yet

        // dropped without poll
    }
    assert_eq!(cleanup_called.get(), true); // now
}

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Tests for the `List` and `Node` types.

#![allow(clippy::bool_assert_comparison)]

use core::pin::{Pin, pin};
use core::cell::Cell;

use lilos_list::List;

use crate::{poll_and_assert_not_ready, poll_and_assert_ready};

pub async fn test_list_basics() {
    let list: Pin<&mut List<()>> = pin!(List::new());

    // Make sure these don't, like, assert on an empty list or anything
    list.as_ref().wake_while(|_| true);
    assert_eq!(list.as_ref().wake_head_if(|_| true), false,
        "wake_one on an empty list must return false");

    // And, detached list drop.
}

pub async fn test_insert_and_wait_not_eager() {
    let list = pin!(List::new());
    let list = list.into_ref();

    // Insertion must not happen eagerly, it must wait for the insert future to
    // be pinned and polled.
    {
        let _fut = list.join(());
        // Should not be able to wake it!
        assert_eq!(list.wake_one(), false);
    }
}

pub async fn test_insert_and_wait_wake_one() {
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();


    // Check that we can insert a node, A:
    let mut fut_a = pin!(list.join(()));
    poll_and_assert_not_ready!(fut_a);

    // Also insert a second node, B:
    let mut fut_b = pin!(list.join(()));

    // We should be able to wake a node.
    assert!(list.wake_one());

    // That node must be node A, not B
    poll_and_assert_ready!(fut_a);
    poll_and_assert_not_ready!(fut_b);
}

pub async fn test_wake_while_insert_order() {
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    // Insert a series of nodes:
    let mut fut_a = pin!(list.join(()));
    poll_and_assert_not_ready!(fut_a);

    let mut fut_b = pin!(list.join(()));
    poll_and_assert_not_ready!(fut_b);

    let mut fut_c = pin!(list.join(()));
    poll_and_assert_not_ready!(fut_c);

    let mut fut_d = pin!(list.join(()));
    poll_and_assert_not_ready!(fut_d);

    // (Ab)use wake_while to only wake up two of them.
    let mut check_count = 0;
    let changes = list.wake_while(|_n| {
        check_count += 1;
        check_count <= 2
    });
    assert!(changes);
    assert_eq!(check_count, 3);

    // We must have woken nodes A and B:
    poll_and_assert_ready!(fut_a);
    poll_and_assert_ready!(fut_b);
    // ...and not nodes C and D:
    poll_and_assert_not_ready!(fut_c);
    poll_and_assert_not_ready!(fut_d);
}

pub async fn test_insert_and_wait_cancel_behavior() {
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    // Let's check my assertion about cancel behavior, shall we?
    let fut = list.join(());
    drop(fut); // never polled, never woken

    // And just for funsies
    {
        let fut = pin!(list.join(()));
        let _ = futures::poll!(fut); // polled exactly once but not woken
    }
}

pub async fn test_iawwc_no_fire_if_never_polled() {
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    let cleanup_called = Cell::new(false);

    let fut = list.join_with_cleanup(
        (),
        || cleanup_called.set(true),
    );
    assert!(!cleanup_called.get());
    drop(fut);
    // Should not be called if the node was detached at drop.
    assert!(!cleanup_called.get());
}

pub async fn test_iawwc_no_fire_if_polled_after_detach() {
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

    let cleanup_called = Cell::new(false);

    {
        let mut fut = pin!(list.join_with_cleanup(
            (),
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
    let list = pin!(List::new());
    // Drop list mutability. TODO: should create_list even return a Pin<&mut>?
    let list = list.into_ref();

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
        let mut fut = pin!(list.join_with_cleanup(
                (),
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

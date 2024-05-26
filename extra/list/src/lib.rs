// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A no-allocation wait-list and associated utility code.
//!
//! This crates provides a doubly-linked intrusive list for tracking timers or
//! wait queues without using dynamic memory allocation. To achieve a safe Rust
//! API, the interface is a bit unusual.
//!
//! See the [`List`] type for details.
//!
//! This list is used internally by [`lilos`] but may also be useful for
//! applications or crates implementing new synchronization primitives. Because
//! `lilos`'s internal use of this list is not exposed, it's not important to
//! use exactly the same version, except to conserve flash space.
//!
//! [`lilos`]: https://docs.rs/lilos/latest/lilos/

// IMPLEMENTATION NOTE: for shorthand and to avoid repeating ourselves, the
// safety comments below refer to something called the Link Valid Invariant.
// This invariant is:
//
// Once a List has been pinned, all nodes reachable from it -- its direct head
// and tail pointers, plus nodes connected to the next/prev pointers of other
// nodes reachable transitively -- must also be pinned and valid.
//
// In addition, a node's list pointer must also be valid or set to `None`.
//
// The operations below are careful to maintain this so that the pointer
// dereferencing is sound.

#![cfg_attr(not(test), no_std)]
#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    missing_debug_implementations,
    missing_docs,
    semicolon_in_expressions_from_macros,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_qualifications
)]
#![warn(clippy::undocumented_unsafe_blocks)]

use core::future::Future;
use core::{
    cell::Cell,
    marker::PhantomPinned,
    pin::Pin,
    ptr::NonNull,
    task::{Poll, Waker},
};

use pin_project::{pin_project, pinned_drop};

/// A list that records concurrent processes waiting for events of some sort.
///
/// This is a very specialized doubly-linked list, designed to implement timer
/// lists and wait queues without dynamic memory allocation, while also passing
/// soundness checks.
///
/// The list only supports the following operations:
///
/// - [`join`][List::join], which produces a `Future` that will register a new
///   node on the list and resolve when it has been triggered by `wake_*`.
///
/// - [`wake_head_if`][List::wake_head_if], which looks at the head node of the
///   list and triggers its owning `Future` if it passes a predicate,
///
/// - And a handful of other wake-related operations that can be expressed in
///   terms of `wake_head_if`: [`wake_while`][List::wake_while],
///   [`wake_all`][List::wake_all], [`wake_one`][List::wake_one].
///
/// In particular, there is no way for the owner of the list to get direct
/// access to any of the nodes in the list -- only act upon them by waking them.
/// The wake operation _does not_ return a reference to the node that is woken.
///
/// This property is critical to ensuring the soundness of an otherwise tricky
/// data structure in Rust.
///
///
/// # The contents type `T`
///
/// Each node in the list has associated with it a value of type `T`. `T` must
/// implement `PartialOrd`, because nodes are kept sorted according to the order
/// defined by `T`'s `PartialOrd` impl, from the smallest at the head to the
/// largest at the tail.
///
/// Using a timestamp type allows the list to act as a timer queue, efficiently
/// waking all nodes waiting for a certain time or lower.
///
/// By using `()` for `T`, you can turn the list into one that simply keeps
/// track of insertion order. This is useful for wait queues for things like
/// mutexes.
///
/// In some niche cases, it can be useful to associate additional information
/// with a node, without having it considered for sorting purposes. You can do
/// this by using a type that contains information but _does not_ use that
/// information in its `PartialOrd` implementation. See [`Meta`] for a utility
/// type that wraps some data and stops it from being sorted, or
/// [`OrderAndMeta`] for a type that lets you have some data used for
/// sorting, and some data simply stored.
///
///
/// # Operation complexity
///
/// This is a doubly-linked list and its operations scale as you'd expect for
/// that data structure:
///
/// - Inserting in a sorted list takes time linear in the size of the list
///   (`O(n)`).
///
/// - Inserting in an unsorted list takes constant time (`O(1)`).
///
/// - Waking the head node takes constant time (`O(1)`).
///
/// - Waking a series of nodes takes time linear in the length of that sequence
///   (`O(m)`).
///
/// - Detaching an arbitrary node (by dropping its owning `Future`) takes
///   constant time (`O(1)`).
#[derive(Default)]
pub struct List<T> {
    /// Links to the head and tail of the list, if the list is non-empty, or
    /// `None` if it's empty.
    root: Cell<Option<Root<T>>>,
    _marker: PhantomPinned,
}

impl<T> List<T> {
    /// Creates a new empty `List`.
    ///
    /// The `List` needs to be pinned before use, so this call often appears as
    /// `pin!(List::new())`.
    pub const fn new() -> Self {
        Self {
            root: Cell::new(None),
            _marker: PhantomPinned,
        }
    }

    /// Checks if the list is empty (i.e. contains zero nodes).
    pub fn is_empty(&self) -> bool {
        self.root.get().is_none()
    }

    /// Starting at the head, wakes nodes with contents that that satisfy `pred`
    /// (that is, where `pred(n.contents)` returns `true`) until it finds one
    /// that doesn't.
    ///
    /// Returns `true` if any nodes were awoken, `false` if none were (either
    /// because the list is empty, or because the first node failed the
    /// predicate).
    pub fn wake_while(
        self: Pin<&Self>,
        mut pred: impl FnMut(&T) -> bool,
    ) -> bool {
        let mut any = false;
        loop {
            if !self.wake_head_if(&mut pred) {
                break;
            }
            any = true;
        }
        any
    }

    /// Wakes all nodes in the list in order from head to tail.
    ///
    /// Returns `true` if any nodes were awoken, `false` if the list was empty.
    pub fn wake_all(self: Pin<&Self>) -> bool {
        self.wake_while(|_| true)
    }

    /// Wakes the head of the list, but only if it satisfies `pred` (that is, if
    /// `pred(head.contents)` returns `true`).
    ///
    /// Returns `true` if there was a head node and it passed, `false` if it
    /// didn't pass or didn't exist.
    pub fn wake_head_if(
        self: Pin<&Self>,
        pred: impl FnOnce(&T) -> bool,
    ) -> bool {
        let Some(root) = self.root.get() else {
            return false;
        };

        let node_ptr = root.head;
        // Safety: dereferencing and pinning the head pointer is safe per the
        // Link Valid Invariant.
        let node = unsafe { Pin::new_unchecked(&*node_ptr.as_ptr()) };

        debug_assert_eq!(node.list.get(), Some(NonNull::from(&*self)));

        // This node is the head, it should not have a previous node.
        debug_assert!(node.prev.get().is_none());

        if !pred(&node.contents) {
            return false;
        }

        if node_ptr == root.tail {
            // This node is the _only_ node in the list.
            debug_assert_eq!(node.next.get(), None,
                "list thinks node @{node_ptr:?} is tail, \
                 node thinks it has a next");
            self.root.set(None);
        } else {
            // Unlink this node from its neighbor.
            let Some(next_ptr) = node.next.take() else {
                panic!()
            };
            // Safety: dereferencing and pinning the neighbor pointer is safe
            // per the Link Valid Invariant.
            let next = unsafe { Pin::new_unchecked(next_ptr.as_ref()) };
            next.prev.set(None);
            self.root.set(Some(Root {
                head: next_ptr,
                ..root
            }));
        }

        node.list.take();
        if let Some(waker) = node.waker.take() {
            waker.wake();
        } else {
            panic!();
        }

        true
    }

    /// Wakes the head of the list unconditionally.
    ///
    /// Returns `true` if the list was non-empty, `false` if it was empty.
    pub fn wake_one(self: Pin<&Self>) -> bool {
        self.wake_head_if(|_| true)
    }

    /// Returns a future that will create a node containing `contents` and
    /// insert it into this list at the appropriate position, and then resolve
    /// only when the node is awoken by a `wake` operation.
    ///
    /// This waiter will appear in the list _after_ all nodes `n` where
    /// `n.contents <= contents`. If `T` is effectively unordered (such as `()`)
    /// this means the waiter just gets tacked onto the end of the list.
    ///
    /// This operation does nothing until the future is polled. This is
    /// important: we need proof that the returned future has been pinned before
    /// it's safe to link it into the list, and polling the future provides that
    /// proof.
    ///
    /// `contents` is consumed by this operation, because it's generally `Copy`
    /// like a timestamp or a `()`.
    ///
    /// # Cancellation
    ///
    /// Dropping the future before it resolves loses its place in line. If there
    /// are other nodes that are equal to `contents`, dropping and recreating
    /// the future will move this waiter after those other nodes.
    pub fn join(
        self: Pin<&Self>,
        contents: T,
    ) -> impl Future<Output = ()> + Captures<&'_ Self>
    where
        T: PartialOrd,
    {
        WaitForDetach {
            list: Some(self),
            node: Node {
                prev: Cell::new(None),
                next: Cell::new(None),
                waker: Cell::new(None),
                list: Cell::new(None),
                contents,
                _marker: PhantomPinned,
            },
        }
    }

    /// Returns a future that does the same thing as [`List::join`], but with
    /// additional behavior if it's dropped in a specific time window.
    ///
    /// Specifically: if the future has inserted its node into the list, then
    /// been awoken, and then gets dropped before being polled again. In that
    /// very narrow circumstance, the future will execute `cleanup` on its way
    /// toward oblivion.
    ///
    /// This is important for synchronization primitives like mutexes, where
    /// ownership gets passed to the next waiter in the queue without
    /// unlocking/relocking (since that could allow races). The cleanup action
    /// gives a waiter on such a queue an opportunity to wake the _next_ node on
    /// the list.
    ///
    /// # Cancellation
    ///
    /// Dropping the future before it resolves loses its place in line. If there
    /// are other nodes that are equal to `contents`, dropping and recreating
    /// the future will move this waiter after those other nodes.
    ///
    /// In addition, dropping the future _after it has been triggered by a wake
    /// operation_ (but before it's been polled to observe that)
    pub fn join_with_cleanup(
        self: Pin<&Self>,
        contents: T,
        cleanup: impl FnOnce(),
    ) -> impl Future<Output = ()> + Captures<Pin<&'_ Self>>
    where
        T: PartialOrd,
    {
        let inner = WaitForDetach {
            list: Some(self),
            node: Node {
                prev: Cell::new(None),
                next: Cell::new(None),
                waker: Cell::new(None),
                list: Cell::new(None),
                contents,
                _marker: PhantomPinned,
            },
        };
        WaitWithCleanup {
            inner,
            cleanup: Some(cleanup),
        }
    }
}

/// Internal future produced by the `join` operation.
#[pin_project]
struct WaitForDetach<'list, T> {
    /// A pointer to the list we're attempting to attach to. Initialized to
    /// `Some` on creation, then changed to `None` when we attach successfully.
    list: Option<Pin<&'list List<T>>>,
    /// The actual node.
    #[pin]
    node: Node<T>,
}

impl<T: PartialOrd> Future for WaitForDetach<'_, T> {
    type Output = ();

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let p = self.project();
        let node = p.node.into_ref();
        let node_ptr = NonNull::from(&*node);

        if let Some(list) = p.list.take() {
            // We haven't yet attached to a list. We need to complete attachment
            // now because we've taken the list field.
            if let Some(mut root) = list.root.get() {
                // The list is not empty.
                //
                // Traverse from the tail to the head looking for the
                // right insertion position.
                let mut maybe_cand = Some(root.tail);
                while let Some(cand_ptr) = maybe_cand {
                    // Safety: dereferencing and pinning the node pointer is
                    // safe per the Link Valid Invariant.
                    let candidate =
                        unsafe { Pin::new_unchecked(cand_ptr.as_ref()) };

                    if candidate.contents <= node.contents {
                        // This is the right place for it. `candidate` will
                        // become `node`'s new `prev`.
                        let old_next = candidate.next.replace(Some(node_ptr));
                        if let Some(next_ptr) = old_next {
                            // Safety: dereferencing and pinning the node
                            // pointer is safe per the Link Valid Invariant.
                            let next = unsafe {
                                Pin::new_unchecked(next_ptr.as_ref())
                            };
                            next.prev.set(Some(node_ptr));
                        }
                        node.next.set(old_next);
                        node.prev.set(Some(cand_ptr));
                        if cand_ptr == root.tail {
                            root.tail = node_ptr;
                            list.root.set(Some(root));
                        }
                        break;
                    }

                    maybe_cand = candidate.prev.get();
                }

                if maybe_cand.is_none() {
                    // node is becoming the new head of the list!
                    // Safety: dereferencing and pinning the head pointer is
                    // safe per the Link Valid Invariant.
                    let old_head =
                        unsafe { Pin::new_unchecked(root.head.as_ref()) };
                    old_head.prev.set(Some(node_ptr));
                    node.next.set(Some(root.head));
                    root.head = node_ptr;
                    list.root.set(Some(root));
                }
            } else {
                // The list is currently empty. This node will become the only
                // node in the list.
                list.root.set(Some(Root {
                    head: node_ptr,
                    tail: node_ptr,
                }));
            }

            // Update the node to reflect that it's in a list now.
            node.list.set(Some(NonNull::from(&*list)));
            node.waker.set(Some(cx.waker().clone()));

            Poll::Pending
        } else {
            // We've already attached
            // See if we've detached.
            if node.list.get().is_none() {
                // The node is not attached to any list, so we can resolve. Note
                // that this means the future is "fused" -- it will keep
                // returning ready if repeatedly polled.
                Poll::Ready(())
            } else {
                // The node remains attached to the list. While unlikely,
                // it's possible that the waker has changed. Update it.
                node.waker.set(Some(cx.waker().clone()));
                Poll::Pending
            }
        }
    }
}

/// Internal future returned by `join_with_cleanup`.
#[pin_project(PinnedDrop)]
struct WaitWithCleanup<'list, T, F: FnOnce()> {
    #[pin]
    inner: WaitForDetach<'list, T>,
    cleanup: Option<F>,
}

#[pinned_drop]
impl<T, F: FnOnce()> PinnedDrop for WaitWithCleanup<'_, T, F> {
    fn drop(self: Pin<&mut Self>) {
        let p = self.project();
        let pi = p.inner.project();
        let node = pi.node.into_ref();

        if pi.list.is_none() && node.list.get().is_none() {
            // Process cleanup if it hasn't already been done.
            if let Some(cleanup) = p.cleanup.take() {
                cleanup();
            }
        }
    }
}

impl<T: PartialOrd, F: FnOnce()> Future for WaitWithCleanup<'_, T, F> {
    type Output = ();

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let p = self.project();
        if p.inner.poll(cx).is_ready() {
            // The inner future has resolved -- we no longer need the cleanup
            // action to hang around.
            p.cleanup.take();
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

impl<T> core::fmt::Debug for List<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("List").field("root", &self.root).finish()
    }
}

#[cfg(debug_assertions)]
impl<T> Drop for List<T> {
    fn drop(&mut self) {
        debug_assert!(self.root.get().is_none());
    }
}

struct Root<T> {
    head: NonNull<Node<T>>,
    tail: NonNull<Node<T>>,
}

impl<T> Copy for Root<T> {}
impl<T> Clone for Root<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> core::fmt::Debug for Root<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Root")
            .field("head", &self.head)
            .field("tail", &self.tail)
            .finish()
    }
}

struct Node<T> {
    /// Previous node in the list, or `None` if this is the head.
    ///
    /// This field may be changed by neighboring nodes, and thus through a
    /// shared reference, so it's in a `Cell`.
    prev: Cell<Option<NonNull<Self>>>,
    /// Next node in the list, or `None` if this is the tail.
    ///
    /// This field may be changed by neighboring nodes, and thus through a
    /// shared reference, so it's in a `Cell`.
    next: Cell<Option<NonNull<Self>>>,
    /// Waker that should be poked if this node is detached from a list. This
    /// does double-duty as the "attached" flag.
    ///
    /// The waker gets triggered by the list, rather than the node's owner, when
    /// the node leaves the list. This means we act on it through a shared
    /// reference. Because Waker is not Copy, and because Clone requires a
    /// second virtual dispatch, this is in an `Option<Cell<>>` so we can `take`
    /// it even through a shared reference.
    waker: Cell<Option<Waker>>,
    /// Data borne by the node to assist in ordering of newly inserted nodes. To
    /// associate data that does not participate in ordering, use a type with a
    /// partialeq impl that ignores part of its contents.
    contents: T,
    /// Pointer to the list this node is associated with.
    ///
    /// This field is filled in when the node joins a list, so it can be used as
    /// an "attached" indicator: `Some` if attached, `None` if not.
    list: Cell<Option<NonNull<List<T>>>>,

    _marker: PhantomPinned,
}

impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        if let Some(list_ptr) = self.list.take() {
            // We are still attached to the list. Detach.
            // Safety: dereferencing and pinning our pointer to the list is safe
            // per the Link Valid Invariant.
            let list = unsafe { Pin::new_unchecked(list_ptr.as_ref()) };
            // Patch up previous node, if any.
            if let Some(prev_ptr) = self.prev.get() {
                // Safety: dereferencing and pinning our pointer to our neighbor
                // is safe per the Link Valid Invariant.
                let prev = unsafe { Pin::new_unchecked(prev_ptr.as_ref()) };
                prev.next.set(self.next.get());
            }
            // Patch up next self, if any.
            if let Some(next_ptr) = self.next.get() {
                // Safety: dereferencing and pinning our pointer to our neighbor
                // is safe per the Link Valid Invariant.
                let next = unsafe { Pin::new_unchecked(next_ptr.as_ref()) };
                next.prev.set(self.prev.get());
            }

            match (self.prev.get(), self.next.get()) {
                (None, None) => {
                    // This was the only node in the list.
                    list.root.set(None);
                }
                (Some(prev_ptr), None) => {
                    // This was the tail of the list.
                    list.root.set(Some(Root {
                        tail: prev_ptr,
                        ..list.root.get().unwrap()
                    }));
                }
                (None, Some(next_ptr)) => {
                    // This was the head of the list.
                    list.root.set(Some(Root {
                        head: next_ptr,
                        ..list.root.get().unwrap()
                    }));
                }
                (Some(_), Some(_)) => {
                    // boring middle of list
                }
            }
        }
        debug_assert_eq!(self.list.get(), None);
    }
}

/// Combines an ordering type `T` with an arbitrary metadata type `M` for use in
/// a [`List`].
///
/// A [`List`] keeps its contents ordered by a type, which must implement
/// `PartialOrd`. That's all well and good, but sometimes you need to store
/// additional metadata in the list node that should not affect ordering -- such
/// as requested access level in a read-write lock, for instance.
///
/// `OrderAndMeta` combines some piece of data `T` that implements `PartialOrd`,
/// with another piece of data `M` that is ignored for comparisons, so that you
/// can have a list that stays sorted but also carries arbitrary additional
/// data.
///
/// If you don't care about the sorting part, have a look at [`Meta`] instead.
#[derive(Copy, Clone, Debug)]
pub struct OrderAndMeta<T, M>(pub T, pub M);

impl<T: PartialEq, M> PartialEq for OrderAndMeta<T, M> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: PartialOrd, M> PartialOrd for OrderAndMeta<T, M> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

/// A wrapper type for including some arbitrary metadata `M` in a [`List`].
///
/// A [`List`] keeps its contents ordered by a type, which must implement
/// `PartialOrd`. Many lists don't need special sorting, and just want to record
/// the order of insertion of the nodes. In those cases, it's common to use
/// `List<()>` to disable the sorting.
///
/// But what if you want the insertion-only-ordering of `()` but also need to
/// include some data in each list node? `Meta` wraps the data of your choice
/// and _blocks access to its `PartialOrd` impl,_ if it even has one to begin
/// with. That is, all `Meta<M>`s look the same to the list, even if the `M`
/// they contain are different.
///
/// If you'd like to store metadata that isn't used for sorting, but _do_ want
/// to sort the list by some other data, see [`OrderAndMeta`].
#[derive(Copy, Clone, Debug)]
pub struct Meta<M>(pub M);

impl<M> PartialEq for Meta<M> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<M> PartialOrd for Meta<M> {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
        Some(core::cmp::Ordering::Equal)
    }
}

/// Marker trait implementing the "Captures Trick" from Rust RFC 3498, ensuring
/// that we do lifetime capturing right in the 2021 edition.
///
/// TODO: revisit this when we can switch to the 2024 edition, where the default
/// behavior makes this less necessary.
pub trait Captures<T> {}

impl<U: ?Sized, T> Captures<T> for U {}

#[cfg(test)]
mod tests {
    #![allow(clippy::bool_assert_comparison)]
    #![allow(clippy::undocumented_unsafe_blocks)]

    use core::{
        cell::Cell,
        future::Future,
        mem::forget,
        pin::pin,
        sync::atomic::{AtomicUsize, Ordering},
        task::{Context, RawWaker, RawWakerVTable, Waker},
    };
    use std::sync::Arc;

    use crate::List;

    /// VTable for the spy waker.
    static VTABLE: RawWakerVTable = RawWakerVTable::new(
        // clone
        |p| {
            let arc = unsafe { Arc::from_raw(p as *const AtomicUsize) };
            let second_arc = Arc::clone(&arc);
            forget(arc);
            RawWaker::new(Arc::into_raw(second_arc) as *const (), &VTABLE)
        },
        // wake
        |p| {
            let arc = unsafe { Arc::from_raw(p as *const AtomicUsize) };
            arc.fetch_add(1, Ordering::Relaxed);
            // drop it to release our count.
        },
        // wake_by_ref
        |p| {
            let arc = unsafe { Arc::from_raw(p as *const AtomicUsize) };
            arc.fetch_add(1, Ordering::Relaxed);
            forget(arc);
        },
        // drop
        |p| {
            let _arc = unsafe { Arc::from_raw(p as *const AtomicUsize) };
        },
    );

    /// Produces a `Waker` and also a shared `AtomicUsize` that counts how many
    /// times the waker is actually used.
    fn spy_waker() -> (Arc<AtomicUsize>, Waker) {
        let count = Arc::new(AtomicUsize::new(0));
        let second_count = Arc::clone(&count);
        (count, unsafe {
            Waker::from_raw(RawWaker::new(
                Arc::into_raw(second_count) as *const (),
                &VTABLE,
            ))
        })
    }

    #[test]
    fn test_create_drop() {
        // It'd be real bad if this didn't work, eh?
        List::<()>::new();
    }

    #[test]
    fn test_single_node_wait_resume() {
        let list = pin!(List::<()>::new());
        let list = list.as_ref();

        let (wake_count, waker) = spy_waker();
        let mut ctx = Context::from_waker(&waker);

        let mut wait_fut = pin!(list.join(()));

        assert!(list.is_empty());

        assert!(wait_fut.as_mut().poll(&mut ctx).is_pending());
        assert_eq!(wake_count.load(Ordering::Relaxed), 0);

        assert!(!list.is_empty());

        assert!(wait_fut.as_mut().poll(&mut ctx).is_pending());
        assert!(wait_fut.as_mut().poll(&mut ctx).is_pending());

        assert!(list.wake_head_if(|_| true));
        assert_eq!(wake_count.load(Ordering::Relaxed), 1);
        assert!(list.is_empty());

        assert!(wait_fut.poll(&mut ctx).is_ready());
        assert_eq!(wake_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_single_node_drop_while_in_list() {
        let list = pin!(List::<()>::new());
        let list = list.as_ref();

        let (wake_count, waker) = spy_waker();
        let mut ctx = Context::from_waker(&waker);

        {
            let mut wait_fut = pin!(list.join(()));
            assert!(wait_fut.as_mut().poll(&mut ctx).is_pending());
            assert!(!list.is_empty());
        }
        assert!(list.is_empty());
        assert_eq!(wake_count.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_wake_while_insert_order() {
        let list = pin!(List::new());
        let list = list.into_ref();

        let (wake_count, waker) = spy_waker();
        let mut ctx = Context::from_waker(&waker);

        // Insert a series of nodes:
        let mut fut_a = pin!(list.join(()));
        assert!(fut_a.as_mut().poll(&mut ctx).is_pending());

        let mut fut_b = pin!(list.join(()));
        assert!(fut_b.as_mut().poll(&mut ctx).is_pending());

        let mut fut_c = pin!(list.join(()));
        assert!(fut_c.as_mut().poll(&mut ctx).is_pending());

        let mut fut_d = pin!(list.join(()));
        assert!(fut_d.as_mut().poll(&mut ctx).is_pending());

        // (Ab)use wake_while to only wake up two of them.
        let mut check_count = 0;
        let changes = list.wake_while(|_n| {
            check_count += 1;
            check_count <= 2
        });
        assert!(changes);
        assert_eq!(check_count, 3);
        assert_eq!(wake_count.load(Ordering::Relaxed), 2);

        // We must have woken nodes A and B:
        assert!(fut_a.as_mut().poll(&mut ctx).is_ready());
        assert!(fut_b.as_mut().poll(&mut ctx).is_ready());
        // ...and not nodes C and D:
        assert!(fut_c.as_mut().poll(&mut ctx).is_pending());
        assert!(fut_d.as_mut().poll(&mut ctx).is_pending());
    }

    #[test]
    fn test_insert_and_wait_cancel_behavior() {
        let list = pin!(List::new());
        let list = list.into_ref();

        // Let's check my assertion about cancel behavior, shall we?
        let fut = list.join(());
        drop(fut); // never polled, never woken

        // And just for funsies
        {
            let (_, waker) = spy_waker();
            let mut ctx = Context::from_waker(&waker);
            let fut = pin!(list.join(()));
            let _ = fut.poll(&mut ctx); // polled exactly once but not woken
        }
    }

    #[test]
    fn test_iawwc_no_fire_if_never_polled() {
        let list = pin!(List::new());
        let list = list.into_ref();

        let cleanup_called = Cell::new(false);

        let fut = list.join_with_cleanup((), || cleanup_called.set(true));
        assert!(!cleanup_called.get());
        drop(fut);
        // Should not be called if the node was detached at drop.
        assert!(!cleanup_called.get());
    }

    #[test]
    fn test_iawwc_no_fire_if_polled_after_detach() {
        let list = pin!(List::new());
        let list = list.into_ref();

        let (_, waker) = spy_waker();
        let mut ctx = Context::from_waker(&waker);

        let cleanup_called = Cell::new(false);

        {
            let mut fut =
                pin!(list.join_with_cleanup((), || cleanup_called.set(true),));
            assert!(!cleanup_called.get());
            // Poll so that the node attaches itself.
            let _ = fut.as_mut().poll(&mut ctx);
            // Cause the node to become detached...
            assert!(list.wake_one());
            // ...and make it aware of this.
            let _ = fut.poll(&mut ctx);
            // dropped
        }
        // Should not be called if the node was polled after detach.
        assert!(!cleanup_called.get());
    }

    #[test]
    fn test_iawwc_fire() {
        let list = pin!(List::new());
        let list = list.into_ref();

        let (_, waker) = spy_waker();
        let mut ctx = Context::from_waker(&waker);

        let cleanup_called = Cell::new(false);

        // Testing the cleanup behavior is slightly subtle: we need to activate
        // the logic for the case where...
        // - The node has successfully been inserted
        // - And then detached
        // - But hasn't been polled to discover this.
        //
        // Once the node has been pinned it becomes hard to drop explicitly, but
        // we can do it with a scope:
        {
            let mut fut =
                pin!(list.join_with_cleanup((), || cleanup_called.set(true),));

            // Poll the insert future to cause the node to link up.
            let _ = fut.as_mut().poll(&mut ctx);
            assert_eq!(cleanup_called.get(), false); // not yet

            // Detach it from the list.
            assert!(list.wake_one());

            assert_eq!(cleanup_called.get(), false); // not yet

            // dropped without poll
        }
        assert_eq!(cleanup_called.get(), true); // now
    }
}

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A queue for moving data from one future/task into another.
//!
//! This is a "single-producer, single-consumer" queue that splits into separate
//! `Pusher` and `Popper` endpoints -- at any given time, there is at most one of
//! each alive in your program, ensuring that pushes and pops are not coming
//! from multiple directions.
//!
//! You create a queue by calling `Queue::new` and passing it a reference to its
//! backing storage. To actually use the queue, however, you must call
//! `Queue::split` to break it into two endpoints, `Pusher` and `Popper`. As
//! their names suggest, `Pusher` can be used to push things into the queue, and
//! `Popper` can be used to pop things out of it.
//!
//! The `Pusher` and `Popper` can then be handed off to separate code paths, so
//! long as they don't outlive the `Queue` and its storage. (The compiler will
//! ensure this.)
//!
//! This queue uses the Rust type system to ensure that only one code path is
//! attempting to push or pop the queue at any given time, because both `Pusher`
//! and `Popper` endpoints borrow the central `Queue`, and an `async` operation
//! to push or pop through an endpoint borrows that endpoint in turn. Neither
//! `Pusher` nor `Popper` can be cloned or copied, ensuring the single-producer
//! single-consumer property.
//!
//! # Implementation
//!
//! This is implemented as a concurrent lock-free Lamport queue. This has two
//! implications:
//! 
//! 1. If you can arrange the lifetimes correctly (i.e. make the queue static)
//!    it is actually safe to operate either Pusher or Popper from an ISR.
//! 2. It fills up at N-1 elements because one empty slot is used as a sentinel
//!    to distinguish full from empty.
//!
//! The adaptations to modern memory ordering semantics are taken from Nhat Minh
//! Lê et al's paper "Correct and Efficient Bounded FIFO Queues," though this
//! implementation does not use _all_ of the optimizations they identified.

use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::exec::Notify;
use crate::util::NotSyncMarker;

/// A single-producer, single-consumer queue. The `Queue` struct contains the
/// controlling information for the queue overall, and _borrows_ the storage.
///
/// See the module docs for details.
#[derive(Debug)]
pub struct Queue<'s, T> {
    storage: &'s mut [UnsafeCell<MaybeUninit<T>>],

    /// Index of next slot in `storage` to write during `push`. Must fall in the
    /// range `0..N`. Read by both sides, written by pushers.
    head: AtomicUsize,
    /// Index of next slot in `storage` to read during `pop`. Must fall in the
    /// range `0..N`. Read by both sides, written by poppers.
    tail: AtomicUsize,

    /// Signals blocked pushers that an element has been popped.
    popped: Notify,
    /// Signals blocked poppers that an element has been pushed.
    pushed: Notify,
}

/// Safety: This type is easily sharable across threads, because there are no
/// useful operations that can be performed using only a shared reference.
unsafe impl<T> Sync for Queue<'_, T> where T: Send {}

impl<'s, T> Queue<'s, T> {
    /// Creates a queue, borrowing the uninitialized `storage` (which will be
    /// arbitrarily overwritten).
    pub fn new(storage: &'s mut [MaybeUninit<T>]) -> Self {
        let storage: *mut [MaybeUninit<T>] = storage;
        let storage: *mut [UnsafeCell<MaybeUninit<T>>] = storage as *mut _;
        // Safety: the cast we're about to do is memory-layout-compatible
        // because:
        // - MaybeUninit<T> has the same memory layout as T
        // - UnsafeCell<T> has the same memory layout as T
        // - Thus, UnsafeCell<MaybeUninit<T>> has the same memory layout
        //   as MaybeUninit<T>.
        //
        // We can do these shenanigans because we have exclusive access to the
        // memory backing `storage`, and the caller thinks of it as
        // `MaybeUninit`, meaning they aren't making assumptions about its
        // contents or dropping it when we're done.
        let storage: &'s mut [UnsafeCell<MaybeUninit<T>>] = unsafe {
            &mut *storage
        };
        Self {
            storage,
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
            pushed: Notify::new(),
            popped: Notify::new(),
        }
    }

    /// Creates a push and pop endpoint for this queue. Note that an exclusive
    /// borrow of the queue exists as long as either endpoint exists, ensuring
    /// that at most one of each endpoint exists at any point in the program.
    ///
    /// You can, however, drop the first pair of endpoints and make a new pair
    /// later -- that's fine.
    pub fn split(&mut self) -> (Pusher<'_, T>, Popper<'_, T>) {
        (
            Pusher { q: self, _marker: NotSyncMarker::default() },
            Popper { q: self, _marker: NotSyncMarker::default() },
        )
    }

    fn next_index(&self, i: usize) -> usize {
        // This produced better code than using remainder on ARMv7-M last
        // I checked.
        let ni = i.wrapping_add(1);
        if ni == self.storage.len() { 0 } else { ni }
    }

}

/// It's entirely possible to drop a non-empty Queue in correct code, unlike
/// (say) a `lilos::list`, so we provide a Drop impl that goes through and
/// cleans up queued elements.
impl<T> Drop for Queue<'_, T> {
    fn drop(&mut self) {
        let h = self.head.load(Ordering::SeqCst);
        let mut t = self.tail.load(Ordering::SeqCst);

        while h != t {
            let unsafecell_ptr = self.storage[t].get();
            // Safety: this is unsafe because we're accessing the UnsafeCell
            // contents. We can do this because since we're &mut Self we
            // have exclusive control over our storage.
            let maybeuninit = unsafe { &mut *unsafecell_ptr };
            // Safety: we're dropping the contents of a MaybeUninit, which
            // implies asserting that it's been initialized. We know it's been
            // initialized because of the `h != t` condition on our loop.
            unsafe {
                maybeuninit.assume_init_drop();
            }
            t = self.next_index(t);
        }
    }
}

/// Queue endpoint for pushing data. Access to a `Pusher` _only_ gives you the
/// right to push data and enquire about push-related properties.
///
/// See the module docs for more details.
#[derive(Debug)]
pub struct Pusher<'a, T> {
    q: &'a Queue<'a, T>,
    _marker: NotSyncMarker,
}

impl<'q, T> Pusher<'q, T> {
    // Implementation note: Pusher "owns" the head and does not need to be
    // careful with its memory ordering, while the tail is "foreign" and must be
    // synchronized.

    /// Checks if there is room to push at least one item. Because the `Pusher`
    /// endpoint has exclusive control over data movement into the queue, if
    /// this returns `true`, the condition will remain true until a `push` or
    /// `try_push` happens through `self`, or `self` is dropped.
    ///
    /// If this returns `false`, of course, room may appear at any time if the
    /// other end of the queue is popped.
    pub fn can_push(&self) -> bool {
        let h = self.q.head.load(Ordering::Relaxed);
        let t = self.q.tail.load(Ordering::Acquire);

        self.q.next_index(h) != t
    }

    /// Checks if there is room to push at least one item, and if so, returns an
    /// `Entry` that entitles its holder to that queue slot.
    ///
    /// If the queue is full, returns `None`.
    pub fn try_reserve(&mut self) -> Option<Entry<'q, T>> {
        let h = self.q.head.load(Ordering::Relaxed);
        let t = self.q.tail.load(Ordering::Acquire);
        let h_next = self.q.next_index(h);

        if h_next == t {
            // We're full.
            return None;
        }

        // Safety: we maintain self.q.head (and thus the value of h here) within
        // range for storage.
        let unsafecell = unsafe {
            self.q.storage.get_unchecked(h)
        };
        let unsafecell_ptr = unsafecell.get();
        // Safety: this is dereferencing a raw pointer into the unsafecell,
        // which we can do because (1) the cell being between h and t implies
        // that it is not aliased, and (2) because we have &mut Self we know
        // we're not racing any other pushes for this slot. (Pops won't touch
        // this slot.)
        let maybeuninit = unsafe { &mut *unsafecell_ptr };

        Some(Entry {
            maybeuninit,
            head: &self.q.head,
            h_next,
            pushed: &self.q.pushed,
        })
    }

    /// Produces a future that resolves when there is enough space in the queue
    /// to push one element. It resolves into an [`Entry`], which entitles the
    /// holder to pushing an element without needing to check or `await`. This
    /// is a deliberate design choice -- it means you can cancel the future
    /// without losing the element you were trying to push.
    ///
    /// The returned `Entry` borrows `self` exclusively. This means you must
    /// use the `Entry`, or drop it, before you can request another. This
    /// prevents a deadlock, where you wait for a second permit that will never
    /// emerge.
    ///
    /// The future produced by `reserve` also borrows `self` exclusively. This
    /// means you can't simultaneously have two futures waiting for permits from
    /// the same `Pusher`. This wouldn't necessarily be a bad thing, but we need
    /// to maintain the exclusive borrow in order to pass it through to the
    /// `Entry`.
    ///
    /// # Cancellation
    ///
    /// **Cancel Safety:** Strict.
    ///
    /// This does basically nothing if cancelled (it is intrinsically
    /// cancel-safe).
    pub async fn reserve(&mut self) -> Entry<'_, T> {
        self.q.popped.until(|| self.try_reserve()).await
    }

    /// Attempts to stuff `value` into the queue.
    ///
    /// If there is space, ownership of `value` moves into the queue and this
    /// returns `Ok(())`.
    ///
    /// If there is not space, this returns `Err(value)` -- that is, ownership
    /// of `value` is handed back to you.
    pub fn try_push(&mut self, value: T) -> Result<(), T> {
        if let Some(entry) = self.try_reserve() {
            entry.push(value);
            Ok(())
        } else {
            Err(value)
        }
    }
}

/// Queue endpoint for popping data. Access to a `Popper` _only_ gives you the
/// right to pop data and enquire about pop-related properties.
///
/// See the module docs for more details.
#[derive(Debug)]
pub struct Popper<'a, T> {
    q: &'a Queue<'a, T>,
    _marker: NotSyncMarker,
}

impl<T> Popper<'_, T> {
    // Implementation note: Popper "owns" the tail and does not need to be
    // careful with its memory ordering, while the head is "foreign" and must be
    // synchronized.

    /// Checks if there is at least one item available to pop from the queue.
    ///
    /// Because the `Popper` endpoint has exclusive control over data movement
    /// out of the queue, if this returns `true`, the condition will remain true
    /// until a `pop` or `try_pop` happens through `self`, or `self` is dropped.
    ///
    /// If this returns `false`, of course, new items may appear at any time if
    /// the other end of the queue is pushed.
    pub fn can_pop(&self) -> bool {
        let t = self.q.tail.load(Ordering::Relaxed);
        let h = self.q.head.load(Ordering::Acquire);
        h != t
    }

    /// Pops an element out of the queue, if the queue is not empty.
    ///
    /// If the queue is empty, returns `None`.
    pub fn try_pop(&mut self) -> Option<T> {
        let t = self.q.tail.load(Ordering::Relaxed);
        let h = self.q.head.load(Ordering::Acquire);
        if h == t {
            // We're empty.
            return None;
        }

        let t_next = self.q.next_index(t);

        // Safety: we always maintain self.q.tail (and thus the value of t here)
        // within bounds for storage.
        let unsafecell = unsafe {
            self.q.storage.get_unchecked(t)
        };
        let unsafecell_ptr = unsafecell.get();
        // Safety: we're dereferencing the raw pointer into the UnsafeCell,
        // which we can do because (1) this cell is between t and h, so it's not
        // aliased by any pushing, and (2) we have a &mut Self, so it's also by
        // definition not aliased by any popping.
        let maybeuninit = unsafe { &mut *unsafecell_ptr };

        // Safety: we're reading the possibly-uninitialized contents of the
        // MaybeUninit, which we can do because the cell is between t and h, and
        // thus has been initialized by a previous push. We will bump tail just
        // below to switch the cell's state to uninitialized after reading.
        let result = unsafe { maybeuninit.assume_init_read() };

        self.q.tail.store(t_next, Ordering::Release);
        self.q.popped.notify();

        Some(result)
    }

    /// Produces a future that resolves to the next element that can be popped
    /// from the queue. If the queue is not empty, this will happen immediately
    /// on the first poll of the future; otherwise, it will happen when the
    /// future is polled after data has been pushed into the queue.
    ///
    /// Note that the future maintains an exclusive borrow over `self` until
    /// that happens -- so just as there can only be one `Popper` endpoint for a
    /// queue at any given time, there can only be one outstanding `pop` future
    /// for that endpoint. This means we don't have to define the order of
    /// competing pops, moving concerns about fairness to compile time.
    ///
    /// # Cancellation
    ///
    /// **Cancel Safety:** Strict.
    ///
    /// The future returned by this function has no side effects until it
    /// resolves to a popped element. If you drop it before it has resolved,
    /// no data is lost.
    pub async fn pop(&mut self) -> T {
        // NOTE: recognizing this function is what allows lilosdbg to show tasks
        // waiting to pop from queues -- inlining the contained future will
        // require debugger changes.
        self.q.pushed.until(move || self.try_pop()).await
    }
}

/// A reference to a free element in a queue, where you can deposit an element
/// without checking or waiting.
///
/// This is produced by [`Pusher::try_reserve`]/[`Pusher::reserve`] when they find
/// space available in the queue. The key property here is that producing a
/// `Entry` does not, by itself, change the queue state -- you can turn around
/// and `Drop` the `Entry` without losing data or pushing anything. This makes
/// cancel safety much easier to reason about.
#[derive(Debug)]
pub struct Entry<'q, T> {
    maybeuninit: &'q mut MaybeUninit<T>,
    head: &'q AtomicUsize,
    pushed: &'q Notify,
    h_next: usize,
}

impl<T> Entry<'_, T> {
    /// Pushes `value` to the queue, consuming this `Entry`.
    ///
    /// The `push` operation is guaranteed to succeed synchronously, since
    /// holding a `Entry` is proof that the next cell at the head of the queue
    /// is available for use.
    pub fn push(self, value: T) {
        self.maybeuninit.write(value);
        self.head.store(self.h_next, Ordering::Release);
        self.pushed.notify();
    }
}

//! A queue for moving data from one future/task into another.
//!
//! This is a "single-producer, single-consumer" queue that splits into separate
//! `Push` and `Pop` endpoints -- at any given time, there is at most one of
//! each alive in your program, ensuring that pushes and pops are not coming
//! from multiple directions.
//!
//! You create a queue by calling `Queue::new` and passing it a reference to its
//! backing storage. To actually use the queue, however, you must call
//! `Queue::split` to break it into two endpoints, `Push` and `Pop`. As their
//! names suggest, `Push` can be used to push things into the queue, and `Pop`
//! can be used to pop things out of it.
//!
//! The `Push` and `Pop` can then be handed off to separate code paths, so long
//! as they don't outlive the `Queue` and its storage.
//!
//! This queue uses the Rust type system to ensure that only one code path is
//! attempting to push or pop the queue at any given time, because both `Push`
//! and `Pop` endpoints borrow the central `Queue`, and an `async` operation to
//! push or pop through an endpoint borrows that endpoint in turn.
//!
//! # Implementation
//!
//! This is implemented as a concurrent lock-free Lamport queue. This has two
//! implications:
//! 
//! 1. If you can arrange the lifetimes correctly (i.e. make the queue static)
//!    it is actually safe to operate either Push or Pop from an ISR.
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

/// A single-producer, single-consumer queue. The `Queue` struct contains the
/// controlling information for the queue overall, and _borrows_ the storage.
///
/// See the module docs for details.
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

/// This type is easily sharable across threads, because there are no useful
/// operations that can be performed using only a shared reference.
unsafe impl<'s, T> Sync for Queue<'s, T> where T: Send {}

impl<'s, T> Queue<'s, T> {
    /// Creates a queue, borrowing the uninitialized `storage` (which will be
    /// arbitrarily overwritten).
    pub fn new(storage: &'s mut [MaybeUninit<T>]) -> Self {
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
            &mut *(storage as *mut [MaybeUninit<T>] as *mut _)
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
    pub fn split(&mut self) -> (Push<'_, T>, Pop<'_, T>) {
        (
            Push { q: self, _marker: crate::NotSyncMarker::default() },
            Pop { q: self, _marker: crate::NotSyncMarker::default() },
        )
    }

    fn next_index(&self, i: usize) -> usize {
        // This produced better code than using remainder on ARMv7-M last
        // I checked.
        if i + 1 == self.storage.len() { 0 } else { i + 1 }
    }

}

/// It's entirely possible to drop a non-empty Queue in correct code, unlike
/// (say) a `lilos::list`, so we provide a Drop impl that goes through and
/// cleans up queued elements.
impl<'s, T> Drop for Queue<'s, T> {
    fn drop(&mut self) {
        let h = self.head.load(Ordering::SeqCst);
        let mut t = self.head.load(Ordering::SeqCst);

        while h != t {
            // Safety: this is unsafe because we're accessing the UnsafeCell
            // contents and dropping whatever's in the MaybeUninit. We can do
            // this because, since h != t, we are popping a previously
            // initialized cell.
            unsafe {
                let cell_contents = &mut *self.storage[t].get();
                core::ptr::drop_in_place(cell_contents.as_mut_ptr());
            }
            t = self.next_index(t);
        }
    }
}

/// Queue endpoint for pushing data. Access to a `Push` _only_ gives you the
/// right to push data and enquire about push-related properties.
///
/// See the module docs for more details.
pub struct Push<'a, T> {
    q: &'a Queue<'a, T>,
    _marker: crate::NotSyncMarker,
}

impl<'q, T> Push<'q, T> {
    // Implementation note: Push "owns" the head and does not need to be careful
    // with its memory ordering, while the tail is "foreign" and must be
    // synchronized.

    /// Checks if there is room to push at least one item. Because the `Push`
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

    /// Attempts to stuff `value` into the queue.
    ///
    /// If there is space, ownership of `value` moves into the queue and this
    /// returns `Ok(())`.
    ///
    /// If there is not space, this returns `Err(value)` -- that is, ownership
    /// of `value` is handed back to you.
    pub fn try_push(&mut self, value: T) -> Result<(), T> {
        let h = self.q.head.load(Ordering::Relaxed);
        let t = self.q.tail.load(Ordering::Acquire);
        let h_next = self.q.next_index(h);

        if h_next == t {
            // We're full.
            return Err(value);
        }

        // Safety: this is unsafe due to the write through the raw pointer.
        // Because this cell is between h and t, it is not aliased and is
        // uninitialized. Because we're writing MaybeUninit, we can just assign
        // to uninitialized memory instead of using ptr::write. And because we
        // required a &mut, we know we're not racing any other pushes for this
        // slot.
        unsafe {
            *self.q.storage[h].get() = MaybeUninit::new(value);
        }

        // We can store instead of compare-exchange here because we are the only
        // Push manipulating this field.
        self.q.head.store(h_next, Ordering::Release);
        self.q.pushed.notify();
        Ok(())
    }

    /// Produces a future that resolves when `value` has been pushed into the
    /// queue, and not before. This implies that at least one free slot must
    /// open in the queue -- either by never having been filled, or by being
    /// freed up by a pop -- for the future to resolve.
    ///
    /// Note that the future maintains an exclusive borrow over `self` until
    /// that happens -- so just as there can only be one `Push` endpoint for a
    /// queue at any given time, there can only be one outstanding `push` future
    /// for that endpoint. This means we don't have to define the order of
    /// competing pushes, moving concerns about fairness to compile time.
    ///
    /// # Cancellation
    ///
    /// The future returned by `push` takes ownership of `value` immediately. If
    /// the future is dropped before `value` makes it into the queue, `value` is
    /// dropped along with it.
    pub async fn push(&mut self, value: T) {
        let mut value = Some(value);
        self.q.popped.until(move || {
            match self.try_push(value.take().unwrap()) {
                Ok(()) => true,
                Err(revalue) => {
                    value = Some(revalue);
                    false
                }
            }
        }).await
    }
}

/// Queue endpoint for popping data. Access to a `Pop` _only_ gives you the
/// right to pop data and enquire about pop-related properties.
///
/// See the module docs for more details.
pub struct Pop<'a, T> {
    q: &'a Queue<'a, T>,
    _marker: crate::NotSyncMarker,
}

impl<'q, T> Pop<'q, T> {
    // Implementation note: Pop "owns" the tail and does not need to be careful
    // with its memory ordering, while the head is "foreign" and must be
    // synchronized.

    /// Checks if there is at least one item available to pop from the queue.
    ///
    /// Because the `Pop` endpoint has exclusive control over data movement out
    /// of the queue, if this returns `true`, the condition will remain true
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

        // Safety: this is unsafe due to the read through the UnsafeCell's raw
        // pointer, and the move out of the MaybeUninit.
        // Because this cell is between t and h, it is not aliased and is
        // initialized. 
        let result = Some(unsafe {
            let cell_contents = &*self.q.storage[t].get();
            cell_contents.as_ptr().read()
        });

        self.q.tail.store(t_next, Ordering::Release);
        self.q.popped.notify();

        result
    }

    /// Produces a future that resolves to the next element that can be popped
    /// from the queue. If the queue is not empty, this will happen immediately
    /// on the first poll of the future; otherwise, it will happen when the
    /// future is polled after data has been pushed into the queue.
    ///
    /// Note that the future maintains an exclusive borrow over `self` until
    /// that happens -- so just as there can only be one `Pop` endpoint for a
    /// queue at any given time, there can only be one outstanding `pop` future
    /// for that endpoint. This means we don't have to define the order of
    /// competing pops, moving concerns about fairness to compile time.
    ///
    /// # Cancellation
    ///
    /// The future returned by this function has no side effects until it
    /// resolves to a popped element. If you drop it before it has resolved,
    /// no data is lost.
    pub async fn pop(&mut self) -> T {
        self.q.pushed.until(move || self.try_pop()).await
    }
}

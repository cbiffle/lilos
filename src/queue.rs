use core::cell::Cell;

use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::pin::Pin;

use crate::list::List;

/// A queue of `T`s that can be sent between tasks.
pub struct Queue<'a, T> {
    /// Pointer to the base of a contiguous buffer of `T`s, exactly `capacity`
    /// slots long. These are tracked as `MaybeUninit` because we move values in
    /// and out of them during normal operation.
    storage: *mut MaybeUninit<T>,
    /// Number of slots in `storage`.
    capacity: usize,
    /// Number of pushes; `head % capacity` gives the index of the next slot in
    /// `storage` to write during `push`.
    head: Cell<usize>,
    /// Number of pops; `tail % capacity` gives the index of the next slot in
    /// `storage` to read during `pop`.
    tail: Cell<usize>,

    /// List of tasks waiting to push, when the queue has room.
    push_waiters: List<()>,
    /// List of tasks waiting to pop, when the queue has data.
    pop_waiters: List<()>,

    _marker: PhantomData<&'a mut [T]>,
}

impl<'a, T> Queue<'a, T> {
    pub unsafe fn new(storage: &'a mut [MaybeUninit<T>]) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Queue {
            storage: storage.as_mut_ptr(),
            capacity: storage.len(),
            head: Cell::new(0),
            tail: Cell::new(0),
            push_waiters: ManuallyDrop::into_inner(List::new()),
            pop_waiters: ManuallyDrop::into_inner(List::new()),

            _marker: PhantomData,
        })
    }

    pub unsafe fn finish_init(mut self: Pin<&mut Self>) {
        List::finish_init(self.as_mut().push_waiters_mut());
        List::finish_init(self.as_mut().pop_waiters_mut());
    }

    pub fn is_full(&self) -> bool {
        self.head.get().wrapping_sub(self.tail.get()) == self.capacity
    }

    pub fn is_empty(&self) -> bool {
        self.head.get() == self.tail.get()
    }

    /// Returns a future that will insert `value` at the head of the queue, once
    /// space is available and earlier pushes have completed.
    ///
    /// Attempts to push are processed in order. The `value` is captured by the
    /// future; between the time when `push` returns, and when the future
    /// resolves, cancelling/dropping the future will also drop `value`.
    ///
    /// When the future resolves, `value` is owned by the queue.
    pub async fn push(self: Pin<&Self>, value: T) {
        if self.is_full() {
            let waker = core::future::get_task_context(|cx| cx.waker().clone());
            create_node!(node, (), waker);
            while self.is_full() {
                self.push_waiters().insert_and_wait(node.as_mut()).await;
            }
        }

        // not full
        let h = self.head.get();
        unsafe {
            core::ptr::write(
                self.storage.add(h % self.capacity),
                MaybeUninit::new(value),
            );
        }
        self.head.set(h + 1);
        // If we were empty...
        if h == self.tail.get() {
            self.pop_waiters().wake_one();
        }
    }

    /// Returns a future that will resolve to a value removed from the tail of
    /// the queue, once a value is available and earlier pops have completed.
    ///
    /// Attempts to pop are processed in order. Between the time `pop` returns,
    /// and when the future resolves, the future can be dropped/cancelled
    /// without affecting the queue.
    ///
    /// When the future resolves, it has the side effect of moving one `T` out
    /// of the queue to return it.
    pub async fn pop(self: Pin<&Self>) -> T {
        if self.is_empty() {
            let waker = core::future::get_task_context(|cx| cx.waker().clone());
            create_node!(node, (), waker);
            while self.is_empty() {
                self.pop_waiters().insert_and_wait(node.as_mut()).await;
            }
        }

        // not empty
        let t = self.tail.get();
        self.tail.set(t + 1);
        // If we were full...
        if self.head.get().wrapping_sub(t) == self.capacity {
            self.push_waiters().wake_one();
        }
        unsafe {
            core::ptr::read(self.storage.add(t % self.capacity)).assume_init()
        }
    }

    /// Internal pin projection.
    fn push_waiters_mut(self: Pin<&mut Self>) -> Pin<&mut List<()>> {
        unsafe { Pin::map_unchecked_mut(self, |s| &mut s.push_waiters) }
    }

    /// Internal pin projection.
    fn pop_waiters_mut(self: Pin<&mut Self>) -> Pin<&mut List<()>> {
        unsafe { Pin::map_unchecked_mut(self, |s| &mut s.pop_waiters) }
    }

    /// Internal pin projection.
    fn push_waiters(self: Pin<&Self>) -> Pin<&List<()>> {
        unsafe { Pin::map_unchecked(self, |s| &s.push_waiters) }
    }

    /// Internal pin projection.
    fn pop_waiters(self: Pin<&Self>) -> Pin<&List<()>> {
        unsafe { Pin::map_unchecked(self, |s| &s.pop_waiters) }
    }
}

/// Dropping a queue drops any remaining elements within it.
///
/// It's not possible to drop a queue while any futures are operating on it,
/// because they borrow the queue.
impl<'a, T> Drop for Queue<'a, T> {
    fn drop(&mut self) {
        inner_drop(unsafe { Pin::new_unchecked(self) });

        fn inner_drop<'a, T>(this: Pin<&mut Queue<'a, T>>) {
            let h = this.head.get();
            let mut t = this.tail.get();
            while t != h {
                unsafe {
                    core::ptr::drop_in_place(
                        this.storage.add(t % this.capacity),
                    );
                }
                t = t.wrapping_add(1);
            }
        }
    }
}

/// Creates a pinned queue on the stack.
#[macro_export]
macro_rules! create_queue {
    ($var:ident) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::queue::Queue::new())
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::queue::Queue::finish_init($var.as_mut());
        }
    };
}


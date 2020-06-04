//! Queues for passing values between tasks.
//!
//! A `Queue<T, S>` manages storage for some number of values of type `T`, where
//! the storage has type `S`. More concretely, there are two main cases:
//!
//! - `Queue<T, [MaybeUninit<T>; N]>`: the queue owns its storage of `N`
//!   elements.
//!
//! - `Queue<T, &'a mut [MaybeUninit<T>]>`: the queue borrows its storage with
//!   lifetime `'a`.
//!
//! Notice that queue storage is `MaybeUninit`. The memory that backs the queue
//! is assumed to be uninitialized by default. The queue will take care of
//! initializing the portions it's using and ensuring that e.g. `drop` gets run
//! at the right times. If you loan memory to a queue and then drop it, the
//! memory is *again uninitialized,* because the queue will have dropped any
//! contents in-place.
//!
//! If you'd prefer not to worry about the lifetime of the queue's storage, we
//! provide macros for the two common cases: `create_queue` for queues that live
//! on the stack, and `create_static_queue` for queues at static scope.

use core::cell::Cell;

use core::mem::{ManuallyDrop, MaybeUninit};
use core::pin::Pin;
use core::ptr::NonNull;

use as_slice::AsMutSlice;

use crate::exec::noop_waker;
use crate::list::List;

/// A queue of `T`s that can be sent between tasks, stored as `S`, which may be
/// an array or a slice.
pub struct Queue<T, S: AsMutSlice<Element = MaybeUninit<T>>> {
    /// Copy of `S`, which mostly matters if `S` is an array.
    storage: S,
    /// Pointer to the first storage element in `S`. This is redundant; we use
    /// it to mutate `S` even though it's aliased. We can do this because we
    /// require pinning.
    storage_ptr: NonNull<MaybeUninit<T>>,

    /// Number of items present in the queue.
    pending: Cell<usize>,

    /// Index of next slot in `storage` to write during `push`. Must fall in the
    /// range `0..storage.len()`.
    head: Cell<usize>,
    /// Index of next slot in `storage` to read during `pop`. Must fall in the
    /// range `0..storage.len()`.
    tail: Cell<usize>,

    /// List of tasks waiting to push, when the queue has room.
    push_waiters: List<()>,
    /// List of tasks waiting to pop, when the queue has data.
    pop_waiters: List<()>,
}

impl<S: AsMutSlice<Element = MaybeUninit<T>>, T> Queue<T, S> {
    /// Creates an initialized but bogus `Queue`.
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call `finish_init`.
    pub unsafe fn new(storage: S) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Queue {
            storage_ptr: NonNull::dangling(),
            storage,
            pending: Cell::new(0),
            head: Cell::new(0),
            tail: Cell::new(0),
            push_waiters: ManuallyDrop::into_inner(List::new()),
            pop_waiters: ManuallyDrop::into_inner(List::new()),
        })
    }

    /// Finishes initializing a queue, discharging obligations from `new`.
    ///
    /// # Safety
    ///
    /// This is safe to call exactly once on the result of `new`, after taking
    /// it out of `ManuallyDrop`, moving it to its final resting place, and
    /// pinning it.
    pub unsafe fn finish_init(mut self: Pin<&mut Self>) {
        // If `S` stores `T`s by value (i.e. we contain an array), its base
        // address may have changed, so we patch the pointer now.
        Pin::get_unchecked_mut(self.as_mut()).storage_ptr =
            NonNull::from(&mut self.as_mut().storage_mut().as_mut_slice()[0]);

        List::finish_init(self.as_mut().push_waiters_mut());
        List::finish_init(self.as_mut().pop_waiters_mut());
    }

    pub fn capacity(&self) -> usize {
        self.storage.as_slice().len()
    }

    pub fn is_full(&self) -> bool {
        self.pending.get() == self.capacity()
    }

    pub fn len(&self) -> usize {
        self.pending.get()
    }

    pub fn is_empty(&self) -> bool {
        self.pending.get() == 0
    }

    /// Returns a future that will insert `value` at the head of the queue, once
    /// space is available and earlier pushes have completed.
    ///
    /// Attempts to push are processed in order. The `value` is captured by the
    /// future; between the time when `push` returns, and when the future
    /// resolves, cancelling/dropping the future will also drop `value`.
    ///
    /// When the future resolves, `value` is owned by the queue.
    pub async fn push(self: Pin<&Self>, mut value: T) {
        loop {
            match self.try_push(value) {
                Ok(_) => return,
                Err(revalue) => {
                    value = revalue;
                    create_node!(node, (), noop_waker());
                    self.push_waiters().insert_and_wait(node.as_mut()).await;
                }
            }
        }
    }

    /// Insert `value` at the head of the queue if space is currently available.
    ///
    /// This is the non-blocking equivalent of `push`.
    pub fn try_push(self: Pin<&Self>, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        // not full
        let h = self.head.get();
        debug_assert!(h < self.capacity());

        // Begin committing changes.
        // Move `value` into queue memory.
        unsafe {
            core::ptr::write(
                self.storage_ptr.as_ptr().add(h),
                MaybeUninit::new(value),
            );
        }
        // Advance head modulo capacity.
        self.head
            .set(if h == self.capacity() - 1 { 0 } else { h + 1 });
        // Update pending count.
        self.pending.set(self.pending.get() + 1);

        // If we were empty...
        if h == self.tail.get() {
            self.pop_waiters().wake_one();
        }

        Ok(())
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
            create_node!(node, (), noop_waker());
            while self.is_empty() {
                self.pop_waiters().insert_and_wait(node.as_mut()).await;
            }
        }

        debug_assert!(!self.is_empty());

        // not empty
        let t = self.tail.get();
        debug_assert!(t < self.capacity());

        // Begin committing changes.
        // Move result out of queue memory.
        let result = unsafe {
            core::ptr::read(self.storage_ptr.as_ptr().add(t)).assume_init()
        };
        // Advance tail pointer modulo capacity
        self.tail
            .set(if t == self.capacity() - 1 { 0 } else { t + 1 });
        // Update pending count.
        self.pending.set(self.pending.get() - 1);

        // If we were full...
        if t == self.head.get() {
            self.push_waiters().wake_one();
        }

        result
    }

    /// Internal pin projection.
    fn storage_mut(self: Pin<&mut Self>) -> &mut [MaybeUninit<T>] {
        unsafe { Pin::get_unchecked_mut(self).storage.as_mut_slice() }
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
impl<T, S: AsMutSlice<Element = MaybeUninit<T>>> Drop for Queue<T, S> {
    fn drop(&mut self) {
        inner_drop(unsafe { Pin::new_unchecked(self) });

        fn inner_drop<T, S: AsMutSlice<Element = MaybeUninit<T>>>(
            this: Pin<&mut Queue<T, S>>,
        ) {
            let mut t = this.tail.get();
            let n = this.pending.get();
            let s = this.storage_mut();
            for _ in 0..n {
                unsafe {
                    core::ptr::drop_in_place(s[t].as_mut_ptr());
                }
                t = (t + 1) % s.len();
            }
        }
    }
}

/// Creates a pinned queue on the stack.
///
/// Because a pinned value must not move, this does not *return* the queue, but
/// instead binds it under the name of your choice:
///
/// ```ignore
/// create_queue!(q, [MaybeUninit::<u32>::uninit(); 100]);
/// // and the type of q is...
/// let q: Pin<&Queue<u32, _>> = q;
/// ```
///
/// For the common case of declaring a queue with owned storage, there's also a
/// three-argument version that saves you the trouble of typing out
/// `MaybeUninit`:
///
/// ```ignore
/// create_queue!(q, u32, 100);
/// ```
///
/// which expands into the code in the previous example.
#[macro_export]
macro_rules! create_queue {
    ($var:ident, $t:ty, $n:expr) => {
        create_queue!($var, [core::mem::MaybeUninit::<$t>::uninit(); $n]);
    };
    ($var:ident, $stor:expr) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::queue::Queue::new(
                $stor,
            ))
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::queue::Queue::finish_init($var.as_mut());
        }
        // Downgrade the &mut
        let $var = $var.into_ref();
    };
}

/// Creates a queue at static scope backed by an array.
///
/// The expression
///
/// ```ignore
/// let q = create_static_queue!([u32; 100]);
/// ```
///
/// statically allocates space for a buffer of 100 `u32`s and the state of one
/// `Queue`. It returns a pinned queue reference; specifically:
///
/// ```ignore
/// let q: Pin<&'static Queue<u32, _>>  = create_static_queue!([u32; 100]);
/// ```
///
/// Each site where `create_static_queue!` gets used creates a separate queue.
/// At runtime, each site must be executed *exactly once* to initialize the
/// queue and produce a reference (e.g. in `main`). This property is tracked
/// using an atomic flag; if code tries to initialize the queue a second time,
/// it panics.
#[macro_export]
macro_rules! create_static_queue {
    ([$t:ty; $sz:expr]) => {{
        use core::mem::{ManuallyDrop, MaybeUninit};
        use core::sync::atomic::{AtomicBool, Ordering};
        use $crate::queue::Queue;

        static INIT: AtomicBool = AtomicBool::new(false);
        static mut Q_STOR: [MaybeUninit<$t>; $sz] =
            [MaybeUninit::uninit(); $sz];
        static mut Q: MaybeUninit<
            Queue<$t, &'static mut [MaybeUninit<$t>; $sz]>,
        > = MaybeUninit::uninit();

        // Ensure that code only makes it past this point once.
        assert_eq!(INIT.swap(true, Ordering::SeqCst), false);

        // Initialize the queue enough that we can start using references.
        unsafe {
            core::ptr::write(
                Q.as_mut_ptr(),
                ManuallyDrop::into_inner(Queue::new(&mut Q_STOR)),
            );
        }

        let mut q: Pin<&'static mut _> =
            unsafe { Pin::new_unchecked(&mut *Q.as_mut_ptr()) };
        unsafe {
            Queue::finish_init(q.as_mut());
        }

        // Downgrade the &mut to keep any smart alec from calling
        // finish_init again.
        q.into_ref()
    }};
}

#[allow(dead_code)]
async fn static_queue_test() {
    // Check that the convenient syntax works:
    let q = create_static_queue!([bool; 123]);
    // Check that the type is what we expect.
    let q: Pin<&'static Queue<bool, &'static mut [MaybeUninit<bool>; 123]>> = q;

    q.push(true).await;
    q.pop().await;
}

#[allow(dead_code)]
async fn queue_test() {
    // Check that the convenient syntax works:
    create_queue!(q, [MaybeUninit::<bool>::uninit(); 123]);
    // Check that the type is what we expect.
    let q: Pin<&Queue<bool, [MaybeUninit<bool>; 123]>> = q;

    q.push(true).await;
    q.pop().await;
}

//! Fair mutex that must be pinned.
//!
//! This implements a mutex, or lock, guarding a value of type `T`. Creating a
//! `Mutex` by hand is somewhat involved (see [`Mutex::new`] for details), so
//! there's a convenience macro, [`create_mutex!`].
//!
//! If you don't want to store a value inside the mutex, use a `Mutex<()>`.
//!
//! # Implementation details
//!
//! This implementation uses a wait-list to track all processes that are waiting
//! to unlock the mutex. This makes unlocking more expensive, but means that the
//! unlock operation is *fair*, preventing starvation of contending tasks.
//!
//! However, in exchange for this property, mutexes must be pinned, which makes
//! using them slightly more awkward.

use core::cell::UnsafeCell;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::exec::noop_waker;
use crate::list::List;

/// Holds a `T` that can be accessed from multiple concurrent futures/tasks, but
/// only one at a time.
///
/// This implementation is more efficient than a spin-lock, because when the
/// mutex is contended, all competing tasks but one register themselves for
/// waking when the mutex is freed. Thus, nobody needs to spin.
///
/// When the mutex is unlocked, the task doing the unlocking will check the
/// mutex's wait list and release the oldest task on it.
pub struct Mutex<T: ?Sized> {
    /// Stores 0 when unlocked, 1 when locked.
    state: AtomicUsize,
    /// Accumulates the wakers for all tasks that have attempted to obtain this
    /// mutex while it was locked.
    waiters: List<()>,
    /// The contents of the mutex. Safe to access only when `state` is
    /// atomically flipped 0->1.
    value: UnsafeCell<T>,
}

impl<T> Mutex<T> {
    /// Returns an initialized but invalid mutex.
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call `finish_init`.
    pub unsafe fn new(contents: T) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Mutex {
            state: AtomicUsize::new(0),
            waiters: ManuallyDrop::into_inner(List::new()),
            value: UnsafeCell::new(contents),
        })
    }

    /// Finishes initializing a mutex, discharging obligations from `new`.
    ///
    /// # Safety
    ///
    /// This is safe to call exactly once on the result of `new`, after it has
    /// been moved to its final position and pinned.
    pub unsafe fn finish_init(this: Pin<&mut Self>) {
        List::finish_init(this.waiters_mut());
    }

    /// Returns a future that will attempt to obtain the mutex each time it gets
    /// polled, completing only when it succeeds.
    pub async fn lock(self: Pin<&Self>) -> MutexGuard<'_, T> {
        // Complete synchronously if the mutex is uncontended.
        if self.state.fetch_or(1, Ordering::Acquire) == 0 {
            return MutexGuard { mutex: self };
        }

        // We'd like to put our name on the wait list, please.
        create_node!(wait_node, (), noop_waker());

        self.waiters().insert_and_wait(wait_node.as_mut()).await;

        MutexGuard { mutex: self }
    }

    fn waiters_mut(self: Pin<&mut Self>) -> Pin<&mut List<()>> {
        // Safety: this is a structural pin projection.
        unsafe { Pin::new_unchecked(&mut Pin::get_unchecked_mut(self).waiters) }
    }

    fn waiters(self: Pin<&Self>) -> Pin<&List<()>> {
        // Safety: this is a structural pin projection.
        unsafe { Pin::map_unchecked(self, |s| &s.waiters) }
    }
}

/// Convenience macro for creating a pinned mutex on the stack.
///
/// This declares a local variable `ident` of type `Pin<&mut Mutex<T>>`, where
/// `T` is the type of `expr`. The contents of the mutex are initialized to the
/// value of `expr`.
#[macro_export]
macro_rules! create_mutex {
    ($var:ident, $contents:expr) => {
        let $var = $contents;
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::mutex::Mutex::new($var))
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::mutex::Mutex::finish_init($var.as_mut());
        }
        // Drop mutability.
        let $var = $var.as_ref();
    };
}

/// Smart pointer representing successful locking of a mutex.
pub struct MutexGuard<'a, T> {
    mutex: Pin<&'a Mutex<T>>,
}

impl<'a, T> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        self.mutex.state.store(0, Ordering::Release);
        self.mutex.waiters().wake_one();
    }
}

impl<'a, T> core::ops::Deref for MutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        let v = &self.mutex.value;
        // Safety: this is deriving a shared reference to the contents of the
        // UnsafeCell. Because `self`, a guard, exists, we know the mutex is
        // locked. Because the caller was able to call a method on `&self`, we
        // further know that no other `&mut` references to this guard or its
        // contents exist.
        unsafe { &*v.get() }
    }
}

impl<'a, T> core::ops::DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let v = &self.mutex.value;
        // Safety: this is deriving an exclusive reference to the contents of
        // the UnsafeCell. Because `self`, a guard, exists, we know the mutex is
        // locked. Because the caller was able to call a method on `&mut self`,
        // we further know that no other `&` or `&mut` references to this guard
        // or its contents exist.
        unsafe { &mut *v.get() }
    }
}

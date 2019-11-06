//! Fair mutex that must be pinned.
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
    pub unsafe fn new(contents: T) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Mutex {
            state: AtomicUsize::new(0),
            waiters: ManuallyDrop::into_inner(List::new()),
            value: UnsafeCell::new(contents),
        })
    }

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
        let waker = core::future::get_task_context(|cx| cx.waker().clone());
        create_node!(wait_node, (), waker);

        self.waiters().insert_and_wait(wait_node.as_mut()).await;

        MutexGuard { mutex: self }
    }

    fn waiters_mut(self: Pin<&mut Self>) -> Pin<&mut List<()>> {
        unsafe { Pin::new_unchecked(&mut Pin::get_unchecked_mut(self).waiters) }
    }

    fn waiters(self: Pin<&Self>) -> Pin<&List<()>> {
        unsafe { Pin::map_unchecked(self, |s| &s.waiters) }
    }
}

#[macro_export]
macro_rules! create_mutex {
    ($var:ident, $contents:expr) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::mutex::Mutex::new(
                $contents,
            ))
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::mutex::Mutex::finish_init($var.as_mut());
        }
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
        unsafe { &*self.mutex.value.get() }
    }
}

impl<'a, T> core::ops::DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.value.get() }
    }
}

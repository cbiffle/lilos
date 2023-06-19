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

use crate::atomic::AtomicArithExt;
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
#[derive(Debug)]
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
        // Safety: List::new is unsafe because it produces a value that cannot
        // yet be dropped. We discharge this obligation by unwrapping it and
        // moving it into a _new_ ManuallyDrop, kicking the can down the road.
        let list = unsafe { List::new() };
        ManuallyDrop::new(Mutex {
            state: AtomicUsize::new(0),
            waiters: ManuallyDrop::into_inner(list),
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
        // Safety: List::finish_init is safe if our _own_ safety contract is
        // upheld.
        unsafe {
            List::finish_init(this.waiters_mut());
        }
    }

    /// Locks this mutex immediately if it is free, and returns a guard for
    /// holding it locked.
    ///
    /// If the mutex is _not_ free, returns `None`.
    pub fn try_lock(self: Pin<&Self>) -> Option<MutexGuard<'_, T>> {
        if self.state.fetch_or_polyfill(1, Ordering::Acquire) == 0 {
            Some(MutexGuard { mutex: self })
        } else {
            None
        }
    }

    /// Unlocks the mutex.
    ///
    /// Normally, you unlock a mutex by dropping the `MutexGuard` that you got
    /// from `try_lock` or `lock`. That proves that you locked it in the first
    /// place.
    ///
    /// `unlock` allows you to unlock a mutex you didn't lock. This can wreak
    /// all sorts of havoc if used incorrectly.
    ///
    /// # Safety
    ///
    /// You can use this safely _only_ if you know that no other code thinks it
    /// still has the mutex locked, including the code calling `unlock`. You
    /// might do this if you have, for instance, used `forget` on the
    /// `MutexGuard` for some reason.
    pub unsafe fn unlock(self: Pin<&Self>) {
        if self.waiters().wake_one() {
            // Someone was waiting. We will leave the state as taken to ensure
            // that no interloper can steal the mutex from the new rightful
            // owner before that owner is polled next.
        } else {
            // Nobody was waiting. Allow whoever tries next to get the mutex.
            self.state.store(0, Ordering::Release);
        }
    }

    /// Returns a future that will attempt to obtain the mutex each time it gets
    /// polled, completing only when it succeeds.
    ///
    /// If the mutex is free at the time of the first `poll`, the future will
    /// resolve cheaply without blocking.
    ///
    /// # Cancellation
    ///
    /// Cancellation behavior for the returned future is slightly subtle.
    ///
    /// - If dropped before it's polled _at all_ it does essentially nothing.
    /// - If dropped once it's added itself to the wait list for the mutex, but
    ///   before it has been given the mutex, it will detach from the wait list.
    /// - If dropped after it has been given the mutex, but before it's been
    ///   polled (and thus given a chance to notice that), it will wake the next
    ///   waiter on the mutex wait list.
    pub async fn lock(self: Pin<&Self>) -> MutexGuard<'_, T> {
        // Complete synchronously if the mutex is uncontended.
        // TODO this is repeated above the loop to avoid the cost of re-setting
        // up the wait node in every loop iteration, and to avoid setting it up
        // in the uncontended case. Is this premature optimization?
        if let Some(guard) = self.try_lock() {
            return guard;
        }

        // We'd like to put our name on the wait list, please.
        create_node!(wait_node, (), noop_waker());

        self.waiters().insert_and_wait_with_cleanup(
            wait_node.as_mut(),
            || {
                // Safety: if we are evicted from the wait list, which is
                // the only time this cleanup routine is called, then we own
                // the mutex and are responsible for unlocking it, though we
                // have not yet created the MutexGuard.
                unsafe {
                    self.unlock();
                }
            },
        ).await;
        // We've been booted out of the waiter list, which (by construction)
        // only happens in `unlock`. Meaning, someone just released the
        // mutex and it's our turn. However, they should _not_ have cleared
        // the mutex flag to prevent races -- and so we cannot use
        // `try_lock` which expects to find the flag clear.
        debug_assert_eq!(self.state.load(Ordering::Acquire), 1);

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
///
/// For instance,
///
/// ```ignore
/// create_mutex!(my_mutex, 42usize);
/// // ...
/// *my_mutex.lock().await += 4; // now contains 46
/// ```
#[macro_export]
macro_rules! create_mutex {
    ($var:ident, $contents:expr) => {
        let $var = $contents;
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let mut $var = core::pin::pin!(unsafe {
            core::mem::ManuallyDrop::into_inner($crate::mutex::Mutex::new($var))
        });
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::mutex::Mutex::finish_init($var.as_mut());
        }
        // Drop mutability.
        let $var = $var.as_ref();
    };
}

/// Convenience macro for creating a pinned mutex in static memory.
///
/// This declares a local variable `ident` of type `Pin<&mut Mutex<T>>`, but
/// which _points to_ a `Mutex<T>` in static memory. This helps to keep your
/// application's memory usage transparent at build time, but it's slightly
/// trickier to use than `create_mutex`, because it will only succeed _once_ in
/// the life of your program: you cannot use a function containing
/// `create_static_mutex` from several tasks to create several mutexes, because
/// they would alias. If you need that, use `create_mutex`.
///
/// Unlike `create_mutex`, `create_static_mutex` returns its `Pin<&mut
/// Mutex<T>>` and can just be assigned to a variable. However, it does require
/// that you tell it the type explicitly:
///
/// ```ignore
/// let my_mutex = create_static_mutex!(usize, 42);
/// // ...
/// *my_mutex.lock().await += 4;
/// ```
///
#[macro_export]
macro_rules! create_static_mutex {
    ($t:ty, $contents:expr) => {{
        use core::sync::atomic::{AtomicBool, Ordering};
        use core::mem::{ManuallyDrop, MaybeUninit};
        use core::pin::Pin;
        use $crate::atomic::AtomicExt;

        // Flag for detecting multiple executions.
        static INIT: AtomicBool = AtomicBool::new(false);

        assert_eq!(INIT.swap_polyfill(true, Ordering::SeqCst), false);

        // Static mutex storage.
        static mut M: MaybeUninit<$crate::mutex::Mutex<$t>> = MaybeUninit::uninit();

        // Safety: there are two things going on here:
        // - Discharging the obligations of Mutex::new (which we'll do in a sec)
        // - Write to a static mut, which is safe because of our INIT check
        //   above.
        unsafe {
            M = MaybeUninit::new(
                ManuallyDrop::into_inner($crate::mutex::Mutex::new($contents))
            );
        }

        // Safety: this is the only mutable reference to M that will ever exist
        // in the program, so we can pin it as long as we don't touch M again
        // below (which we do not).
        let mut m: Pin<&'static mut _> = unsafe {
            Pin::new_unchecked(&mut *M.as_mut_ptr())
        };

        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::mutex::Mutex::finish_init(m.as_mut());
        }

        // Drop mutability and return value.
        m.into_ref()
    }};
}

/// Smart pointer representing successful locking of a mutex.
#[derive(Debug)]
pub struct MutexGuard<'a, T> {
    mutex: Pin<&'a Mutex<T>>,
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        // Safety: we are by definition the holder of the mutex, so we can use
        // the normally unsafe `unlock` operation to avoid repeating code.
        unsafe {
            self.mutex.unlock();
        }
    }
}

impl<T> core::ops::Deref for MutexGuard<'_, T> {
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

impl<T> core::ops::DerefMut for MutexGuard<'_, T> {
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

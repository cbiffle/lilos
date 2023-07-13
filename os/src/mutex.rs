//! Fair mutex that must be pinned.
//!
//! This implements a mutex (a kind of lock) guarding a value of type `T`.
//! Creating a `Mutex` by hand is somewhat involved (see [`Mutex::new`] for
//! details), so there's a convenience macro,
//! [`create_mutex!`][crate::create_mutex].
//!
//! If you don't want to store a value inside the mutex, use a `Mutex<()>`.
//!
//! # `lock` vs `lock_assuming_cancel_safe`
//!
//! This mutex API is subtly different from most other async mutex APIs in that
//! its default `lock` operation does _not_ return a "smart pointer" style mutex
//! guard that can `Deref` to access the guarded data. Instead, by default,
//! locking this mutex only grants you the ability to do a single action with
//! the guarded data, without being able to `await` during the action. There is
//! a very good reason for this, but it's subtle.
//!
//! You'd use this default `lock` API like this:
//!
//! ```ignore
//! some_mutex.lock().await.perform(|data| data.squirrels += 1);
//! ```
//!
//! That is, you call `.lock().await` to block until the mutex is yours, and
//! then call `perform` on the result to access the guarded data. The function
//! provided to `perform` must be a normal Rust `fn`, and _not_ an `async fn`.
//! The mutex is released as soon as `perform` runs your function. This means
//! there is no way to make alterations to the guarded data, `await`, and then
//! try and make more.
//!
//! This helps to avoid a common implementation mistake in software using
//! mutexes: assuming that you can temporarily violate invariants on the data
//! guarded by the mutex because you will restore things before you unlock it --
//! but then `await`ing (and thus accepting possible cancellation) while those
//! invariants are still being violated. This can cause the next observer of the
//! guarded data to find the data in an invalid state, often leading to panics
//! -- but _not_ panics in the code that had the bug! This makes the bug very
//! difficult to track down.
//!
//! To make this class of bugs harder to write, the default `lock` operation on
//! this mutex doesn't allow you to access the guarded data on two sides of an
//! `await` point.
//!
//! But because this doesn't cover every use case, and in keeping with the
//! broader OS philosophy of letting you do potentially dangerous but powerful
//! things, there's an _opt-in_ API that provides the traditional, smart-pointer
//! style interface. To use this API, you must create your mutex in a way that
//! asserts that you intend to keep its contents valid across any possible
//! cancellation point. As long as you do that, this API won't cause you any
//! problems.
//!
//! To assert this, wrap the guarded data in the [`CancelSafe`] wrapper type,
//! and write the mutex type as `Mutex<CancelSafe<T>>` instead of just
//! `Mutex<T>`. Then two new operations become available:
//! [`Mutex::lock_assuming_cancel_safe`] and
//! [`Mutex::try_lock_assuming_cancel_safe`]. These work in the traditional way
//! for more complex use cases.
//!
//! # Implementation details
//!
//! This implementation uses a wait-list to track all processes that are waiting
//! to unlock the mutex. (An OS task may contain many processes.) This makes
//! unlocking more expensive, but means that the unlock operation is *fair*,
//! preventing starvation of contending tasks.
//!
//! However, in exchange for this property, mutexes must be pinned, which makes
//! using them slightly more awkward. See the macros
//! [`create_mutex!`][crate::create_mutex] and
//! [`create_static_mutex!`][crate::create_static_mutex] for convenient
//! shorthand (or as examples of how to do it yourself).

use core::cell::UnsafeCell;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};

use pin_project_lite::pin_project;

use crate::atomic::AtomicArithExt;
use crate::exec::noop_waker;
use crate::list::List;

pin_project! {
    /// Holds a `T` that can be accessed from multiple concurrent futures/tasks,
    /// but only one at a time.
    ///
    /// This implementation is more efficient than a spin-lock, because when the
    /// mutex is contended, all competing tasks but one register themselves for
    /// waking when the mutex is freed. Thus, nobody needs to spin.
    ///
    /// When the mutex is unlocked, the task doing the unlocking will check the
    /// mutex's wait list and release the oldest task on it.
    #[derive(Debug)]
    pub struct Mutex<T: ?Sized> {
        // Stores 0 when unlocked, 1 when locked.
        state: AtomicUsize,
        // Accumulates the wakers for all tasks that have attempted to obtain this
        // mutex while it was locked.
        #[pin]
        waiters: List<()>,
        // The contents of the mutex. Safe to access only when `state` is
        // atomically flipped 0->1.
        value: UnsafeCell<T>,
    }
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
            List::finish_init(this.project().waiters);
        }
    }

    /// Attempts to lock this mutex and return an `ActionPermit` if the mutex is
    /// free, but without blocking if the mutex is not free.
    ///
    /// If the mutex is free, this returns `Some(permit)`, where `permit` is an
    /// `ActionPermit` granting the ability to perform a single synchronous
    /// action against the guarded data.
    ///
    /// If the mutex is _not_ free, returns `None`.
    ///
    /// This is the cheaper, non-blocking version of [`Mutex::lock`].
    pub fn try_lock(self: Pin<&Self>) -> Option<ActionPermit<'_, T>> {
        if self.state.fetch_or_polyfill(1, Ordering::Acquire) == 0 {
            Some(ActionPermit {
                mutex: self,
            })
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
        let p = self.project_ref();
        if p.waiters.wake_one() {
            // Someone was waiting. We will leave the state as taken to ensure
            // that no interloper can steal the mutex from the new rightful
            // owner before that owner is polled next.
        } else {
            // Nobody was waiting. Allow whoever tries next to get the mutex.
            self.state.store(0, Ordering::Release);
        }
    }

    /// Returns a future that will attempt to lock this mutex, resolving only
    /// when it succeeds. When it resolves, it will produce an `ActionPermit`,
    /// granting the ability to perform one synchronous closure to the guarded
    /// data.
    ///
    /// If the mutex is free at the time of the first `poll`, the future will
    /// resolve cheaply without blocking. Otherwise, it will join the mutex's
    /// wait-list to avoid waking its task until its turn comes up.
    ///
    /// This is the more expensive, blocking version of [`Mutex::try_lock`].
    ///
    /// # This does not return a smart pointer
    ///
    /// This operation doesn't return a "smart pointer" mutex guard that can
    /// `Deref` to `T`, because that style of API acts as a "bug generator" in
    /// async Rust code that hasn't carefully thought about cancellation. That
    /// style of API is still available with restrictions, however. See the docs
    /// on [`Mutex`] for more details.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict.
    ///
    /// Dropping the future before it resolves loses its place in line. Dropping
    /// it after the mutex is locked passes ownership to the next waiter.
    ///
    /// This API is designed to make it easy for you to implement further
    /// strict-cancel-safe operations using `Mutex`.
    pub async fn lock(self: Pin<&Self>) -> ActionPermit<'_, T> {
        // Complete synchronously if the mutex is uncontended.
        // TODO this is repeated above the loop to avoid the cost of re-setting
        // up the wait node in every loop iteration, and to avoid setting it up
        // in the uncontended case. Is this premature optimization?
        if let Some(perm) = self.try_lock() {
            return perm;
        }

        // We'd like to put our name on the wait list, please.
        create_node!(wait_node, (), noop_waker());

        let p = self.project_ref();
        p.waiters.insert_and_wait_with_cleanup(
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

        ActionPermit {
            mutex: self,
        }
    }

    unsafe fn contents(&self) -> &T {
        let ptr = self.value.get();
        unsafe { &*ptr }
    }
}

/// A token that grants the ability to run one closure against the data guarded
/// by a [`Mutex`].
///
/// This is produced by the `lock` family of operations on [`Mutex`] and is
/// intended to provide a more robust API than the traditional "smart pointer"
/// mutex guard.
#[derive(Debug)]
pub struct ActionPermit<'a, T> {
    mutex: Pin<&'a Mutex<T>>,
}

impl<T> ActionPermit<'_, T> {
    /// Runs a closure with access to the guarded data, consuming the permit in
    /// the process.
    pub fn perform<R>(self, action: impl FnOnce(&mut T) -> R) -> R {
        // Safety: we are by definition the holder of the mutex, so we can
        // use the `UnsafeCell` to access the guarded data as long as we only
        // have one such mutable reference outstanding.
        action(unsafe { &mut *self.mutex.value.get() })

        // Note: we're relying on the Drop impl for `self` to unlock the mutex.
    }
}

impl<T> Drop for ActionPermit<'_, T> {
    fn drop(&mut self) {
        // Safety: we are by definition the holder of the mutex, so we can
        // use the normally unsafe `unlock` operation to avoid repeating
        // code.
        unsafe {
            self.mutex.unlock();
        }
    }
}

impl<T> Mutex<CancelSafe<T>> {
    /// Locks this mutex immediately if it is free, and returns a guard for
    /// keeping it locked, even across `await` points -- which means you're
    /// implicitly asserting that whatever you're about to do maintains
    /// invariants across cancel points. The `Mutex` will assume you're right
    /// about that.
    ///
    /// If the mutex is _not_ free, returns `None`.
    ///
    /// This API can be error-prone, which is why it's only available if you've
    /// asserted your guarded data is `CancelSafe`. When possible, see if you
    /// can do the job using [`Mutex::try_lock`] instead.
    pub fn try_lock_assuming_cancel_safe(self: Pin<&Self>) -> Option<MutexGuard<'_, T>> {
        if self.state.fetch_or_polyfill(1, Ordering::Acquire) == 0 {
            Some(MutexGuard { mutex: self })
        } else {
            None
        }
    }

    /// Returns a future that will attempt to lock the mutex, resolving only
    /// when it succeeds. When it resolves, it will a `MutexGuard`, a "smart
    /// pointer" resource token that represents successfully locking a mutex,
    /// and grants its holder access to the guarded data -- even across an
    /// `await` point. This means by using this operation, you're asserting that
    /// what you're about to do maintains any invariants across cancel points.
    /// The `Mutex` will assume you're right about that.
    ///
    /// If the mutex is free at the time of the first `poll`, the future will
    /// resolve cheaply without blocking.
    ///
    /// # This operation is opt-in
    ///
    /// `lock_assuming_cancel_safe` is not available on mutexes unless you wrap
    /// the contents in the [`CancelSafe`] marker type. This is because the
    /// traditional Rust mutex API pattern of returning a guard can introduce
    /// surprising problems in `async` code. See the docs on [`Mutex`] about
    /// `lock` vs `lock_assuming_cancel_safe` for more details.
    ///
    /// Consider whether you can use the [`Mutex::lock`] operation instead.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict. No, really. Even with the warning above.
    ///
    /// The future returned by `lock_assuming_cancel_safe`, and the
    /// `MutexGuard` it resolves to, can both be dropped/cancelled at any time
    /// without side effect, and simply calling `lock` again works to retry. The
    /// reason this API is behind a guard rail is that that statement isn't
    /// _sufficient:_ yeah, this is technically strictly cancel-safe, but it
    /// makes it _really easy_ for you to write code on top of it that _isn't._
    /// (It would be great if cancel-safety were purely compositional, so
    /// writing a program in terms of all cancel-safe operations is
    /// automatically cancel-safe; this is not the case.) So, please read the
    /// [`Mutex`] docs carefully before deciding to use this.
    ///
    /// Cancellation behavior for the returned future is slightly subtle, but
    /// does the right thing for all cases.
    ///
    /// - If dropped before it's polled _at all_ it does essentially nothing.
    /// - If dropped once it's added itself to the wait list for the mutex, but
    ///   before it has been given the mutex, it will detach from the wait list.
    /// - If dropped after it has been given the mutex, but before it's been
    ///   polled (and thus given a chance to notice that), it will wake the next
    ///   waiter on the mutex wait list.
    pub async fn lock_assuming_cancel_safe(self: Pin<&Self>) -> MutexGuard<'_, T> {
        // Complete synchronously if the mutex is uncontended.
        // TODO this is repeated above the loop to avoid the cost of re-setting
        // up the wait node in every loop iteration, and to avoid setting it up
        // in the uncontended case. Is this premature optimization?
        if let Some(guard) = self.try_lock_assuming_cancel_safe() {
            return guard;
        }

        // We'd like to put our name on the wait list, please.
        create_node!(wait_node, (), noop_waker());

        let p = self.project_ref();
        p.waiters.insert_and_wait_with_cleanup(
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

}

/// Newtype to wrap the contents of a `Mutex` when you know, in the context of
/// the current application, that it is okay to unlock this mutex at _any_
/// cancellation point.
///
/// This is a wrapper, rather than a `trait` implemented by certain types,
/// because the property it asserts is not a property of a type at all -- it's a
/// property of _context._ For instance, consider `Mutex<Option<T>>`. One
/// application may be just fine with that mutex containing `None`, while
/// another may only remove the contents temporarily to act on it, but expect it
/// to be restored to `Some` before unlocking. Because both these use cases are
/// valid, we can't universally label `Option` as either "cancellation friendly"
/// or "not cancellation friendly," and must leave it up to the code that
/// manages the mutex itself.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Default, Ord, PartialOrd)]
pub struct CancelSafe<T>(pub T);

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
///
/// This is produced by the `lock_assuming_cancel_safe` family of operations on
/// [`Mutex`], which are only available if you opt in using the [`CancelSafe`]
/// type.
#[derive(Debug)]
pub struct MutexGuard<'a, T> {
    mutex: Pin<&'a Mutex<CancelSafe<T>>>,
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
        // Safety: this is deriving a shared reference to the contents of the
        // UnsafeCell. Because `self`, a guard, exists, we know the mutex is
        // locked. Because the caller was able to call a method on `&self`, we
        // further know that no other `&mut` references to this guard or its
        // contents exist.
        &unsafe { self.mutex.contents() }.0
    }
}

impl<T> core::ops::DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: this is deriving an exclusive reference to the contents of
        // the UnsafeCell. Because `self`, a guard, exists, we know the mutex is
        // locked. Because the caller was able to call a method on `&mut self`,
        // we further know that no other `&` or `&mut` references to this guard
        // or its contents exist.
        &mut unsafe { &mut *self.mutex.value.get() }.0
    }
}

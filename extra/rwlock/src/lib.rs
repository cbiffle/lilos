// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A [read-write lock] for use with [`lilos`].
//!
//! There's a small family of related types in this here crate:
//!
//! - [`RwLock<T>`] contains some data of type `T` and allows either multiple
//!   shared references, or one exclusive reference, but not both
//!   simultaneously.
//! - [`SharedGuard<T>`] represents a shared reference to the data guarded by a
//!   `RwLock` and allows access to it (via `Deref`).
//! - [`ActionPermit<T>`] represents an _exclusive_ reference to the data
//!   guarded by a `RwLock`, but once you start doing something that can modify
//!   the data, you can't `await`, to ensure that cancellation won't corrupt the
//!   guarded data.
//! - [`ExclusiveGuard<T>`] allows arbitrary exclusive access, even across
//!   `await` points, but you have to promise the library that the data is
//!   inherently cancel-safe (by using the [`lilos::util::CancelSafe`] marker
//!   type).
//!
//! See the docs on [`RwLock`] for more details.
//!
//! [`lilos`]: https://docs.rs/lilos/
//! [read-write lock]: https://en.wikipedia.org/wiki/Readers%E2%80%93writer_lock

#![no_std]
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

use core::cell::{Cell, UnsafeCell};
use core::ops::{Deref, DerefMut};
use core::pin::Pin;
use lilos_list::{List, Meta};
use lilos::util::CancelSafe;
use pin_project::pin_project;
use scopeguard::ScopeGuard;

/// A lock that guards data of type `T` and allows, at any one time, shared
/// access by many readers, or exclusive access by one writer, but not both.
///
/// This is similar to [`RefCell`][core::cell::RefCell], but allows programs to
/// block while waiting for access, and ensures _fairness_ among blocked
/// processes.
///
/// Fairness, in this case, means that access is granted in the order it is
/// requested.
///
/// - If the lock is currently claimed for shared access, _and_ nobody is
/// waiting for exclusive access, further attempts to lock it for shared access
/// will succeed immediately --- but an attempt to lock it for exclusive access
/// will need to wait.
///
/// - Once there is at least one exclusive access claim waiting, further
/// shared access claims (and additional exclusive access claims) now have to
/// wait behind it.
///
/// - Once all outstanding shared access claims are released, the first
/// exclusive access claim in the wait queue is granted.
///
/// - Once _that_ gets released, the next claim(s) in the queue are granted -- a
/// single exclusive claim, or any number of (consecutive) shared claims.
///
///
/// # Getting an `RwLock`
///
/// `RwLock` needs to be pinned to be useful, so you'll generally write:
///
/// ```
/// let my_lock = pin!(RwLock::new(initial_data_here()));
/// // Drop &mut:
/// let my_lock = my_lock.into_ref();
///
/// let guard = my_lock.lock_shared().await;
/// guard.do_stuff();
/// ```
///
/// There is also the [`create_rwlock!`] macro that wraps up those first two
/// lines, if you prefer.
///
///
/// # Using the guarded data
///
/// [`RwLock::lock_shared`] places a _shared claim_ on the data, and returns a
/// future that will resolve when that claim can be granted. That produces a
/// [`SharedGuard`] that allows shared (`&` reference) access to the `T`
/// contained in the `RwLock`. (The non-blocking equivalent is
/// [`RwLock::try_lock_shared`].)
///
/// [`RwLock::lock_exclusive`] places an _exclusive claim_ on the data, and
/// returns a future that will resolve when that claim can be granted. That
/// produces an [`ActionPermit`] that allows exclusive (`&mut` reference) access
/// to the `T` --- but without the ability to `await`. See
/// [`ActionPermit::perform`] for information on how this works. (The
/// non-blocking equivalent is [`RwLock::try_lock_exclusive`].
///
/// In general, holding a `&mut` to guarded data across `await` points means
/// that there's a risk your future will be cancelled and leave the guarded data
/// in an invalid state. (This problem exists with all async Mutex-like data
/// structures in Rust.) You can still do it, as long as you're very careful not
/// to `await` while the guarded data is in an unacceptable state.
///
/// To do this, you wrap the data in a [`CancelSafe`][lilos::util::CancelSafe]
/// wrapper, which causes [`RwLock::lock_exclusive_assuming_cancel_safe`] to
/// become available. This returns an [`ExclusiveGuard`] which acts like the
/// mutex guards in `std`.
#[derive(Debug)]
#[pin_project]
pub struct RwLock<T> {
    #[pin]
    lock: LockImpl,
    contents: UnsafeCell<T>,
}

impl<T> RwLock<T> {
    /// Creates a future that will resolve when it successfully locks `self` for
    /// shared access. Until then, the future will remain pending (i.e. block).
    ///
    /// Shared access can be obtained when no other code currently has exclusive
    /// access, or is waiting for exclusive access.
    ///
    /// # Cancellation
    ///
    /// Cancel-safe but affects your position in line, to maintain fairness.
    ///
    /// If you drop the returned future before it resolves...
    /// - If it had not successfully locked, nothing happens.
    /// - If it had, the lock is released.
    ///
    /// Dropping the future and re-calling `lock_shared` bumps the caller to the
    /// back of the priority list, to maintain fairness. Otherwise, the result
    /// is indistinguishable.
    pub async fn lock_shared(self: Pin<&Self>) -> SharedGuard<'_, T> {
        let lock = self.project_ref().lock.lock_shared().await;
        SharedGuard {
            _lock: lock,
            contents: unsafe { &*self.contents.get() },
        }
    }

    /// Attempts to lock `self` for shared access.
    ///
    /// This will succeed if there are either no other claims on the lock, or if
    /// there are any number of shared claims. In this case, it will return
    /// `Ok(guard)`, where `guard` allows shared access to the guarded data.
    ///
    /// If there is an outstanding exclusive claim on the lock, this will fail
    /// with `Err(InUse)`.
    pub fn try_lock_shared(
        self: Pin<&Self>,
    ) -> Result<SharedGuard<'_, T>, InUse> {
        let lock = self.project_ref().lock.try_lock_shared()?;
        Ok(SharedGuard {
            _lock: lock,
            contents: unsafe { &*self.contents.get() },
        })
    }

    /// Creates a future that will resolve when it successfully locks `self` for
    /// exclusive access. Until then, the future will remain pending (i.e.
    /// block).
    ///
    /// Exclusive access can be obtained when other code currently has neither
    /// shared nor exclusive access.
    ///
    /// This returns an [`ActionPermit`] that lets you perform non-`async`
    /// actions on the guarded data. If you need a version that can be held
    /// across an `await` point, and you've read and understood the caveats
    /// described on the [`CancelSafe`] type, then have a look at
    /// [`Self::lock_exclusive_assuming_cancel_safe`].
    ///
    /// # Cancellation
    ///
    /// Cancel-safe but affects your position in line, to maintain fairness.
    ///
    /// If you drop the returned future before it resolves...
    /// - If it had not successfully locked, nothing happens.
    /// - If it had, the lock is released.
    ///
    /// Dropping the future and re-calling `lock_exclusive` bumps the caller to
    /// the back of the priority list, to maintain fairness. Otherwise, the
    /// result is indistinguishable.
    pub async fn lock_exclusive(self: Pin<&Self>) -> ActionPermit<'_, T> {
        let lock = self.project_ref().lock.lock_exclusive().await;
        ActionPermit {
            _lock: lock,
            contents: unsafe { &mut *self.contents.get() },
        }
    }

    /// Attempts to lock `self` for exclusive access.
    ///
    /// This will succeed if there are no other claims on the lock of any kind.
    /// In this case, it will return `Ok(permit)`, where `permit` is an
    /// [`ActionPermit`] allowing you to take non-`async` actions on the guarded
    /// data.
    ///
    /// If there is an outstanding exclusive claim on the lock, this will fail
    /// with `Err(InUse)`.
    ///
    /// If you need an exclusive lock that can be held across `await` points,
    /// and you have read and understand the caveats described on the
    /// [`CancelSafe`] type, then have a look at
    /// [`Self::try_lock_exclusive_assuming_cancel_safe`].
    pub fn try_lock_exclusive(
        self: Pin<&Self>,
    ) -> Result<ActionPermit<'_, T>, InUse> {
        let lock = self.project_ref().lock.try_lock_exclusive()?;
        Ok(ActionPermit {
            _lock: lock,
            contents: unsafe { &mut *self.contents.get() },
        })
    }

    /// Returns an `RwLock` containing `contents`.
    ///
    /// The result needs to be pinned to be useful, so you'll generally write:
    ///
    /// ```
    /// let my_rwlock = pin!(RwLock::new(contents));
    /// let my_rwlock = my_rwlock.into_ref();
    /// ```
    pub const fn new(contents: T) -> Self {
        // The Access value chosen here doesn't matter.
        Self {
            lock: LockImpl {
                readers: Cell::new(0),
                waiters: List::new(),
            },
            contents: UnsafeCell::new(contents),
        }
    }
}

#[derive(Debug)]
#[pin_project]
struct LockImpl {
    readers: Cell<isize>,
    #[pin]
    waiters: List<Meta<Access>>,
}

impl LockImpl {
    async fn lock_shared(self: Pin<&Self>) -> SharedInternal<'_> {
        // Fast path:
        if let Ok(guard) = self.try_lock_shared() {
            return guard;
        }

        // Add ourselves to the wait list. Unlike many synchronization
        // primitives, we have no need to register a cleanup action here,
        // because simply getting evicted from the wait list doesn't grant us
        // any access we'd need to give up -- that's handled below.
        self.project_ref()
            .waiters
            .join_with_cleanup(Meta(Access::Shared), || {
                // The release routine advances the reader count _for us_ so
                // that our access is assured even if we're not promptly polled.
                // This means we have to reverse that change if we're cancelled.
                unsafe {
                    self.release_shared();
                }
            })
            .await;

        // Having been detached from the list means that we are among the
        // observers who have been granted shared access -- otherwise we'd be
        // left in the queue.
        SharedInternal { lock: self }
    }

    fn try_lock_shared(self: Pin<&Self>) -> Result<SharedInternal<'_>, InUse> {
        // Interestingly, this next check appears to be the entire difference
        // between a writer-biased and a reader-biased lock. Are reader-biased
        // locks a thing people need? If so this could be configurable...
        if !self.waiters.is_empty() {
            // If there's anything on the list, we can't lock it right now.
            return Err(InUse);
        }

        let r = self.readers.get();
        if (0..isize::MAX).contains(&r) {
            self.readers.set(r + 1);
            Ok(SharedInternal { lock: self })
        } else {
            Err(InUse)
        }
    }

    fn process_exclusive_cancellation(self: Pin<&Self>) {
        if self.readers.get() >= 0 {
            // Wake any number of pending _shared_ users and record their
            // count, to keep them from getting scooped before they're
            // polled.
            self.project_ref().waiters.wake_while(|Meta(access)| {
                if access == &Access::Shared {
                    let r = self.readers.get();
                    // We do not want to overflow the reader count during this
                    // wake-frenzy.
                    if r < isize::MAX {
                        self.readers.set(self.readers.get() + 1);
                        return true;
                    }
                }
                false
            });
        }
    }

    async fn lock_exclusive(self: Pin<&Self>) -> ExclusiveInternal<'_> {
        // Fast path...
        if let Ok(permit) = self.try_lock_exclusive() {
            return permit;
        }

        // Cancellation behavior here is slightly subtle because we can have
        // effects even _before_ we're detached, by blocking processing of a
        // sequence of shared waiters. So we set a trap: on drop, we will invoke
        // the `process_exclusive_cancellation` hook to restore the invariant
        // that any sequence of shared claims is coalesced.
        //
        // We do not need to do this if we get detached. So, we disarm the trap
        // on detach. Because we can't actually run code on detach, we're
        // instead exploiting the cleanup hook to cover the two cases:
        //
        // 1. Detached, but then dropped before polling.
        // 2. Detached, and then polled.
        //
        //
        let mut trap = Some(scopeguard::guard((), |_| {
            self.process_exclusive_cancellation();
        }));

        self.project_ref()
            .waiters
            .join_with_cleanup(Meta(Access::Exclusive), || {
                // Disarm the trap.
                ScopeGuard::into_inner(trap.take().unwrap());
                // The release routine decrements the reader count _for us_ so
                // that our access is assured even if we're not promptly polled.
                // This means we have to reverse that change if we're cancelled.
                unsafe {
                    self.release_exclusive();
                }
            })
            .await;
        // Disarm the trap.
        ScopeGuard::into_inner(trap.take().unwrap());

        // The fact that we have been detached means that we have exclusive
        // control.
        ExclusiveInternal { lock: self }
    }

    fn try_lock_exclusive(
        self: Pin<&Self>,
    ) -> Result<ExclusiveInternal<'_>, InUse> {
        let r = self.readers.get();
        if r == 0 {
            self.readers.set(-1);
            Ok(ExclusiveInternal { lock: self })
        } else {
            Err(InUse)
        }
    }

    // # Safety
    //
    // Must only be called in contexts where one previously obtained shared
    // access permit is being retired. Use in any other context may cause the
    // lock to grant exclusive access to another observer, resulting in
    // aliasing.
    unsafe fn release_exclusive(self: Pin<&Self>) {
        let prev = self.readers.get();
        debug_assert!(
            prev < 0,
            "release_exclusive used with no exclusive lock outstanding"
        );
        self.readers.set(prev + 1);

        if prev == -1 {
            // We are the last exclusive lock being released. (Yes, there can be
            // more than one exclusive lock because of map_split.)

            let p = self.project_ref();

            // Wake a _single_ exclusive lock attempt if one exists at the head
            // of the queue.
            if p.waiters.wake_head_if(|Meta(access)| access == &Access::Exclusive) {
                // Record it, to keep it from getting scooped.
                self.readers.set(-1);
            } else {
                // Wake any number of pending _shared_ users and record their
                // count, to keep them from getting scooped before they're
                // polled.
                p.waiters.wake_while(|Meta(access)| {
                    if access == &Access::Shared {
                        let r = self.readers.get();
                        // We do not want to overflow the reader count during this
                        // wake-frenzy.
                        if r < isize::MAX {
                            self.readers.set(self.readers.get() + 1);
                            return true;
                        }
                    }
                    false
                });
            }
        }
    }

    // # Safety
    //
    // Must only be called in contexts where one previously obtained shared
    // access permit is being retired. Use in any other context may cause the
    // lock to grant exclusive access to another observer, resulting in
    // aliasing.
    unsafe fn release_shared(self: Pin<&Self>) {
        let prev = self.readers.get();
        debug_assert!(
            prev > 0,
            "release_shared used with no shared lock outstanding"
        );
        self.readers.set(prev - 1);
        match prev {
            1 => {
                // It's our job to try and wake a writer, if one exists. (The list
                // should, at this point, either be empty or contain a single
                // exclusive access plus an arbitrary list.)
                if self
                    .project_ref()
                    .waiters
                    .wake_head_if(|Meta(access)| access == &Access::Exclusive)
                {
                    // Found one. Record its count to ensure that nobody scoops it
                    // before it gets polled.
                    self.readers.set(-1);
                }
            }
            isize::MAX => {
                // We somehow filled up the reader count, so it's our job to
                // attempt to wake a _reader,_ weirdly.
                if self
                    .project_ref()
                    .waiters
                    .wake_head_if(|Meta(access)| access == &Access::Shared)
                {
                    // Set the count back to saturated.
                    self.readers.set(isize::MAX);
                }
            }
            _ => (),
        }
    }
}

/// Internal type for marking the sort of access a node is after.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum Access {
    /// An observer who wants shared access.
    Shared,
    /// An observer who wants exclusive access.
    Exclusive,
}

#[derive(Debug)]
struct SharedInternal<'a> {
    lock: Pin<&'a LockImpl>,
}

impl Clone for SharedInternal<'_> {
    fn clone(&self) -> Self {
        let prev = self.lock.readers.get();
        if prev == isize::MAX {
            panic!();
        }
        self.lock.readers.set(prev + 1);
        Self { lock: self.lock }
    }
}

impl Drop for SharedInternal<'_> {
    fn drop(&mut self) {
        unsafe {
            self.lock.release_shared();
        }
    }
}

/// Resource object that grants shared access to guarded data of type `T`.
#[derive(Debug)]
#[must_use = "simply dropping SharedGuard unlocks the RwLock immediately"]
pub struct SharedGuard<'a, T: ?Sized> {
    _lock: SharedInternal<'a>,
    contents: &'a T,
}

impl<'a, T> SharedGuard<'a, T>
where
    T: ?Sized,
{
    /// Converts a `SharedGuard<T>` into a `SharedGuard<U>` by applying a
    /// projection function to select a sub-component of the guarded data.
    ///
    /// The `SharedGuard<U>` this produces will keep the whole `T` locked for
    /// shared access, but won't be able to access anything but the chosen
    /// sub-component `U`.
    ///
    /// By transforming an existing reader, this leaves the reader count
    /// unchanged.
    pub fn map<U>(guard: Self, f: impl FnOnce(&T) -> &U) -> SharedGuard<'a, U>
    where
        U: ?Sized,
    {
        SharedGuard {
            _lock: guard._lock,
            contents: f(guard.contents),
        }
    }

    /// Converts a `SharedGuard<T>` into a pair `SharedGuard<U>` and
    /// `SharedGuard<V>` by applying a projection function to select two
    /// sub-components of the guarded data.
    ///
    /// Both of the returned guards will keep the whole `T` locked for shared
    /// access, but won't be able to access access anything but the chosen
    /// sub-components `U` and `V` (respectively).
    ///
    /// This increases the total reader count of the lock by 1.
    ///
    /// # Panics
    ///
    /// There is a maximum number of supported readers on a lock, which is at
    /// least `usize::MAX/2`. This number is very difficult to reach in
    /// non-pathological code. However, if you reach it by splitting a reader,
    /// this will panic.
    pub fn map_split<U, V>(
        guard: Self,
        f: impl FnOnce(&T) -> (&U, &V),
    ) -> (SharedGuard<'a, U>, SharedGuard<'a, V>)
    where
        U: ?Sized,
        V: ?Sized,
    {
        let (u, v) = f(guard.contents);
        (
            SharedGuard {
                _lock: guard._lock.clone(),
                contents: u,
            },
            SharedGuard {
                _lock: guard._lock,
                contents: v,
            },
        )
    }
}

impl<T> Deref for SharedGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.contents
    }
}

/// Error produced by [`RwLock::try_lock_shared`] and related non-blocking
/// locking operations.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct InUse;

/// Internal implementation of both `ActionPermit` and `ExclusiveGuard`,
/// ensuring that we only need one copy of the `Drop` impl and contents
/// accessors, and that `ActionPermit` can be conveniently destructured to turn
/// it into an `ExclusiveGuard`. (Since having a `Drop` impl would otherwise
/// prevent this.)
#[derive(Debug)]
#[must_use = "internal implementation issue"]
struct ExclusiveInternal<'a> {
    lock: Pin<&'a LockImpl>,
}

impl Clone for ExclusiveInternal<'_> {
    fn clone(&self) -> Self {
        let prev = self.lock.readers.get();
        if prev == isize::MIN {
            panic!();
        }
        self.lock.readers.set(prev - 1);
        Self { lock: self.lock }
    }
}

impl Drop for ExclusiveInternal<'_> {
    fn drop(&mut self) {
        // Safety: because we exist, we know the lock is locked-exclusive, and
        // that no other code thinks _they_ have locked it exclusive, so we can
        // use release_exclusive trivially.
        unsafe {
            self.lock.release_exclusive();
        }
    }
}

/// Permit returned by [`RwLock::lock_exclusive`] or
/// [`RwLock::try_lock_exclusive`] that indicates that the holder has exclusive
/// access to the lock, and that permits non-`async` alterations to the guarded
/// data.
///
/// See [`ActionPermit::perform`].
#[derive(Debug)]
#[must_use = "simply dropping ActionPermit unlocks the RwLock immediately"]
pub struct ActionPermit<'a, T> {
    _lock: ExclusiveInternal<'a>,
    contents: &'a mut T,
}

impl<'a, T> ActionPermit<'a, T> {
    /// Run `action` with access to the guarded data.
    ///
    /// This function takes a closure to ensure that the code can't `await`.
    /// This means the code in `action` can break invariants in `T` as long as
    /// it restores them before returning, without risk of cancellation.
    pub fn perform<R>(self, action: impl FnOnce(&mut T) -> R) -> R {
        let Self { _lock, contents } = self;
        action(contents)

        // Note: we're relying on the Drop impl for _lock to unlock.
    }

    /// Get a shared reference to the guarded data.
    ///
    /// This makes an `ActionPermit` behave like an awkward and expensive
    /// [`SharedGuard`], but this may be useful for code that wants to check
    /// properties of the data before committing with [`ActionPermit::perform`].
    pub fn inspect(&self) -> &T {
        self.contents
    }

    /// Converts an `ActionPermit<T>` into an `ActionPermit<U>` using a
    /// projection function to select a sub-component of `T`.
    ///
    /// `projection` selects a part of `T` and returns an exclusive reference to
    /// it. By applying `map`, you give up the ability to use this
    /// `ActionPermit` to affect parts of `T` outside the returned sub-component
    /// `U`.
    ///
    /// By transforming an existing writer, this leaves the writer count of the
    /// lock unchanged.
    pub fn map<U>(
        self,
        projection: impl FnOnce(&mut T) -> &mut U,
    ) -> ActionPermit<'a, U> {
        let Self { _lock, contents } = self;
        ActionPermit {
            _lock,
            contents: projection(contents),
        }
    }

    /// Converts an `ActionPermit<T>` into a pair `ActionPermit<U>` and
    /// `ActionPermit<V>` using a projection function to select two
    /// non-overlapping sub-components of `T`.
    ///
    /// This increases the writer count of the lock by 1; writers still have
    /// exclusive access because they don't overlap.
    ///
    /// # Panics
    ///
    /// There is a maximum writer count on the lock, which is at least
    /// `usize::MAX/2`. It's difficult to reach it in non-pathological code.
    /// However, if you do manage to reach it by splitting, this will panic.
    pub fn map_split<U, V>(
        self,
        split: impl FnOnce(&mut T) -> (&mut U, &mut V),
    ) -> (ActionPermit<'a, U>, ActionPermit<'a, V>) {
        let Self { _lock, contents } = self;
        let (u, v) = split(contents);
        (
            ActionPermit {
                _lock: _lock.clone(),
                contents: u,
            },
            ActionPermit { _lock, contents: v },
        )
    }
}

impl<T> RwLock<CancelSafe<T>> {
    /// Attempts to lock `self` for exclusive access, succeeding if there are no
    /// other claims on `self`.
    ///
    /// On success, this returns `Ok(guard)`, where `guard` allows direct access
    /// to the guarded data. The `guard` can be held across `await` points,
    /// which are also potential cancellation points. This means it's not safe
    /// to use `guard` to break any invariants in `T` unless you're careful to
    /// restore them before an `await` --- the compiler will not help you with
    /// this.
    ///
    /// On error, this returns `Err(InUse)`.
    ///
    /// See the docs on [`CancelSafe`] for more information.
    pub fn try_lock_exclusive_assuming_cancel_safe(
        self: Pin<&Self>,
    ) -> Result<ExclusiveGuard<'_, T>, InUse> {
        let ActionPermit { _lock, contents } = self.try_lock_exclusive()?;
        Ok(ExclusiveGuard {
            _lock,
            contents: &mut contents.0,
        })
    }

    /// Returns a future that resolves once it is able to lock `self` for
    /// exclusive access.
    ///
    /// On success, this returns a `guard` which allows direct access to the
    /// guarded data. The `guard` can be held across `await` points, which are
    /// also potential cancellation points. This means it's not safe to use
    /// `guard` to break any invariants in `T` unless you're careful to restore
    /// them before an `await` --- the compiler will not help you with this.
    ///
    /// See the docs on [`CancelSafe`] for more information.
    pub async fn lock_exclusive_assuming_cancel_safe(
        self: Pin<&Self>,
    ) -> ExclusiveGuard<'_, T> {
        let ActionPermit {
            _lock: lock,
            contents,
        } = self.lock_exclusive().await;
        ExclusiveGuard {
            _lock: lock,
            contents: &mut contents.0,
        }
    }
}

/// A resource object that grants read/write access to the data guarded by an
/// [`RwLock`].
///
/// Read/write access means you can arbitrarily break invariants in the guarded
/// data, even in safe Rust. As a result, this is only available for locks that
/// explicitly use the wrapper type [`CancelSafe`], e.g.
/// `RwLock<CancelSafe<MyStruct>>`. See the docs on `CancelSafe` for more
/// details.
#[derive(Debug)]
pub struct ExclusiveGuard<'a, T> {
    _lock: ExclusiveInternal<'a>,
    contents: &'a mut T,
}

impl<'a, T> ExclusiveGuard<'a, T> {
    /// Converts an `ExclusiveGuard<T>` into an `ExclusiveGuard<U>` using a
    /// projection function to select a sub-component of `T`.
    ///
    /// `projection` selects a part of `T` and returns an exclusive reference to
    /// it. By applying `map`, you give up the ability to use this
    /// `ExclusiveGuard` to affect parts of `T` outside the returned
    /// sub-component `U`.
    ///
    /// The returned guard keeps the entire `T` locked for exclusive access.
    pub fn map<U>(
        self,
        projection: impl FnOnce(&mut T) -> &mut U,
    ) -> ExclusiveGuard<'a, U> {
        let Self { _lock, contents } = self;
        ExclusiveGuard {
            _lock,
            contents: projection(contents),
        }
    }

    /// Converts an `ExclusiveGuard<T>` into a pair `ExclusiveGuard<U>` and
    /// `ExclusiveGuard<V>` using a projection function to select two
    /// non-overlapping sub-components of `T`.
    ///
    /// # Panics
    ///
    /// There is a maximum writer count on the lock, which is at least
    /// `usize::MAX/2`. It's difficult to reach it in non-pathological code.
    /// However, if you do manage to reach it by splitting, this will panic.
    pub fn map_split<U, V>(
        self,
        split: impl FnOnce(&mut T) -> (&mut U, &mut V),
    ) -> (ExclusiveGuard<'a, U>, ExclusiveGuard<'a, V>) {
        let Self { _lock, contents } = self;
        let (u, v) = split(contents);
        (
            ExclusiveGuard {
                _lock: _lock.clone(),
                contents: u,
            },
            ExclusiveGuard { _lock, contents: v },
        )
    }
}

impl<T> Deref for ExclusiveGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.contents
    }
}

impl<T> DerefMut for ExclusiveGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.contents
    }
}

/// Convenience macro for creating an [`RwLock`].
#[macro_export]
macro_rules! create_rwlock {
    ($var:ident, $contents:expr) => {
        let $var = core::pin::pin!($crate::RwLock::new($contents));
        let $var = $var.into_ref();
    };
}

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A [counting semaphore] for use with [`lilos`].
//!
//! See the docs on [`Semaphore`] for more details.
//!
//! [`lilos`]: https://docs.rs/lilos/
//! [counting semaphore]: https://en.wikipedia.org/wiki/Semaphore_(programming)

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

use core::pin::Pin;
use portable_atomic::{AtomicUsize, Ordering};
use lilos_list::List;
use pin_project::pin_project;

/// A [counting semaphore].
///
/// A `Semaphore` gets initialized with a certain number of _permits._
/// Callers can take one permit from the semaphore using the
/// [`Semaphore::acquire`] operation, which will block if there are none
/// available, and wake when one becomes available.
///
/// Permits can be added back to the semaphore one at a time using the
/// [`Semaphore::release`] operation, or in batches using
/// [`Semaphore::release_multiple`].
///
/// Semaphores are useful for restricting concurrent access to something,
/// particularly in cases where you don't want to restrict it to exactly one
/// observer (like with a `Mutex`). Two common use cases are:
///
/// - To ensure that no more than `N` tasks can make it into a critical section
/// simultaneously, you'd create a `Semaphore` with `N` permits. Each task would
/// `acquire` a permit to gain entry, and then `release` it at the end. In this
/// case, a "permit object" might be fine, because `acquire` and `release` are
/// both being called in the same context.
///
/// - To represent data being generated or received (perhaps over a network),
/// you'd create a `Semaphore` with 0 permits. Tasks interested in consuming
/// resources would attempt to `acquire` and block; as data becomes available,
/// the generating task would `release` permits, potentially in batches, to
/// unblock the consumers. In this case, `release` and `acquire` are happening
/// in totally different contexts.
///
/// To support _both_ these uses, the `Semaphore` API is different from a lot of
/// Rust concurrency APIs, and does not return a "permit object" that represents
/// a permit until dropped. If your use case is closer to the first example, and
/// you would like the convenience of a permit object managing calls to
/// `release` for you, have a look at [`ScopedSemaphore`], a thin wrapper that
/// provides a [`Permit`].
///
///
/// # Getting a semaphore
///
/// Like `lilos`'s `Mutex` type, `Semaphore` must be pinned to be useful. So
/// generally you'll wind up writing something like this:
///
/// ```
/// let scooters = pin!(Semaphore::new(5));
/// // Drop &mut:
/// let scooters = scooters.into_ref();
///
/// // Check out one scooter from the pool.
/// scooters.acquire().await;
/// ```
///
/// This crate includes a convenience macro, [`create_semaphore!`], that
/// basically just wraps up the first two lines:
///
/// ```
/// lilos_semaphore::create_semaphore!(scooters, 5);
///
/// // Check out one scooter from the pool.
/// scooters.acquire().await;
/// ```
///
///
/// # Fairness
///
/// This semaphore implementation is _fair,_ which in this context means
/// that permits are handed out in the order they're requested. If the
/// semaphore runs out of permits, tasks requesting permits are queued in
/// order and will be issued permits in order as they are returned to the
/// semaphore.
///
/// [counting semaphore]: https://en.wikipedia.org/wiki/Semaphore_(programming)
#[derive(Debug)]
#[pin_project]
pub struct Semaphore {
    available: AtomicUsize,
    #[pin]
    waiters: List<()>,
}

impl Semaphore {
    /// Creates a future that will resolve when it can take a single permit from
    /// the semaphore. Until then, the future will remain pending (i.e. block).
    ///
    /// # Cancellation
    ///
    /// Cancel-safe but affects your position in line, to maintain fairness.
    ///
    /// If you drop the returned future before it resolves...
    /// - If it had not successfully acquired a permit, nothing happens.
    /// - If it had, the permit is released.
    ///
    /// Dropping the future and re-calling `acquire` bumps the caller to the
    /// back of the priority list, to maintain fairness. Otherwise, the result
    /// is indistinguishable.
    pub async fn acquire(self: Pin<&Self>) {
        if self.try_acquire().is_ok() {
            return;
        }

        // Add ourselves to the wait list...
        self.project_ref()
            .waiters
            .join_with_cleanup((), || {
                // This is called when we've been detached from the wait
                // list, which means a permit was transferred to us, but
                // we haven't been polled -- and won't ever be polled,
                // for we are being dropped. This means we need to
                // release our permit, which might wake another task.
                self.release();
            })
            .await
    }

    /// Attempts to take a single permit from the semaphore, returning `Ok` if
    /// one is available immediately, or `Err` if they are all taken.
    pub fn try_acquire(&self) -> Result<(), NoPermits> {
        self.available
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |a| {
                a.checked_sub(1)
            })
            .map_err(|_| NoPermits)?;
        Ok(())
    }

    /// Returns the number of permits available in the semaphore.
    ///
    /// Note that this is a _snapshot._ If this returns 4, for instance, it
    /// doesn't mean you can successfully call `acquire` 4 times without
    /// blocking, because another acquirer may be racing you.
    pub fn permits_available(&self) -> usize {
        self.available.load(Ordering::Relaxed)
    }

    /// Stuffs one permit back into the semaphore.
    #[inline(always)]
    pub fn release(self: Pin<&Self>) {
        self.release_multiple(1)
    }

    /// Stuffs one permit back into the semaphore.
    ///
    /// Use this if you have called [`core::mem::forget`] on a [`Permit`], when
    /// you want to restore that permit to the semaphore. Note that this is an
    /// unusual use case and should only be done with good reason.
    ///
    /// It is, however, safe, in the Rust sense.
    ///
    /// It's possible to use this operation to increase the total number of
    /// permits available in the `Semaphore`. That's an even weirder use case,
    /// so be careful.
    pub fn release_multiple(self: Pin<&Self>, mut n: usize) {
        debug_assert!(n > 0);

        let p = self.project_ref();
        while n > 0 {
            if !p.waiters.wake_one() {
                // We have exhausted the list, stop using this strategy.
                break;
            }
            n -= 1;
        }

        if n > 0 {
            // Since we're not yielding -- we're not even in an async fn! -- the
            // only thing concurrent with us is ISRs, which can only wake tasks,
            // not insert them.
            //
            // So the fact that the waiters list was found empty cannot change
            // during this loop.
            self.available
                .fetch_update(
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                    // Note that this has a potential overflow on addition. This is
                    // deliberate, and is why we're not using fetch_add here!
                    |a| Some(a + n),
                )
                .unwrap();
        }
    }

    /// Returns an `Semaphore` initialized with `permits` permits.
    ///
    /// The result needs to be pinned to be useful, so you'll usually write:
    ///
    /// ```
    /// let semaphore = pin!(Semaphore::new(permit_count));
    /// let semaphore = semaphore.into_ref();
    /// ```
    ///
    /// See also the convenience macro [`create_semaphore!`].
    pub const fn new(permits: usize) -> Self {
        Semaphore {
            available: AtomicUsize::new(permits),
            waiters: List::new(),
        }
    }
}

/// Error produced by [`Semaphore::try_acquire`] when no permits were available.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct NoPermits;

/// Convenience macro for creating a [`Semaphore`] on the stack.
///
/// `create_semaphore!(ident, num_permits)` creates a semaphore that initially
/// contains `num_permits` permits, and assigns it to a local variable called
/// `ident`. `ident` will have the type `Pin<&Semaphore>`.
///
/// Yes, it's weird that this macro creates a local variable, but there's no
/// good way around it in current Rust. You can, of course, write the
/// initialization code yourself if you'd prefer --- see the macro source code
/// for details.
#[macro_export]
macro_rules! create_semaphore {
    ($var:ident, $permits:expr) => {
        let $var = core::pin::pin!($crate::Semaphore::new($permits));
        let $var = $var.into_ref();
    };
}

/// A [counting semaphore] that uses resource objects to manage permits,
/// eliminating the need to explicitly call `release` in certain kinds of use
/// cases.
///
/// A `ScopedSemaphore` is almost identical to a [`Semaphore`], but any time a
/// permit is successfully acquired from a `ScopedSemaphore`, it produces a
/// [`Permit`] object that represents the lifetime of that permit. When the
/// `Permit` is dropped, it will be automatically returned to the
/// `ScopedSemaphore`. This makes the API closer to a traditional Rust mutex
/// API, but only works in cases where the permits are being acquired and
/// released in the same context.
///
/// See [`Semaphore`] for background and information about fairness.
///
/// [counting semaphore]: https://en.wikipedia.org/wiki/Semaphore_(programming)
#[derive(Debug)]
#[pin_project]
pub struct ScopedSemaphore {
    #[pin]
    inner: Semaphore,
}

impl ScopedSemaphore {
    /// Creates a future that will resolve when it can take a single [`Permit`]
    /// from the semaphore. Until then, the future will remain pending (i.e.
    /// block).
    ///
    /// # Cancellation
    ///
    /// Cancel-safe but affects your position in line, to maintain fairness.
    ///
    /// If you drop the returned future before it resolves...
    /// - If it had not successfully acquired a permit, nothing happens.
    /// - If it had, the permit is released.
    ///
    /// Dropping the future and re-calling `acquire` bumps the caller to the
    /// back of the priority list, to maintain fairness. Otherwise, the result
    /// is indistinguishable.
    pub async fn acquire(self: Pin<&Self>) -> Permit<'_> {
        self.project_ref().inner.acquire().await;

        Permit { semaphore: self }
    }

    /// Attempts to take a single [`Permit`] from the semaphore, returning
    /// `Ok(permit)` on success, or `Err` if they are all taken.
    pub fn try_acquire(self: Pin<&Self>) -> Result<Permit<'_>, NoPermits> {
        self.inner.try_acquire()?;
        Ok(Permit { semaphore: self })
    }

    /// Returns the number of permits available in the semaphore.
    ///
    /// Note that this is a _snapshot._ If this returns 4, for instance, it
    /// doesn't mean you can successfully call `acquire` 4 times without
    /// blocking, because another acquirer may be racing you.
    pub fn permits_available(&self) -> usize {
        self.inner.permits_available()
    }

    /// Stuffs `n` permits back into the semaphore.
    ///
    /// This operation is useful for either increasing the number of permits
    /// available in an existing semaphore, or restoring permits that were
    /// hidden from the compiler's view by calling [`core::mem::forget`] on a
    /// [`Permit`].
    ///
    /// If you find yourself using this operation regularly, it may be a sign
    /// that you want a plain old [`Semaphore`] instead of a `ScopedSemaphore`.
    pub fn out_of_band_release(self: Pin<&Self>, n: usize) {
        self.project_ref().inner.release_multiple(n);
    }

    /// Returns a `ScopedSemaphore` that initially contains `permits` permits.
    ///
    /// The result needs to be pinned to be useful, so you'll usually write:
    ///
    /// ```
    /// let semaphore = pin!(ScopedSemaphore::new(permit_count));
    /// let semaphore = semaphore.into_ref();
    /// ```
    ///
    /// See also the convenience macro [`create_scoped_semaphore!`].
    pub const fn new(permits: usize) -> Self {
        Self {
            inner: Semaphore::new(permits),
        }
    }
}

/// A resource object representing one permit acquired from a
/// [`ScopedSemaphore`].
///
/// When dropped, this will return one permit to its originating semaphore.
#[derive(Debug)]
#[must_use = "dropping the permit will immediately release it"]
pub struct Permit<'a> {
    semaphore: Pin<&'a ScopedSemaphore>,
}

impl Drop for Permit<'_> {
    fn drop(&mut self) {
        self.semaphore.out_of_band_release(1)
    }
}

/// Convenience macro for creating a [`ScopedSemaphore`] on the stack.
///
/// `create_scoped_semaphore!(ident, num_permits)` creates a semaphore that
/// initially contains `num_permits` permits, and assigns it to a local variable
/// called `ident`. `ident` will have the type `Pin<&ScopedSemaphore>`.
///
/// Yes, it's weird that this macro creates a local variable, but there's no
/// good way around it in current Rust. You can, of course, write the
/// initialization code yourself if you'd prefer --- see the macro source code
/// for details.
#[macro_export]
macro_rules! create_scoped_semaphore {
    ($var:ident, $permits:expr) => {
        let $var = core::pin::pin!($crate::ScopedSemaphore::new($permits));
        let $var = $var.into_ref();
    };
}

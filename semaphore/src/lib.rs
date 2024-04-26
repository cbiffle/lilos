//! A counting semaphore for use with [`lilos`].
//!
//! See the docs on [`Semaphore`] for more details.
//!
//! [`lilos`]: https://docs.rs/lilos/

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

use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, Ordering};
use lilos::atomic::AtomicExt;
use lilos::create_node;
use lilos::exec::noop_waker;
use lilos::list::List;
use pin_project_lite::pin_project;

pin_project! {
    /// A counting semaphore.
    ///
    /// A `Semaphore` gets initialized with a certain number of _permits._
    /// Callers can take one permit from the semaphore using the `acquire`
    /// operation, which will block if there are none available, and wake when
    /// one becomes available.
    ///
    /// `acquire` returns a `Permit`, which is a resource object that represents
    /// holding one permit. When it is dropped, it restores its permit back to
    /// the `Semaphore`, potentially waking a blocked caller.
    ///
    /// Semaphores are useful for restricting concurrent access to something.
    ///
    /// # Getting a semaphore
    ///
    /// Like `lilos`'s `Mutex` type, `Semaphore` must be pinned to be useful.
    /// This crate includes a convenience macro, [`create_semaphore!`], to make
    /// this easy. Like `create_mutex!`, `create_semaphore!` makes a named
    /// variable as if you had used `let`, but does it internally to simplify
    /// some stuff.
    ///
    /// ```
    /// use lilos_semaphore::{create_semaphore, Semaphore};
    ///
    /// create_semaphore!(five_permits, 5);
    ///
    /// let _one_permit = five_permits.acquire().await;
    /// ```
    ///
    /// Alternatively, if you want to avoid macros that hide the details from
    /// you, you can create one by hand using the same two-step initialization
    /// protocol as `Mutex`. See the source code for `create_semaphore!` for a
    /// working example of how to do it.
    ///
    /// # Fairness
    ///
    /// This semaphore implementation is _fair,_ which in this context means
    /// that permits are handed out in the order they're requested. If the
    /// semaphore runs out of permits, tasks requesting permits are queued in
    /// order and will be issued permits in order as they are returned to the
    /// semaphore.
    #[derive(Debug)]
    pub struct Semaphore {
        available: AtomicUsize,
        #[pin]
        waiters: List<()>,
    }
}

impl Semaphore {
    /// Creates a future that will resolve when it can take a single permit from
    /// the semaphore. Until then, the future will remain pending (i.e. block).
    ///
    /// Normally, once this future resolves, you'd keep the [`Permit`] object
    /// around until you're ready to give up the permit, at which point you'd
    /// drop it.
    ///
    /// To take a permit in a context where you can't keep a `Permit` around,
    /// for whatever reason, you can instead call [`core::mem::forget`] on the
    /// `Permit`. If you do this, be sure to call
    /// [`Semaphore::out_of_band_release`] to return your permit once you're
    /// ready -- otherwise the semaphore can be drained of all permits and
    /// nobody can make progress again.
    ///
    /// # Cancellation
    ///
    /// Cancel-safe but affects fairness.
    ///
    /// If you drop the returned future before it resolves...
    /// - If it had not successfully acquired a permit, nothing happens.
    /// - If it had, the permit is released.
    ///
    /// Dropping the future and re-calling `acquire` bumps the caller to the
    /// back of the priority list, to maintain fairness. Otherwise, the result
    /// is indistinguishable.
    pub async fn acquire(self: Pin<&Self>) -> Permit<'_> {
        loop {
            if let Some(permit) = self.try_acquire() {
                return permit;
            }

            // Add ourselves to the wait list...
            create_node!(node, (), noop_waker());
            self.project_ref()
                .waiters
                .insert_and_wait_with_cleanup(node, || {
                    // This is called when we've been detached from the wait
                    // list, which means a permit was transferred to us, but
                    // we haven't been polled -- and won't ever be polled,
                    // for we are being dropped. This means we need to
                    // release our permit, which might wake another task.
                    self.out_of_band_release();
                })
                .await;
        }
    }

    /// Attempts to take a single permit from the semaphore, returning
    /// `Some(permit)` if one is available immediately, or `None` if they are
    /// all taken.
    ///
    /// Normally, if this returns `Some`, you'd keep the [`Permit`] object around
    /// until you're ready to give up the permit, at which point you'd drop it.
    ///
    /// To take a permit in a context where you can't keep a `Permit` around,
    /// for whatever reason, you can instead call [`core::mem::forget`] on the
    /// `Permit`. If you do this, be sure to call
    /// [`Semaphore::out_of_band_release`] to return your permit once you're
    /// ready -- otherwise the semaphore can be drained of all permits and
    /// nobody can make progress again.
    pub fn try_acquire(self: Pin<&Self>) -> Option<Permit<'_>> {
        self.available
            .fetch_update_polyfill(Ordering::Relaxed, Ordering::Relaxed, |a| {
                a.checked_sub(1)
            })
            .ok()?;
        Some(Permit { semaphore: self })
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
    pub fn out_of_band_release(self: Pin<&Self>) {
        let p = self.project_ref();
        if p.waiters.wake_one() {
            // We have transferred our permit to a waiter, no need to mess with
            // updating the count.
        } else {
            // We don't have to repeat the wake_one call in this loop, because
            // we're not yielding -- we're not even in an async fn! -- so the
            // only thing concurrent with us is ISRs, which can only wake tasks,
            // not insert them.
            //
            // So the fact that the waiters list was found empty cannot change
            // during this loop.
            self.available
                .fetch_update_polyfill(
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                    // Note that this has a potential overflow on addition. This is
                    // deliberate, and is why we're not using fetch_add here!
                    |a| Some(a + 1),
                )
                .unwrap();
        }
    }

    /// Returns an initialized but invalid `Semaphore`.
    ///
    /// You'll rarely use this function directly. For a more convenient way of
    /// creating a `Semaphore`, see [`create_semaphore!`].
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call [`Semaphore::finish_init`].
    pub unsafe fn new(permits: usize) -> ManuallyDrop<Self> {
        let list = unsafe { List::new() };
        ManuallyDrop::new(Semaphore {
            available: AtomicUsize::new(permits),
            waiters: ManuallyDrop::into_inner(list),
        })
    }

    /// Finishes initializing a semaphore, discharging obligations from
    /// [`Semaphore::new`].
    ///
    /// You'll rarely use this function directly. For a more convenient way of
    /// creating a `Semaphore`, see [`create_semaphore!`].
    ///
    /// # Safety
    ///
    /// This is safe to call exactly once on the result of `new`, after it has
    /// been moved to its final position and pinned.
    pub unsafe fn finish_init(this: Pin<&mut Self>) {
        unsafe {
            List::finish_init(this.project().waiters);
        }
    }
}

/// A resource object that represents holding a single permit from a
/// [`Semaphore`].
///
/// You can obtain a `Permit` by calling [`Semaphore::acquire`] or
/// [`Semaphore::try_acquire`]. This decrements the semaphore's internal permit
/// counter by 1. When you `drop` the `Permit`, it increments the counter by
/// 1, possibly waking a task that was blocked.
#[derive(Debug)]
pub struct Permit<'a> {
    semaphore: Pin<&'a Semaphore>,
}

impl Drop for Permit<'_> {
    fn drop(&mut self) {
        self.semaphore.out_of_band_release();
    }
}

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
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let mut $var = core::pin::pin!({
            // Evaluate $permits eagerly, before defining any locals, and
            // outside of any unsafe block. This ensures that the caller will
            // get a warning if they do something unsafe in the $permits
            // expression, while also ensuring that any existing variable called
            // __permits is available for use here.
            let __permits = $permits;
            unsafe {
                core::mem::ManuallyDrop::into_inner($crate::Semaphore::new(
                    __permits,
                ))
            }
        });
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::Semaphore::finish_init($var.as_mut());
        }
        // Drop mutability.
        let $var = $var.as_ref();
    };
}

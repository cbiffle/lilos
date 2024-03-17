//! Timekeeping abstracted over [`Timer`].
//!
//! This module provides the trait [`Timer`], which if implemented will make the
//! methods [`sleep_until`], [`sleep_for`], [`with_deadline`], [`with_timeout`]
//! available.
//!
//! To implement [`Timer`], you only need to implement a way to get the current
//! time, the [`Timer::timer_list`] function is there to get the `timer_list`
//! member, which should be a [`crate::list::List<Interval>`] list which is
//! created using [`crate::create_list!`] at the use-site (i.e. just before
//! calling [`crate::exec::run_tasks_with_idle`] or
//! [`crate::exec::run_tasks_with_preemption_and_idle`] -- you need a custom
//! idle hook, see below).
//!
//! *However* to make use of the timer, you also need to put
//! [`List<Interval: PartialOrd>::wake_less_than`] into the
//! `idle_hook` argument of [`crate::exec::run_tasks_with_idle`]. You presumably
//! also want to wait for the timer (or other) interrupts in the idle hook to
//! save power.
//!
//! See examples/rp2040/multicore/src/main.rs for an example using a custom
//! timer

#[cfg(all(feature = "systick", not(feature = "2core")))]
pub mod systick;
#[cfg(all(feature = "systick", not(feature = "2core")))]
// Re-export for compatibility
pub use systick::*;

use crate::list::List;

use core::future::Future;
use core::ops::Add;
use core::pin::Pin;
use core::task::{Context, Poll};

use pin_project_lite::pin_project;

/// Sleep trait, allowing for sleeping until, etc. Implemented for single-core,
/// you will want to implement it for multicore.
///
/// Example implementation for multi-core is available in
/// examples/rp2040/multicore/src/main.rs
pub trait Timer {
    /// Type of a point in time
    type Instant: PartialOrd;

    /// Read the current point in time
    fn now(&self) -> Self::Instant;

    /// Gets the timer-list of the timer
    fn timer_list(&self) -> Pin<&List<Self::Instant>>;
}

/// Sleeps until the system time is equal to or greater than `deadline`.
///
/// More precisely, `sleep_until(d)` returns a `Future` that will poll as
/// `Pending` until `Timer::now() >= deadline`; then it will poll `Ready`.
///
/// If `deadline` is already in the past, this will instantly become `Ready`.
///
/// Other tools you might consider:
///
/// - If you want to sleep for a relative time interval, consider [`sleep_for`].
/// - If you want to make an action periodic by sleeping in a loop,
///   [`PeriodicGate`] helps avoid common mistakes that cause timing drift and
///   jitter.
/// - If you want to impose a deadline/timeout on async code, see
///   [`with_deadline`].
///
/// # Preconditions
///
/// This can only be used within a task.
///
/// # Cancellation
///
/// **Cancel safety:** Strict.
///
/// Dropping this future does nothing in particular.
pub async fn sleep_until<'a, I, T>(timer: &'a T, deadline: I)
where
    I: PartialOrd + 'a,
    T: Timer<Instant = I>,
{
    if timer.now() >= deadline {
        return;
    }

    crate::create_node!(node, deadline, crate::exec::noop_waker());

    // Insert our node into the pending timer list. If we get cancelled, the
    // node will detach itself as it's being dropped.
    timer.timer_list().insert_and_wait(node.as_mut()).await
}

/// Sleeps until the system time has increased by `d`.
///
/// More precisely, `sleep_for(d)` captures the system time, `t`, and returns a
/// `Future` that will poll as `Pending` until `Timer::now() >= t + d`; then
/// it will poll `Ready`.
///
/// If `d` is 0, this will instantly become `Ready`.
///
/// `d` can be any type that can be added to `Timer::Instant`.
///
/// This function is a thin wrapper around [`sleep_until`]. See that function's
/// docs for examples, details, and alternatives.
///
/// # Cancellation
///
/// **Cancel safety:** Strict.
///
/// Dropping this future does nothing in particular.
pub fn sleep_for<'a, D, I, T>(
    timer: &'a T,
    d: D,
) -> impl Future<Output = ()> + 'a
where
    I: PartialOrd + Add<D, Output = I> + 'a,
    T: Timer<Instant = I>,
{
    let until = timer.now() + d;
    sleep_until(timer, until)
}

/// Alters a future to impose a deadline on its completion.
///
/// Concretely,
/// - The output type is changed from `T` to `Option<T>`.
/// - If the future resolves on any polling that starts before `deadline`, its
///   result will be produced, wrapped in `Some`.
/// - If poll is called at or after `deadline`, the future resolves to `None`.
///
/// The wrapped future is _not_ immediately dropped if the timeout expires. It
/// will be dropped when you drop the wrapped version. Under normal
/// circumstances this happens automatically, e.g. if you do:
///
/// ```ignore
/// with_deadline(MY_DEADLINE, some_operation()).await;
/// ```
///
/// In this case, `await` drops the future as soon as it resolves (as always),
/// which means the nested `some_operation()` future will be promptly dropped
/// when we notice that the deadline has been met or exceeded.
pub fn with_deadline<'a, F, I, T>(
    timer: &'a T,
    deadline: I,
    code: F,
) -> impl Future<Output = Option<F::Output>> + 'a
where
    I: PartialOrd + 'a,
    T: Timer<Instant = I>,
    F: Future + 'a,
{
    TimeLimited {
        limiter: sleep_until(timer, deadline),
        process: code,
    }
}

/// Alters a future to impose a timeout on its completion.
///
/// This is equivalent to [`with_deadline`] using a deadline of `Timer::now()
/// + timeout`. That is, the current time is captured when `with_timeout` is
/// called (_not_ at first poll), the provided timeout is added, and that's used
/// as the deadline for the returned future.
///
/// See [`with_deadline`] for more details.
pub fn with_timeout<'a, D, F, I, T>(
    timer: &'a T,
    timeout: D,
    code: F,
) -> impl Future<Output = Option<F::Output>> + 'a
where
    I: PartialOrd + Add<D, Output = I> + 'a,
    T: Timer<Instant = I>,
    F: Future + 'a,
{
    let until = timer.now() + timeout;
    with_deadline(timer, until, code)
}

pin_project! {
    /// A future-wrapper that gates polling a future `B` on whether another
    /// future `A` has resolved.
    ///
    /// Once `A` resolved, `B` is no longer polled and the combined future
    /// resolves to `None`. If `B` resolves first, its result is produced
    /// wrapped in `Some`.
    #[derive(Debug)]
    pub struct TimeLimited<A, B> {
        #[pin]
        limiter: A,
        #[pin]
        process: B,
    }
}

impl<A, B> Future for TimeLimited<A, B>
where
    A: Future<Output = ()>,
    B: Future,
{
    type Output = Option<B::Output>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let p = self.project();
        // We always check the limiter first. If the limiter's condition has
        // occurred, we bail, even if the limited process is also ready.
        if let Poll::Ready(()) = p.limiter.poll(cx) {
            return Poll::Ready(None);
        }
        p.process.poll(cx).map(Some)
    }
}

/// Helper for doing something periodically, accurately.
///
/// A `PeriodicGate` can be used to *gate* (pause) execution of a task until a
/// point in time arrives; that point in time is *periodic*, meaning it repeats
/// at regular intervals. For example, to call the function `f` every 30
/// milliseconds, you would write:
///
/// ```ignore
/// let gate = PeriodicGate::from(Millis(30));
/// loop {
///     f();
///     gate.next_time().await;
/// }
/// ```
///
/// This will maintain the 30-millisecond interval consistently, even if `f()`
/// takes several milliseconds to run, and even if `f()` is sometimes fast and
/// sometimes slow. (If `f` sometimes takes more than 30 milliseconds, the next
/// execution will happen later than normal -- there's not a lot we can do about
/// that. However, as soon as calls to `f` take less than 30 milliseconds, we'll
/// return to the normal periodic timing.)
///
/// This is often, but not always, what you want in a timing loop.
///
/// - `PeriodicGate` has "catch-up" behavior that might not be what you want: if
///   one execution takes (say) 5 times longer than the chosen period, it will
///   frantically run 4 more just after it to "catch up." This attempts to
///   maintain a constant number of executions per unit time, but that might not
///   be what you want.
///
/// - [`sleep_for`] can ensure a minimum delay _between_ operations, which is
///   different from `PeriodicGate`'s behavior.
#[derive(Debug)]
pub struct PeriodicGate<D, I>
where
    I: PartialOrd + Add<D, Output = I>,
{
    interval: D,
    next: I,
}

#[cfg(all(feature = "systick", not(feature = "2core")))]
impl From<Millis> for PeriodicGate<Millis, TickTime> {
    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting right now.
    fn from(interval: Millis) -> Self {
        PeriodicGate {
            interval,
            next: TickTime::now(),
        }
    }
}

impl<D, I> PeriodicGate<D, I>
where
    D: Copy,
    I: PartialOrd + Add<D, Output = I> + Copy,
{
    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting right now.
    pub fn new<T>(timer: &T, period: D) -> Self
    where
        T: Timer<Instant = I>,
    {
        PeriodicGate {
            interval: period,
            next: timer.now(),
        }
    }

    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting `delay` ticks in the future.
    ///
    /// This can be useful for creating multiple periodic gates that operate out
    /// of phase with respect to each other.
    pub fn new_shift<T>(timer: &T, interval: D, delay: D) -> Self
    where
        T: Timer<Instant = I>,
    {
        PeriodicGate {
            interval,
            next: timer.now() + delay,
        }
    }

    /// Returns a future that will resolve when it's time to execute again.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict.
    ///
    /// Dropping this future does nothing in particular.
    pub async fn next_time<T>(&mut self, timer: &T)
    where
        T: Timer<Instant = I>,
    {
        sleep_until(timer, self.next).await;
        self.next = self.next + self.interval;
    }
}

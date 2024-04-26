//! Timekeeping using the SysTick Timer.
//!
//! **Note:** this entire module is only available if the `systick` feature is
//! present; it is on by default.
//!
//! The OS uses the Cortex-M SysTick Timer to maintain a monotonic counter
//! recording the number of milliseconds ("ticks") since boot. This module
//! provides ways to read that timer, and also to arrange for tasks to be woken
//! at specific times (such as [`sleep_until`] and [`sleep_for`]).
//!
//! To use this facility in an application, you need to call
//! [`initialize_sys_tick`] to inform the OS of the system clock speed.
//! Otherwise, no operations in this module will work properly.
//!
//! You can get the value of tick counter using [`TickTime::now`].
//!
//! # Types for describing time
//!
//! This module uses three main types for describing time, in slightly different
//! roles.
//!
//! `TickTime` represents a specific point in time, measured as a number of
//! ticks since boot (or, really, since the executor was started). It's a
//! 64-bit count of milliseconds, which means it overflows every 584 million
//! years. This lets us ignore overflows in timestamps, making everything
//! simpler. `TickTime` is analogous to `std::time::Instant` from the Rust
//! standard library.
//!
//! `Millis` represents a relative time interval in milliseconds. This uses the
//! same representation as `TickTime`, so adding them together is cheap.
//!
//! `core::time::Duration` is similar to `Millis` but with a lot more bells and
//! whistles. It's the type used to measure time intervals in the Rust standard
//! library. It can be used with most time-related API in the OS, but you might
//! not want to do so on a smaller CPU: `Duration` uses a mixed-number-base
//! format internally that means almost all operations require a 64-bit multiply
//! or divide. On machines lacking such instructions, this can become quite
//! costly (in terms of both program size and time required).
//!
//! Cases where the OS won't accept `Duration` are mostly around things like
//! sleeps, where the operation will always be performed in units of whole
//! ticks, so being able to pass (say) nanoseconds is misleading.
//!
//! # Imposing a timeout on an operation
//!
//! If you want to stop a concurrent process if it's not done by a certain time,
//! see the [`with_deadline`] function (and its relative friend,
//! [`with_timeout`]). These let you impose a deadline on any future, such that
//! if it hasn't resolved by a certain time, it will be dropped (cancelled).
//!
//! # Fixing "lost ticks"
//!
//! If the longest sequence in your application between any two `await` points
//! takes less than a millisecond, the standard timer configuration will work
//! fine and keep reliable time.
//!
//! However, if you sometimes need to do more work than that -- or if you're
//! concerned you might do so by accident due to a bug -- the systick IRQ can be
//! configured to preempt task code. The OS is designed to handle this safely.
//! For more information, see
//! [`run_tasks_with_preemption`][crate::exec::run_tasks_with_preemption].
//!
//! # Getting higher precision
//!
//! For many applications, milliseconds are a fine unit of time, but sometimes
//! you need something more precise. Currently, the easiest way to do this is to
//! enlist a different hardware timer. The `time` module has no special
//! privileges that you can't make use of, and adding your own alternate
//! timekeeping module is explictly supported in the design (this is why the
//! `"systick"` feature exists).
//!
//! This can also be useful on processors like the Nordic nRF52 series, where
//! the best sleep mode to use when idling the CPU also stops the systick timer.
//! On platforms like that, the systick isn't useful as a monotonic clock, and
//! you'll want to use some other vendor-specific timer.
//!
//! Currently there's no example of how to do this in the repo. If you need
//! this, please file an issue.

use core::future::Future;
use core::ops::{Add, AddAssign};
use core::pin::Pin;
use core::sync::atomic::{AtomicU32, Ordering};
use core::task::{Context, Poll};
use core::time::Duration;

use cortex_m::peripheral::{syst::SystClkSource, SYST};
use cortex_m_rt::exception;
use pin_project::pin_project;

use crate::atomic::AtomicArithExt;

/// Bottom 32 bits of the tick counter. Updated by ISR.
static TICK: AtomicU32 = AtomicU32::new(0);
/// Top 32 bits of the tick counter. Updated by ISR.
static EPOCH: AtomicU32 = AtomicU32::new(0);

/// Sets up the tick counter for 1kHz operation, assuming a CPU core clock of
/// `clock_hz`.
///
/// If you use this module in your application, call this before
/// [`run_tasks`][crate::exec::run_tasks] (or a fancier version of `run_tasks`)
/// to set up the timer for monotonic operation.
pub fn initialize_sys_tick(syst: &mut SYST, clock_hz: u32) {
    let cycles_per_millisecond = clock_hz / 1000;
    syst.set_reload(cycles_per_millisecond - 1);
    syst.clear_current();
    syst.set_clock_source(SystClkSource::Core);
    syst.enable_interrupt();
    syst.enable_counter();
}

/// Represents a moment in time by the value of the system tick counter.
/// System-specific analog of `std::time::Instant`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Default)]
pub struct TickTime(u64);

impl TickTime {
    /// Retrieves the current value of the tick counter.
    pub fn now() -> Self {
        // This loop will only repeat if e != e2, which means we raced the
        // systick ISR. Since that ISR only occurs once per millisecond, this
        // loop should repeat at most twice.
        loop {
            let e = EPOCH.load(Ordering::SeqCst);
            let t = TICK.load(Ordering::SeqCst);
            let e2 = EPOCH.load(Ordering::SeqCst);
            if e == e2 {
                break TickTime(((e as u64) << 32) | (t as u64));
            }
        }
    }

    /// Constructs a `TickTime` value describing a certain number of
    /// milliseconds since the executor booted.
    pub fn from_millis_since_boot(m: u64) -> Self {
        Self(m)
    }

    /// Subtracts this time from an earlier time, giving the `Duration` between
    /// them.
    ///
    /// # Panics
    ///
    /// If this time is not actually `>= earlier`.
    pub fn duration_since(self, earlier: TickTime) -> Duration {
        Duration::from_millis(self.millis_since(earlier).0)
    }

    /// Subtracts this time from an earlier time, giving the amount of time
    /// between them measured in `Millis`.
    ///
    /// # Panics
    ///
    /// If this time is not actually `>= earlier`.
    pub fn millis_since(self, earlier: TickTime) -> Millis {
        Millis(self.0.checked_sub(earlier.0).unwrap())
    }

    /// Checks the clock to determine how much time has elapsed since the
    /// instant recorded by `self`.
    pub fn elapsed(self) -> Millis {
        Self::now().millis_since(self)
    }

    /// Checks the clock to determine how much time has elapsed since the
    /// instant recorded by `self`. Convenience version that returns the result
    /// as a `Duration`.
    pub fn elapsed_duration(self) -> Duration {
        Duration::from_millis(self.elapsed().0)
    }

    /// Adds some milliseconds to `self`, checking for overflow. Note that since
    /// we use 64 bit ticks, overflow is unlikely in practice.
    pub fn checked_add(self, millis: Millis) -> Option<Self> {
        self.0.checked_add(millis.0).map(TickTime)
    }

    /// Subtracts some milliseconds from `self`, checking for overflow. Overflow
    /// can occur if `millis` is longer than the time from boot to `self`.
    pub fn checked_sub(self, millis: Millis) -> Option<Self> {
        self.0.checked_sub(millis.0).map(TickTime)
    }
}

/// Add a `Duration` to a `Ticks` with normal `+` overflow behavior (i.e.
/// checked in debug builds, optionally not checked in release builds).
impl Add<Duration> for TickTime {
    type Output = Self;
    fn add(self, other: Duration) -> Self::Output {
        TickTime(self.0 + other.as_millis() as u64)
    }
}

impl AddAssign<Duration> for TickTime {
    fn add_assign(&mut self, other: Duration) {
        self.0 += other.as_millis() as u64
    }
}

impl From<TickTime> for u64 {
    fn from(t: TickTime) -> Self {
        t.0
    }
}

/// A period of time measured in milliseconds.
///
/// This plays a role similar to `core::time::Duration` but is designed to be
/// cheaper to use. In particular, as of this writing, `Duration` insists on
/// converting times to and from a Unix-style (seconds, nanoseconds)
/// representation internally. This means that converting to or from any simple
/// monotonic time -- even in nanoseconds! -- requires a 64-bit division or
/// multiplication. Many useful processors, such as Cortex-M0, don't have 32-bit
/// division, much less 64-bit division.
///
/// `Millis` wraps a `u64` and records a number of milliseconds. Since
/// milliseconds are `lilos`'s unit used for internal timekeeping, this ensures
/// that a `Millis` can be used for any deadline or timeout computation without
/// any unit conversions or expensive arithmetic operations.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Default)]
pub struct Millis(pub u64);

/// Adds a number of milliseconds to a `TickTime` with normal `+` overflow
/// behavior (i.e. checked in debug builds, optionally not checked in release
/// builds).
impl Add<Millis> for TickTime {
    type Output = Self;
    fn add(self, other: Millis) -> Self::Output {
        TickTime(self.0 + other.0)
    }
}

/// Adds a number of milliseconds to a `TickTime` with normal `+=` overflow
/// behavior (i.e. checked in debug builds, optionally not checked in release
/// builds).
impl AddAssign<Millis> for TickTime {
    fn add_assign(&mut self, other: Millis) {
        self.0 += other.0;
    }
}

impl From<Millis> for u64 {
    fn from(x: Millis) -> Self {
        x.0
    }
}

impl From<u64> for Millis {
    fn from(x: u64) -> Self {
        Self(x)
    }
}

/// Sleeps until the system time is equal to or greater than `deadline`.
///
/// More precisely, `sleep_until(d)` returns a `Future` that will poll as
/// `Pending` until `TickTime::now() >= deadline`; then it will poll `Ready`.
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
pub async fn sleep_until(deadline: TickTime) {
    if TickTime::now() >= deadline {
        return;
    }

    crate::create_node!(node, deadline, crate::exec::noop_waker());

    // Insert our node into the pending timer list. If we get cancelled, the
    // node will detach itself as it's being dropped.
    crate::exec::get_timer_list().insert_and_wait(node.as_mut()).await
}

/// Sleeps until the system time has increased by `d`.
///
/// More precisely, `sleep_for(d)` captures the system time, `t`, and returns a
/// `Future` that will poll as `Pending` until `TickTime::now() >= t + d`; then
/// it will poll `Ready`.
///
/// If `d` is 0, this will instantly become `Ready`.
///
/// `d` can be any type that can be added to a `TickTime`, which in practice
/// means either [`Millis`] or [`Duration`].
///
/// This function is a thin wrapper around [`sleep_until`]. See that function's
/// docs for examples, details, and alternatives.
///
/// # Cancellation
///
/// **Cancel safety:** Strict.
///
/// Dropping this future does nothing in particular.
pub fn sleep_for<D>(d: D) -> impl Future<Output = ()>
    where TickTime: Add<D, Output = TickTime>,
{
    sleep_until(TickTime::now() + d)
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
pub fn with_deadline<F>(deadline: TickTime, code: F) -> impl Future<Output = Option<F::Output>>
    where F: Future,
{
    TimeLimited {
        limiter: sleep_until(deadline),
        process: code,
    }
}

/// Alters a future to impose a timeout on its completion.
///
/// This is equivalent to [`with_deadline`] using a deadline of `TickTime::now()
/// + timeout`. That is, the current time is captured when `with_timeout` is
/// called (_not_ at first poll), the provided timeout is added, and that's used
/// as the deadline for the returned future.
///
/// See [`with_deadline`] for more details.
pub fn with_timeout<D, F>(timeout: D, code: F) -> impl Future<Output = Option<F::Output>>
    where F: Future,
          TickTime: Add<D, Output = TickTime>,
{
    with_deadline(TickTime::now() + timeout, code)
}

/// A future-wrapper that gates polling a future `B` on whether another
/// future `A` has resolved.
///
/// Once `A` resolved, `B` is no longer polled and the combined future
/// resolves to `None`. If `B` resolves first, its result is produced
/// wrapped in `Some`.
#[derive(Debug)]
#[pin_project]
struct TimeLimited<A, B> {
    #[pin]
    limiter: A,
    #[pin]
    process: B,
}

impl<A, B> Future for TimeLimited<A, B>
    where A: Future<Output = ()>,
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
pub struct PeriodicGate {
    interval: Millis,
    next: TickTime,
}

impl From<Duration> for PeriodicGate {
    fn from(d: Duration) -> Self {
        PeriodicGate {
            interval: Millis(d.as_millis() as u64),
            next: TickTime::now(),
        }
    }
}

impl From<Millis> for PeriodicGate {
    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting right now.
    fn from(interval: Millis) -> Self {
        PeriodicGate {
            interval,
            next: TickTime::now(),
        }
    }
}

impl PeriodicGate {
    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting `delay` ticks in the future.
    ///
    /// This can be useful for creating multiple periodic gates that operate out
    /// of phase with respect to each other.
    pub fn new_shift(interval: Millis, delay: Millis) -> Self {
        PeriodicGate {
            interval,
            next: TickTime::now() + delay,
        }
    }

    /// Returns a future that will resolve when it's time to execute again.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict.
    ///
    /// Dropping this future does nothing in particular.
    pub async fn next_time(&mut self) {
        sleep_until(self.next).await;
        self.next += self.interval;
    }
}

/// System tick ISR. Advances the tick counter. This doesn't wake any tasks; see
/// code in `exec` for that.
#[doc(hidden)]
#[exception]
fn SysTick() {
    if TICK.fetch_add_polyfill(1, Ordering::Release) == u32::MAX {
        EPOCH.fetch_add_polyfill(1, Ordering::Release);
    }
}

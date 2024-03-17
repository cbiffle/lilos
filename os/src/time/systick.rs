//! Timekeeping using the SysTick Timer.
//!
//! **Note:** this entire module is only available if the `systick` feature is
//! present, and the `2core` feature is not; which is the default.
//!
//! The OS uses the Cortex-M SysTick Timer to maintain a monotonic counter
//! recording the number of milliseconds ("ticks") since boot. This module
//! provides ways to read that timer, and also to arrange for tasks to be woken
//! at specific times (such as [`super::sleep_until`] and [`super::sleep_for`]).
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
//! see the [`super::with_deadline`] function (and its relative friend,
//! [`super::with_timeout`]). These let you impose a deadline on any future, such that
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

use crate::cheap_assert;
use crate::list::List;

use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Add, AddAssign};
use core::pin::Pin;
use core::ptr::{addr_of, addr_of_mut};
use core::time::Duration;

use cortex_m::peripheral::{syst::SystClkSource, SYST};
use cortex_m_rt::exception;

use portable_atomic::{AtomicBool, AtomicU32, Ordering};

/// Bottom 32 bits of the tick counter. Updated by ISR.
static TICK: AtomicU32 = AtomicU32::new(0);
/// Top 32 bits of the tick counter. Updated by ISR.
static EPOCH: AtomicU32 = AtomicU32::new(0);

/// Sets up the tick counter for 1kHz operation, assuming a CPU core clock of
/// `clock_mhz`.
///
/// If you use this module in your application, call this before
/// [`run_tasks`][crate::exec::run_tasks] (or a fancier version of `run_tasks`)
/// to set up the timer for monotonic operation.
pub fn initialize_sys_tick(syst: &mut SYST, clock_mhz: u32) {
    let cycles_per_millisecond = clock_mhz / 1000;
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

/// System tick ISR. Advances the tick counter. This doesn't wake any tasks; see
/// code in `exec` for that.
#[doc(hidden)]
#[exception]
fn SysTick() {
    if TICK.fetch_add(1, Ordering::Release) == core::u32::MAX {
        EPOCH.fetch_add(1, Ordering::Release);
    }
}

/// Tracks whether the timer list has been initialized.
static TIMER_LIST_READY: AtomicBool = AtomicBool::new(false);

/// Storage for the timer list.
static mut TIMER_LIST: MaybeUninit<List<TickTime>> = MaybeUninit::uninit();

/// A timer using the SysTick of the core.
#[derive(Debug)]
pub struct SysTickTimer;

impl SysTickTimer {
    pub(crate) fn init(&self) {
        let already_initialized = TIMER_LIST_READY.swap(true, Ordering::SeqCst);
        // Catch any attempt to do this twice. Would doing this twice be bad?
        // Not necessarily. But it would be damn suspicious.
        cheap_assert!(!already_initialized);

        // Safety: by successfully flipping the initialization flag, we know
        // we can do this without aliasing; being in a single-threaded context
        // right now means we can do it without racing.
        let timer_list = unsafe { &mut *addr_of_mut!(TIMER_LIST) };
        // Initialize the list node itself.
        //
        // Safety: we discharge the obligations of `new` here by continuing,
        // below, to pin and finish initialization of the list.
        timer_list.write(ManuallyDrop::into_inner(unsafe { List::new() }));
        // Safety: we're not going to overwrite or drop this static list, so we
        // have trivially fulfilled the pin requirements.
        let mut timer_list =
            unsafe { Pin::new_unchecked(timer_list.assume_init_mut()) };
        // Safety: finish_init requires that we haven't done anything to the
        // List since `new` except for pinning it, which is the case here.
        unsafe {
            List::finish_init(timer_list.as_mut());
        }

        // The list is initialized; we can now produce _shared_ references to
        // it. Our one and only Pin<&mut List> ends here.
    }
}

impl super::Timer for SysTickTimer {
    type Instant = TickTime;

    fn now(&self) -> Self::Instant {
        TickTime::now()
    }

    /// Nabs a reference to the current timer list and executes `body`.
    ///
    /// This provides a safe way to access the timer thread local.
    ///
    /// # Preconditions
    ///
    /// - Must not be called from an interrupt.
    /// - Must only be called with a timer list available, which is to say, from
    ///   within a task.
    fn timer_list(&self) -> Pin<&List<Self::Instant>> {
        // Prevent this from being used from interrupt context.

        crate::exec::assert_not_in_isr();

        // Ensure that the timer list has been initialized.
        cheap_assert!(TIMER_LIST_READY.load(Ordering::Acquire));

        // Since we know we're not running concurrently with the scheduler setup, we
        // can freely vend pin references to the now-immortal timer list.
        //
        // Safety: &mut references to TIMER_LIST have stopped after initialization.
        let list_ref = unsafe { &*addr_of!(TIMER_LIST) };
        // Safety: we know the list has been initialized because we checked
        // TIMER_LIST_READY, above. We also know that the list trivially meets the
        // pin criterion, since it's immortal and always referenced by shared
        // reference at this point.
        unsafe { Pin::new_unchecked(list_ref.assume_init_ref()) }
    }
}

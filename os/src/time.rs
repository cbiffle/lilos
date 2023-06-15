//! Timekeeping.
//!
//! The OS uses the Cortex-M SysTick Timer to maintain a count of ticks since
//! boot. You can get the value of this counter using
//! [`TickTime::now()`][TickTime::now].
//!
//! Ticks are currently fixed at 1ms.
//!
//! Application startup code needs to call [`initialize_sys_tick`] to inform the
//! OS of the system clock speed. Otherwise, no timing-related calls will behave
//! correctly.
//!
//! Note: this entire module is only available if the `systick` feature is
//! present; it is on by default.
//!
//! # Types for describing time
//!
//! This module uses three main types for describing time, in slightly different
//! roles.
//!
//! `TickTime` represents a specific point in time, measured as a number of
//! ticks since boot (or, really, since the OS itself was started). It's a
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
//! sleeps, where the operation will be performed in millisecond units, so being
//! able to pass (say) nanoseconds is misleading.

use core::sync::atomic::{AtomicU32, Ordering};
use core::time::Duration;

use cortex_m::peripheral::{syst::SystClkSource, SYST};
use cortex_m_rt::exception;

use crate::atomic::AtomicArithExt;

/// Bottom 32 bits of the tick counter. Updated by ISR.
static TICK: AtomicU32 = AtomicU32::new(0);
/// Top 32 bits of the tick counter. Updated by ISR.
static EPOCH: AtomicU32 = AtomicU32::new(0);

/// Sets up the tick counter for 1kHz operation, assuming a CPU core clock of
/// `clock_mhz`.
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
impl core::ops::Add<Duration> for TickTime {
    type Output = Self;
    fn add(self, other: Duration) -> Self::Output {
        TickTime(self.0 + other.as_millis() as u64)
    }
}

impl core::ops::AddAssign<Duration> for TickTime {
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
impl core::ops::Add<Millis> for TickTime {
    type Output = Self;
    fn add(self, other: Millis) -> Self::Output {
        TickTime(self.0 + other.0)
    }
}

/// Adds a number of milliseconds to a `TickTime` with normal `+=` overflow
/// behavior (i.e. checked in debug builds, optionally not checked in release
/// builds).
impl core::ops::AddAssign<Millis> for TickTime {
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
    if TICK.fetch_add_polyfill(1, Ordering::Release) == core::u32::MAX {
        EPOCH.fetch_add_polyfill(1, Ordering::Release);
    }
}

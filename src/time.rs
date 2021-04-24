//! Timekeeping.
//!
//! The OS uses the Cortex-M SysTick Timer to maintain a count of ticks since
//! boot. You can get the value of this counter using
//! [`Ticks::now()`][Ticks::now].
//!
//! Ticks are currently fixed at 1ms.
//!
//! Application startup code needs to call [`initialize_sys_tick`] to inform the
//! OS of the system clock speed. Otherwise, no timing-related calls will behave
//! correctly.

use core::sync::atomic::{AtomicU32, Ordering};
use core::time::Duration;

use cortex_m::peripheral::{syst::SystClkSource, SYST};

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
pub struct Ticks(u64);

impl Ticks {
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
                break Ticks(((e as u64) << 32) | (t as u64));
            }
        }
    }

    /// Subtracts this time from an earlier time, giving the `Duration` between
    /// them.
    ///
    /// # Panics
    ///
    /// If this time is not actually `>= earlier`.
    pub fn duration_since(self, earlier: Ticks) -> Duration {
        Duration::from_millis(self.0.checked_sub(earlier.0).unwrap())
    }

    /// Checks the clock to determine how much time has elapsed since the
    /// instant recorded by `self`.
    pub fn elapsed(self) -> Duration {
        Self::now().duration_since(self)
    }

    /// Adds a duration to `self`, checking for overflow. Note that since we use
    /// 64 bit ticks, overflow is unlikely in practice.
    pub fn checked_add(self, duration: Duration) -> Option<Self> {
        self.0.checked_add(duration.as_millis() as u64).map(Ticks)
    }

    /// Subtracts a duration from `self`, checking for overflow. Overflow can
    /// occur if `duration` is longer than the time from boot to `self`.
    pub fn checked_sub(self, duration: Duration) -> Option<Self> {
        self.0.checked_sub(duration.as_millis() as u64).map(Ticks)
    }
}

/// Add a `Duration` to a `Ticks` with normal `+` overflow behavior (i.e.
/// checked in debug builds, optionally not checked in release builds).
impl core::ops::Add<Duration> for Ticks {
    type Output = Self;
    fn add(self, other: Duration) -> Self::Output {
        Ticks(self.0 + other.as_millis() as u64)
    }
}

impl core::ops::AddAssign<Duration> for Ticks {
    fn add_assign(&mut self, other: Duration) {
        self.0 += other.as_millis() as u64
    }
}

/// System tick ISR. Advances the tick counter. This doesn't wake any tasks; see
/// code in `exec` for that.
#[doc(hidden)]
#[cortex_m_rt::exception]
fn SysTick() {
    if TICK.fetch_add(1, Ordering::Release) == core::u32::MAX {
        EPOCH.fetch_add(1, Ordering::Release);
    }
}

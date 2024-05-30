// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Cortex-M implemention of timer interface.

use cortex_m::peripheral::{syst::SystClkSource, SYST};
use cortex_m_rt::exception;

use crate::time::TickTime;

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

/// System tick ISR. Advances the tick counter. This doesn't wake any tasks; see
/// code in `exec` for that.
#[doc(hidden)]
#[exception]
fn SysTick() {
    TickTime::increment();
}

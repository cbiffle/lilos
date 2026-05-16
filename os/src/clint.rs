// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Support for the riscv CLINT mtimer peripheral.
use crate::time::TickTime;

/// Starts the system clock.
pub fn initialize_sys_tick() {
    timer_isr(); // set mtimecmp
    unsafe {
        riscv::register::mie::set_mtimer();
        riscv::interrupt::enable();
    }
}

extern "Rust" {
    /// Application must implement this function, which returns the
    /// timer instance and the system clock frequency, expressed in
    /// clock ticks
    fn _get_sysclk() -> (riscv_peripheral::aclint::mtimer::MTIMER, u64);
}

#[export_name = "MachineTimer"]
#[doc(hidden)]
fn timer_isr() {
    TickTime::increment();
    let (mtimer, freq) = unsafe { _get_sysclk() };
    let now = mtimer.mtime.read();
    let next = now + freq;
    mtimer.mtimecmp0.write(next);
}

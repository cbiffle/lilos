// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! OS test suite, LM3S6965 wrapper.

#![no_std]
#![no_main]

riscv_peripheral::clint_codegen!(
    base 0x0200_0000,    // hardcoded in QEMU virt.c
    freq 10_000_000,    // RISCV_ACLINT_DEFAULT_TIMEBASE_FREQ in QEMU sources
);

#[no_mangle]
pub fn _get_sysclk() -> (riscv_peripheral::aclint::mtimer::MTIMER, u64) {
    (CLINT::mtimer(), CLINT::freq() as u64 / 1000) // 1ms clock tick
}

use core::panic::PanicInfo;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // logs "panicked at '$reason', src/main.rs:27:4" to the host stderr
    riscv_semihosting::hprintln!("{}", info);
    riscv_semihosting::debug::exit(Err(()));

    loop {}
}

#[riscv_rt::entry]
fn main() -> ! {
    lilos_testsuite::run_test_suite(0);
}

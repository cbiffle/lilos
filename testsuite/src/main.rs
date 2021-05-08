//! OS test suite.
//!
//! The test suite is SoC-independent, but we build and test on STM32F407
//! because Cargo's feature resolution plus `cortex-m-rt`'s feature handling
//! means that every binary in this workspace has to target the same SoC. Sigh.

#![no_std]
#![no_main]

extern crate panic_semihosting;
extern crate stm32f4;

use cortex_m_semihosting::hprintln;

/// This constant assumes a 16MHz clock at reset. You probably don't need to
/// adjust it if your processor starts at a different speed; none of the tests
/// rely on this being _correct,_ they only require it to have been set.
const HZ: u32 = 16_000_000;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();

    let startup_task = test_startup_task();
    pin_utils::pin_mut!(startup_task);

    lilos::time::initialize_sys_tick(&mut cp.SYST, HZ);
    lilos::exec::run_tasks(
        &mut [
            startup_task,
        ],
        lilos::exec::ALL_TASKS,
    )
}

async fn test_startup_task() -> ! {
    hprintln!("tests complete.").ok();
    loop {
        cortex_m::asm::wfi();
    }
}

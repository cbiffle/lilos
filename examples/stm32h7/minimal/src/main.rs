// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Minimal example of using `lilos` to blink an LED at 1Hz on the
//! STM32H7 NUCLEO board.
//!
//! This starts a single task, which uses the scheduler and timer to
//! periodically toggle a GPIO pin (B0, which is an LED on the STM32H7 NUCLEO
//! board).
//!
//! This demonstrates
//!
//! 1. How to start the `lilos` executor and configure timekeeping.
//! 2. How to perform periodic actions and delays.
//! 3. How to safely share data on the stack with a task.

// We won't be using the standard library.
#![no_std]
// We don't have a conventional `main` (`cortex_m_rt::entry` is different).
#![no_main]

// Pull in a panic handling crate. We have to `extern crate` this explicitly
// because it isn't otherwise referenced in code!
extern crate panic_halt;

use stm32_metapac::{self as device, gpio::vals::Moder};

// How often our blinky task wakes up (1/2 our blink frequency).
const PERIOD: lilos::time::Millis = lilos::time::Millis(500);

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();

    // Turn on GPIOB. Note the barrier: the H7 is a multi-issue CPU and if we
    // want a specific ordering of memory operations, we have to ask for it.
    device::RCC.ahb4enr().modify(|w| w.set_gpioben(true));
    cortex_m::asm::dmb();

    // Configure our output pin, B0.
    device::GPIOB.moder().modify(|w| w.set_moder(0, Moder::OUTPUT));

    // Create a task to blink the LED. You could also write this as an `async
    // fn` but we've inlined it as an `async` block for simplicity.
    let blink = core::pin::pin!(async {
        // PeriodicGate is a `lilos` tool for implementing low-jitter periodic
        // actions. It opens once per PERIOD.
        let mut gate = lilos::time::PeriodicGate::from(PERIOD);

        // Loop forever, blinking things. Note that this borrows the device
        // peripherals `p` from the enclosing stack frame.
        loop {
            device::GPIOB.bsrr().write(|w| w.set_bs(0, true));
            gate.next_time().await;
            device::GPIOB.bsrr().write(|w| w.set_br(0, true));
            gate.next_time().await;
        }
    });

    // Configure the systick timer for 1kHz ticks at 64MHz (the speed the CPU is
    // running at when it leaves reset).
    lilos::cortex_m_timer::initialize_sys_tick(&mut cp.SYST, 64_000_000);
    // Set up and run the scheduler with a single task.
    lilos::exec::run_tasks(
        &mut [blink],  // <-- array of tasks
        lilos::exec::ALL_TASKS,  // <-- which to start initially
    )
}

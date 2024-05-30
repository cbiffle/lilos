// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! More complex LED-blinking demo using parameterized tasks.
//!
//! This blinks four LEDs on the STM32F4DISCOVERY board. Each LED uses the same
//! blink routine, but customized with different parameters to achieve different
//! frequencies and control different pins.
//!
//! The LEDs are expected to be on pins PD12-PD15.
//!
//! This example leaves out some detail compared to `minimal`, you may want to
//! read that one first.
//!
//! This demonstrates the stuff included in `minimal`, plus:
//!
//! 1. How to start multiple tasks.
//! 2. How to customize a single `async fn` to create multiple tasks with
//!    different behavior.

#![no_std]
#![no_main]

// Pull in a panic handling crate. We have to `extern crate` this explicitly
// because it isn't otherwise referenced in code!
extern crate panic_halt;

use core::convert::Infallible;
use core::pin::pin;
use core::time::Duration;

use lilos::time::sleep_for;

// Shorthand for which SoC we're targeting:
use stm32_metapac::{self as device, gpio::vals::Moder};

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();

    // Enable clock to GPIOD.
    device::RCC.ahb1enr().modify(|w| w.set_gpioden(true));
    // Set pins D12 thru D15 to outputs.
    device::GPIOD.moder().modify(|w| {
        for p in 12..=15 {
            w.set_moder(p, Moder::OUTPUT);
        }
    });

    // Allocate some tasks, each with different LED mask and period.
    let fut1 = pin!(blinky(1 << 12, Duration::from_millis(800), device::GPIOD));
    let fut2 = pin!(blinky(1 << 13, Duration::from_millis(400), device::GPIOD));
    let fut3 = pin!(blinky(1 << 14, Duration::from_millis(200), device::GPIOD));
    let fut4 = pin!(blinky(1 << 15, Duration::from_millis(100), device::GPIOD));

    // Set up the OS timer. This can be done before or after starting the
    // scheduler, but must be done before using any timer features.
    lilos::cortex_m_timer::initialize_sys_tick(&mut cp.SYST, 16_000_000);

    // Run our four tasks in parallel. The final parameter specifies which tasks
    // to poll on the first iteration.
    lilos::exec::run_tasks(
        &mut [fut1, fut2, fut3, fut4],
        lilos::exec::ALL_TASKS,
    )
}

/// Blinks LED(s) attached to GPIOD as a concurrent process.
///
/// The pins being driven are given by `pin_mask`; a 1 bit means the
/// corresponding pin is driven. `interval_ms` gives the time between toggles in
/// milliseconds, or half of the overall blink period.
///
/// Each call to `blinky` produces a `Future` that captures its parameters. The
/// `Future` loops forever, as indicated by its "never resolves" return type,
/// `!`.
async fn blinky(pin_mask: u16, interval: Duration, gpiod: device::gpio::Gpio)
    -> Infallible
{
    // Zero-extend the mask to fit the BSRR register.
    let pin_mask = u32::from(pin_mask);

    loop {
        // on
        gpiod.bsrr().write(|w| w.0 = pin_mask);
        sleep_for(interval).await;
        // off (same bits set in top 16 bits)
        gpiod.bsrr().write(|w| w.0 = pin_mask << 16);
        sleep_for(interval).await;
    }
}

//! Slightly more interesting example demonstrating parameterized tasks.
//!
//! This blinks four LEDs on the STM32F4DISCOVERY board. Each LED uses the same
//! task function, but customized with different parameters.

#![no_std]
#![no_main]

extern crate panic_halt;

use core::time::Duration;

use lilos::exec::sleep_for;
use pin_utils::pin_mut;
use stm32f4::stm32f407 as device;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = device::Peripherals::take().unwrap();

    // Enable power to GPIOD.
    p.RCC.ahb1enr.modify(|_, w| w.gpioden().enabled());
    // Set pins to outputs.
    p.GPIOD.moder.modify(|_, w| {
        w.moder12()
            .output()
            .moder13()
            .output()
            .moder14()
            .output()
            .moder15()
            .output()
    });

    // Allocate some tasks, each with different LED mask and period. Note that
    // we're able to have each task *borrow* a reference to GPIOD, which is not
    // `Sync` -- because the tasks are cooperative, it doesn't need to be.
    let fut1 = blinky(1 << 12, 800, &p.GPIOD);
    pin_mut!(fut1);
    let fut2 = blinky(1 << 13, 400, &p.GPIOD);
    pin_mut!(fut2);
    let fut3 = blinky(1 << 14, 200, &p.GPIOD);
    pin_mut!(fut3);
    let fut4 = blinky(1 << 15, 100, &p.GPIOD);
    pin_mut!(fut4);

    // Set up the OS timer. This can be done before or after starting the
    // scheduler, but must be done before using any timer features.
    lilos::time::initialize_sys_tick(&mut cp.SYST, 16_000_000);

    // Run them in parallel. The final parameter specifies which tasks to poll
    // on the first iteration as a bitmask, so `!0` means "all."
    lilos::exec::run_tasks(
        &mut [fut1, fut2, fut3, fut4],
        lilos::exec::ALL_TASKS,
    )
}

/// A task that will blink LED(s) attached to GPIOD.
///
/// The pins being driven are given by `pin_mask`; a 1 bit means the
/// corresponding pin is driven. `interval_ms` gives the time between toggles in
/// milliseconds, or half of the overall blink period.
async fn blinky(pin_mask: u16, interval_ms: u64, gpiod: &device::GPIOD) -> ! {
    let p = Duration::from_millis(interval_ms);
    let pin_mask = u32::from(pin_mask);

    loop {
        gpiod.bsrr.write(|w| unsafe { w.bits(pin_mask) });
        sleep_for(p).await;
        gpiod.bsrr.write(|w| unsafe { w.bits(pin_mask << 16) });
        sleep_for(p).await;
    }
}

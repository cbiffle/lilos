#![no_std]
#![no_main]
#![feature(never_type)]

extern crate panic_halt;

use core::time::Duration;

use os::exec::sleep_for;
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
    p.GPIOD
        .moder
        .modify(|_, w| w.moder12().output().moder13().output());

    // Allocate some tasks, each with different LED mask and period. Loan them
    // all GPIOD; we can do this safely because the tasks won't run on separate
    // threads.
    let fut1 = blinky(1 << 12, 500, &p.GPIOD);
    pin_mut!(fut1);
    let fut2 = blinky(1 << 13, 300, &p.GPIOD);
    pin_mut!(fut2);

    // Set up the OS timer. This can be done before or after starting the
    // scheduler, but must be done before using any timer features.
    os::time::initialize_sys_tick(&mut cp.SYST, 8_000_000);

    // Run them in parallel. The final parameter specifies which tasks to poll
    // on the first iteration as a bitmask, so `!0` means "all."
    os::exec::run_tasks(&mut [fut1, fut2], !0)
}

/// A task that will blink LED(s) attached to GPIOD.
///
/// The pins being driven are given by `mask`; a 1 bit means the corresponding
/// pin is driven. `interval_ms` gives the time between toggles in milliseconds,
/// or half of the overall blink period.
async fn blinky(mask: u16, interval_ms: u32, gpiod: &device::GPIOD) -> ! {
    let p = Duration::from_millis(u64::from(interval_ms));
    let mask = u32::from(mask);

    loop {
        gpiod.bsrr.write(|w| unsafe { w.bits(mask) });
        sleep_for(p).await;
        gpiod.bsrr.write(|w| unsafe { w.bits(mask << 16) });
        sleep_for(p).await;
    }
}

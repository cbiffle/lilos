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
use core::time::Duration;

use lilos::exec::sleep_for;
use pin_utils::pin_mut;

// Shorthand for which SoC we're targeting:
use stm32f4::stm32f407 as device;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = device::Peripherals::take().unwrap();

    // Enable clock to GPIOD.
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
    // we're able to have each task *borrow* a reference to GPIOD. This is
    // interesting because we're loaning a local variable to other tasks, and
    // also because `p.GPIOD` is not `Sync` and so normally cannot be shared
    // across threads -- but our tasks are not threads, since they are
    // cooperatively scheduled. So this just works.
    let fut1 = blinky(1 << 12, Duration::from_millis(800), &p.GPIOD);
    pin_mut!(fut1);
    let fut2 = blinky(1 << 13, Duration::from_millis(400), &p.GPIOD);
    pin_mut!(fut2);
    let fut3 = blinky(1 << 14, Duration::from_millis(200), &p.GPIOD);
    pin_mut!(fut3);
    let fut4 = blinky(1 << 15, Duration::from_millis(100), &p.GPIOD);
    pin_mut!(fut4);

    // Set up the OS timer. This can be done before or after starting the
    // scheduler, but must be done before using any timer features.
    lilos::time::initialize_sys_tick(&mut cp.SYST, 16_000_000);

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
async fn blinky(pin_mask: u16, interval: Duration, gpiod: &device::GPIOD)
    -> Infallible
{
    // Zero-extend the mask to fit the BSRR register.
    let pin_mask = u32::from(pin_mask);

    loop {
        // on
        gpiod.bsrr.write(|w| unsafe { w.bits(pin_mask) });
        sleep_for(interval).await;
        // off (same bits set in top 16 bits)
        gpiod.bsrr.write(|w| unsafe { w.bits(pin_mask << 16) });
        sleep_for(interval).await;
    }
}

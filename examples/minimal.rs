//! Minimal example of using the OS to blink an LED at 1Hz on the
//! STM32F4DISCOVERY board.
//!
//! This starts a single task, which uses the scheduler and timer to
//! periodically toggle a GPIO pin.

#![no_std]
#![no_main]

extern crate panic_halt;

use core::time::Duration;

use stm32f4::stm32f407 as device;

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = device::Peripherals::take().unwrap();

    // Configure our output pin.
    p.RCC.ahb1enr.modify(|_, w| w.gpioden().enabled());
    p.GPIOD.moder.modify(|_, w| w.moder12().output());

    // Create a task to blink the LED.
    let blink = async {
        const PERIOD: Duration = Duration::from_millis(500);
        let mut gate = lilos::exec::PeriodicGate::new(PERIOD);

        loop {
            p.GPIOD.bsrr.write(|w| w.bs12().set_bit());
            gate.next_time().await;
            p.GPIOD.bsrr.write(|w| w.br12().set_bit());
            gate.next_time().await;
        }
    };
    pin_utils::pin_mut!(blink);

    // Set up and run the scheduler.
    lilos::time::initialize_sys_tick(&mut cp.SYST, 16_000_000);
    lilos::exec::run_tasks(
        &mut [blink],
        lilos::exec::ALL_TASKS,
    )
}

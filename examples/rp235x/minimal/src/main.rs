// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Minimal example of using `lilos` to blink an LED at 1Hz on the
//! Raspberry Pi Pico board.
//!
//! This starts a single task, which uses the scheduler and timer to
//! periodically toggle a GPIO pin (pin 22, which is an LED on the Pi Pico
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

// GPIO module
pub mod gpio;

// Pull in a panic handling crate. We have to `extern crate` this explicitly
// because it isn't otherwise referenced in code!
extern crate panic_halt;

/// A Block as understood by the Boot ROM.
///
/// This is an Image Definition Block
///
/// It contains within the special start and end markers the Boot ROM is looking for.
#[derive(Debug)]
#[repr(C)]
pub struct ImageDefBlock {
    marker_start: u32,
    item: u32,
    length: u32,
    offset: u32,
    marker_end: u32,
}

/// Tell the Boot ROM about our application
/// Refer RP2350 Datasheet, 5.9.5.1. Minimum Arm IMAGE_DEF
/// TODO: Assuming CRIT1.SECURE_BOOT_ENABLE is clear
#[unsafe(link_section = ".image_def")]
#[used]
pub static MINIMUM_ARM_IMAGE_DEF: ImageDefBlock = ImageDefBlock {
    marker_start: 0xffffded3,
    item: 0x10210142,
    length: 0x000001ff,
    offset: 0x00000000,
    marker_end: 0xab123579,
};

// How often our blinky task wakes up (1/2 our blink frequency).
const PERIOD: lilos::time::Millis = lilos::time::Millis(500);

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = unsafe { rp235x_pac::Peripherals::steal() };

    // Configure our output pin, GPIO 22. Begin by bringing IO BANK0 out of
    // reset.
    p.RESETS.reset().modify(|_, w| w.io_bank0().clear_bit());
    while !p.RESETS.reset_done().read().io_bank0().bit() {}

    // Set GPIO22 to be controlled by SIO
    gpio::led_config_io(&p.IO_BANK0, &p.PADS_BANK0, 22);
    // Set GPIO22 to output
    gpio::led_config_output(&p.SIO, 22);

    // Create a task to blink the LED. You could also write this as an `async
    // fn` but we've inlined it as an `async` block for simplicity.
    let blink = core::pin::pin!(async {
        // PeriodicGate is a `lilos` tool for implementing low-jitter periodic
        // actions. It opens once per PERIOD.
        let mut gate = lilos::time::PeriodicGate::from(PERIOD);

        // Loop forever, blinking things. Note that this borrows the device
        // peripherals `p` from the enclosing stack frame.
        loop {
            gpio::led_toggle(&p.SIO, 22);
            gate.next_time().await;
        }
    });

    // Configure the systick timer for 1kHz ticks at the default ROSC speed of
    // _roughly_ 6 MHz.
    lilos::time::initialize_sys_tick(&mut cp.SYST, 6_000_000);
    // Set up and run the scheduler with a single task.
    lilos::exec::run_tasks(
        &mut [blink],           // <-- array of tasks
        lilos::exec::ALL_TASKS, // <-- which to start initially
    )
}

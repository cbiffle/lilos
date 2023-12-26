//! Multi-core example of using `lilos` to blink an LED at varying intervals on
//! the Raspberry Pi Pico board.
//!
//! This starts a task on each core, one which computes a delay, and sends it to
//! the other core via the FIFO, which then uses that delay to blink the LED.
//!
//! It is an adaptation of the `multicore_fifo_blink` example in `rp2040-hal.
//!
//! This demonstrates
//!
//! 1. How to start the `lilos` executor and configure timekeeping.
//! 2. How to perform periodic actions and delays.
//! 3. How to share data between cores using the multicor FIFO
//! 4. How to use a custom lilos timer implementation instead of the default
//!    single-core systick implementation

// We won't be using the standard library.
#![no_std]
// We don't have a conventional `main` (`cortex_m_rt::entry` is different).
#![no_main]

// Pull in a panic handling crate. We have to `extern crate` this explicitly
// because it isn't otherwise referenced in code!
extern crate panic_halt;

// For RP2040, we need to include a bootloader. The general Cargo build process
// doesn't have great support for this, so we included it as a binary constant.
#[link_section = ".boot_loader"]
#[used]
static BOOT: [u8; 256] = rp2040_boot2::BOOT_LOADER_W25Q080;

// How often our blinky task wakes up (1/2 our blink frequency).
const PERIOD: lilos::time::Millis = lilos::time::Millis(500);

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = rp2040_pac::Peripherals::take().unwrap();

    // Configure our output pin, GPIO 25. Begin by bringing IO BANK0 out of
    // reset.
    p.RESETS.reset.modify(|_, w| w.io_bank0().clear_bit());
    while !p.RESETS.reset_done.read().io_bank0().bit() {}

    // Set GPIO25 to be controlled by SIO.
    p.IO_BANK0.gpio[25].gpio_ctrl.write(|w| w.funcsel().sio());
    // Now have SIO configure GPIO25 as an output.
    p.SIO.gpio_oe_set.write(|w| unsafe { w.bits(1 << 25) });

    // Create a task to blink the LED. You could also write this as an `async
    // fn` but we've inlined it as an `async` block for simplicity.
    let blink = core::pin::pin!(async {
        // PeriodicGate is a `lilos` tool for implementing low-jitter periodic
        // actions. It opens once per PERIOD.
        let mut gate = lilos::time::PeriodicGate::from(PERIOD);

        // Loop forever, blinking things. Note that this borrows the device
        // peripherals `p` from the enclosing stack frame.
        loop {
            p.SIO.gpio_out_xor.write(|w| unsafe { w.bits(1 << 25) });
            gate.next_time(&lilos::time::SysTickTimer).await;
        }
    });

    // Configure the systick timer for 1kHz ticks at the default ROSC speed of
    // _roughly_ 6 MHz.
    lilos::time::initialize_sys_tick(&mut cp.SYST, 6_000_000);
    // Set up and run the scheduler with a single task.
    lilos::exec::run_tasks(
        &mut [blink],           // <-- array of tasks
        lilos::exec::ALL_TASKS, // <-- which to start initially
        &lilos::time::SysTickTimer,
    )
}

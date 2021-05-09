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

// How often our blinky task wakes up (1/2 our blink frequency).
const PERIOD: core::time::Duration = core::time::Duration::from_millis(500);

#[cortex_m_rt::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = stm32h7::stm32h743::Peripherals::take().unwrap();

    // Turn on GPIOB. Note the barrier: the H7 is a multi-issue CPU and if we
    // want a specific ordering of memory operations, we have to ask for it.
    p.RCC.ahb4enr.modify(|_, w| w.gpioben().enabled());
    cortex_m::asm::dmb();

    // Configure our output pin, B0.
    p.GPIOB.moder.modify(|_, w| w.moder0().output());

    // Create a task to blink the LED. You could also write this as an `async
    // fn` but we've inlined it as an `async` block for simplicity.
    let blink = async {
        // PeriodicGate is a `lilos` tool for implementing low-jitter periodic
        // actions. It opens once per PERIOD.
        let mut gate = lilos::exec::PeriodicGate::new(PERIOD);

        // Loop forever, blinking things. Note that this borrows the device
        // peripherals `p` from the enclosing stack frame.
        loop {
            p.GPIOB.bsrr.write(|w| w.bs0().set_bit());
            gate.next_time().await;
            p.GPIOB.bsrr.write(|w| w.br0().set_bit());
            gate.next_time().await;
        }
    };
    // Pin our task in place on the stack.
    pin_utils::pin_mut!(blink);

    // Configure the systick timer for 1kHz ticks at 64MHz (the speed the CPU is
    // running at when it leaves reset).
    lilos::time::initialize_sys_tick(&mut cp.SYST, 64_000_000);
    // Set up and run the scheduler with a single task.
    lilos::exec::run_tasks(
        &mut [blink],  // <-- array of tasks
        lilos::exec::ALL_TASKS,  // <-- which to start initially
    )
}

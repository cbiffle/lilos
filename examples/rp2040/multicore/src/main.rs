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

pub mod fifo;
use fifo::AsyncFifo;

use rp_pico as bsp;

use bsp::{hal, hal::pac};
use hal::fugit::ExtU64;
use hal::multicore::{Multicore, Stack};
use hal::Clock;

use core::pin::{pin, Pin};
use cortex_m::peripheral::syst::SystClkSource;
use cortex_m_rt::exception;
use lilos::list::List;

use embedded_hal::digital::v2::ToggleableOutputPin;

type Instant = hal::fugit::Instant<u64, 1, 1_000_000>;

// For RP2040, we need to include a bootloader. The general Cargo build process
// doesn't have great support for this, so we included it as a binary constant.
#[link_section = ".boot_loader"]
#[used]
static BOOT: [u8; 256] = rp2040_boot2::BOOT_LOADER_W25Q080;

static mut CORE1_STACK: Stack<4096> = Stack::new();

fn cpu_core_id() -> u16 {
    hal::Sio::core() as u16
}

fn tick() -> Instant {
    let timer = unsafe { &*pac::TIMER::ptr() };
    Instant::from_ticks(loop {
        let e = timer.timerawh.read().bits();
        let t = timer.timerawl.read().bits();
        let e2 = timer.timerawh.read().bits();
        if e == e2 {
            break ((e as u64) << 32) | (t as u64);
        }
    })
}

/// We mostly just need to not enter an infinite loop, which is what the
/// `cortex_m_rt` does in `DefaultHandler`. But turning systick off until it's
/// needed can save some energy, especially if the reload value is small.
#[exception]
fn SysTick() {
    // Disable the counter, we enable it again when necessary
    // Safety: We are in the SysTick interrupt handler, having been woken up by
    // it, so shouldn't receive another systick interrupt here.
    unsafe {
        let syst = &*cortex_m::peripheral::SYST::PTR;
        const SYST_CSR_TICKINT: u32 = 1 << 1;
        syst.csr.modify(|v| v & !SYST_CSR_TICKINT);
    }
}

fn make_idle_task<'a>(
    core: &'a mut cortex_m::Peripherals,
    timer_list: Pin<&'a List<Instant>>,
    cycles_per_us: u32,
) -> impl FnMut() + 'a {
    // Make it so that `wfe` waits for masked interrupts as well as events --
    // the problem is that the idle-task is called with interrupts disabled (to
    // not have an interrupt fire before we call the idle task but after we
    // check that we should sleep -- for `wfi` it would just wake up).
    // See
    // https://www.embedded.com/the-definitive-guide-to-arm-cortex-m0-m0-wake-up-operation/
    const SEVONPEND: u32 = 1 << 4;
    unsafe {
        core.SCB.scr.modify(|scr| scr | SEVONPEND);
    }

    // 24-bit timer
    let max_sleep_us = ((1 << 24) - 1) / cycles_per_us;
    core.SYST.set_clock_source(SystClkSource::Core);

    move || {
        match timer_list.peek() {
            Some(wake_at) => {
                let now = tick();
                if wake_at > now {
                    let wake_in_us = u64::min(
                        max_sleep_us as u64,
                        (wake_at - now).to_micros(),
                    );
                    let wake_in_ticks = wake_in_us as u32 * cycles_per_us;
                    // Setting zero to the reload register disables systick --
                    // systick is non-zero due to `wake_at > now`
                    core.SYST.set_reload(wake_in_ticks);
                    core.SYST.clear_current();
                    core.SYST.enable_interrupt();
                    core.SYST.enable_counter();
                    // We use `SEV` to signal from the other core that we can
                    // send more data. See also the comment above on SEVONPEND
                    cortex_m::asm::wfe();
                } else {
                    // We just missed a timer, don't idle
                }
            }
            None => {
                // We use `SEV` to signal from the other core that we can send
                // more data. See also the comment above on SEVONPEND
                cortex_m::asm::wfe();
            }
        }
    }
}

struct Timer<'a> {
    timer_list: Pin<&'a List<Instant>>,
}

impl<'a> lilos::time::Timer for Timer<'a> {
    type Instant = Instant;
    fn timer_list(&self) -> Pin<&'a List<Self::Instant>> {
        self.timer_list
    }

    fn now(&self) -> Self::Instant {
        tick()
    }
}

#[bsp::entry]
fn main() -> ! {
    // Check out peripherals from the runtime.
    let core = pac::CorePeripherals::take().unwrap();
    let mut pac = pac::Peripherals::take().unwrap();
    let mut watchdog = hal::Watchdog::new(pac.WATCHDOG);
    let clocks = hal::clocks::init_clocks_and_plls(
        bsp::XOSC_CRYSTAL_FREQ,
        pac.XOSC,
        pac.CLOCKS,
        pac.PLL_SYS,
        pac.PLL_USB,
        &mut pac.RESETS,
        &mut watchdog,
    )
    .ok()
    .unwrap();
    let sys_clk = clocks.system_clock.freq();

    // Make it so that `wfe` waits for masked interrupts as well as events --
    // the problem is that the idle-task is called with interrupts disabled (to
    // not have an interrupt fire before we call the idle task but after we
    // check that we should sleep -- for `wfi` it would just wake up).
    // See
    // https://www.embedded.com/the-definitive-guide-to-arm-cortex-m0-m0-wake-up-operation/
    const SEVONPEND: u32 = 1 << 4;
    unsafe {
        core.SCB.scr.modify(|scr| scr | SEVONPEND);
    }

    let mut sio = hal::Sio::new(pac.SIO);
    let pins = hal::gpio::Pins::new(
        pac.IO_BANK0,
        pac.PADS_BANK0,
        sio.gpio_bank0,
        &mut pac.RESETS,
    );

    let mut led = pins.gpio25.into_push_pull_output();

    let mut mc = Multicore::new(&mut pac.PSM, &mut pac.PPB, &mut sio.fifo);
    let cores = mc.cores();
    let core1 = &mut cores[1];
    let _task = core1.spawn(unsafe { &mut CORE1_STACK.mem }, move || {
        // Because both core's peripherals are mapped to the same address, this
        // is not necessary, but serves as a reminder that core 1 has its own
        // core peripherals
        // See also https://github.com/rust-embedded/cortex-m/issues/149
        let mut core = unsafe { pac::CorePeripherals::steal() };
        let pac = unsafe { pac::Peripherals::steal() };
        let mut sio = hal::Sio::new(pac.SIO);

        lilos::create_list!(timer_list, Instant::from_ticks(0));
        let timer_list = timer_list.as_ref();
        let timer = Timer { timer_list };
        let idle_task = make_idle_task(&mut core, timer_list, sys_clk.to_MHz());

        fifo::reset_read_fifo(&mut sio.fifo);

        // Create a task to blink the LED. You could also write this as an `async
        // fn` but we've inlined it as an `async` block for simplicity.
        let blink = pin!(async {
            // Loop forever, blinking things. Note that this borrows the device
            // peripherals `p` from the enclosing stack frame.
            loop {
                let delay = sio.fifo.read_async().await as u64;
                lilos::time::sleep_for(&timer, delay.millis()).await;
                led.toggle().unwrap();
            }
        });

        lilos::exec::run_tasks_with_idle(
            &mut [blink],           // <-- array of tasks
            lilos::exec::ALL_TASKS, // <-- which to start initially
            &timer,
            1,
            idle_task,
        )
    });

    let compute_delay = pin!(async {
        /// How much we adjust the LED period every cycle
        const INC: i32 = 2;
        /// The minimum LED toggle interval we allow for.
        const MIN: i32 = 0;
        /// The maximum LED toggle interval period we allow for. Keep it reasonably short so it's easy to see.
        const MAX: i32 = 100;
        loop {
            for period in (MIN..MAX).step_by(INC as usize) {
                sio.fifo.write_async(period as u32).await;
            }
            for period in (MIN..MAX).step_by(INC as usize).rev() {
                sio.fifo.write_async(period as u32).await;
            }
        }
    });

    lilos::create_list!(timer_list, Instant::from_ticks(0));
    let timer_list = timer_list.as_ref();
    let timer = Timer { timer_list };

    // Set up and run the scheduler with a single task.
    lilos::exec::run_tasks_with_idle(
        &mut [compute_delay],   // <-- array of tasks
        lilos::exec::ALL_TASKS, // <-- which to start initially
        &timer,
        0,
        // We use `SEV` to signal from the other core that we can send more
        // data. See also the comment above on SEVONPEND
        cortex_m::asm::wfe,
    )
}

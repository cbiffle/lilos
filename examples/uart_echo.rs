//! An example of receiving and retransmitting bytes through a UART on the
//! STM32F4xx.
//!
//! This defaults to using USART2, which is the one easily accessible on my
//! breakout board. Bytes received at 115200 baud will be retransmitted at the
//! same rate. 
//!
//! Wiring:
//! - PA2 is USART2 TX
//! - PA3 is USART2 RX
//! - PD12 is the heartbeat LED.
//!
//! This demonstrates the same stuff included in `blinky`, plus:
//!
//! 1. How to fork a task into multiple child tasks and then re-join.
//! 2. Use of queues to transfer data between concurrent processes (here, acting
//!    as a UART FIFO).
//! 3. Custom interrupt handlers and the use of `Notify`.
//!
//! # Theory of operation
//!
//! Here's what this does:
//!
//! - `main` sets up some hardware and then starts the `lilos` executor with two
//!   root tasks, `heartbeat` and `echo`.
//! - `heartbeat` periodically blinks an LED forever.
//! - `echo` configures USART2, creates a shared queue, and then forks into two
//!   concurrent processes `echo_tx` and `echo_rx`.
//! - `echo_rx` responds to received-data interrupts by copying bytes into the
//!   shared queue.
//! - `echo_tx` wakes when the queue is empty (and the USART's transmit data
//!   register is empty) and stuffs bytes into the USART.
//!
//! Because `lilos` uses `async` for concurrency, the implementation is
//! different from what you might see in a traditional RTOS. Each concurrent
//! process is still written as a straight-line function that loops when needed,
//! but the way they interact is different:
//!
//! - Unrelated tasks (like `heartbeat` and `echo`) are split into state that
//!   lives across `await` points, which is stored separately, and dynamic stack
//!   usage *between* `await` points, which reuses the same stack space. This
//!   means we need less overall stack allocation.
//!
//! - `echo` forking into `echo_tx` and `echo_rx` is quite literal: `echo` turns
//!   itself into two concurrent processes, reusing its resources, including
//!   loaning local variables into the two processes. This is very hard to
//!   do on a conventional RTOS, particularly if you want to do it safely.

#![no_std]
#![no_main]
#![feature(never_type)]

extern crate panic_halt;

use core::mem::MaybeUninit;
use core::time::Duration;
use core::future::Future;

use stm32f4::stm32f407 as device;
use device::interrupt;

use lilos::exec::{Notify, PeriodicGate};
use lilos::spsc;

///////////////////////////////////////////////////////////////////////////////
// Entry point

#[cortex_m_rt::entry]
fn main() -> ! {
    const CLOCK_HZ: u32 = 16_000_000;

    // Check out peripherals from the runtime. The programming model used by the
    // cortex_m crate expects that there's some common init code where this can
    // be done centrally -- so we pretty much have to do it here.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = device::Peripherals::take().unwrap();

    // Create and pin tasks.
    let heartbeat = heartbeat(&p.RCC, &p.GPIOD);
    pin_utils::pin_mut!(heartbeat);
    let echo = usart_echo(
        &p.RCC,
        &p.GPIOA,
        &p.USART2,
        CLOCK_HZ,
    );
    pin_utils::pin_mut!(echo);

    p.RCC.ahb1enr.modify(|_, w| w.gpioden().enabled());
    p.GPIOD.moder.modify(|_, w| w.moder15().output());

    // Set up and run the scheduler.
    lilos::time::initialize_sys_tick(&mut cp.SYST, CLOCK_HZ);
    lilos::exec::run_tasks_with_idle(
        &mut [heartbeat, echo],
        lilos::exec::ALL_TASKS,
        || {
            p.GPIOD.bsrr.write(|w| w.br15().set_bit());
            cortex_m::asm::wfi();
            p.GPIOD.bsrr.write(|w| w.bs15().set_bit());
        },
    )
}

///////////////////////////////////////////////////////////////////////////////
// Task implementations

/// Pulses a GPIO pin connected to an LED, to show that the scheduler is still
/// running, etc.
///
/// Note that this captures only one of the two references it receives.
fn heartbeat<'gpio>(
    rcc: &device::RCC,
    gpiod: &'gpio device::GPIOD,
) -> impl Future<Output = !> + 'gpio {
    // This is implemented using an explicit `async` block, instead of as an
    // `async fn`, to make it clear which actions occur during setup, and which
    // are ongoing. In particular, we only need to borrow the RCC for *setup*
    // and don't need to retain access to it. This distinction is hard (or
    // impossible?) to express with an `async fn`.

    const PERIOD: Duration = Duration::from_millis(500);

    // Configure our output pin.
    rcc.ahb1enr.modify(|_, w| w.gpioden().enabled());
    gpiod.moder.modify(|_, w| w.moder12().output());

    // Set up our timekeeping to capture the current time (not whenever we first
    // get polled). This is usually not important but I'm being picky.
    let mut gate = PeriodicGate::new(PERIOD);

    // Return the task future. We use `move` so that the `gate` is transferred
    // from our stack into the future.
    async move {
        loop {
            gpiod.bsrr.write(|w| w.bs12().set_bit());
            gate.next_time().await;
            gpiod.bsrr.write(|w| w.br12().set_bit());
            gate.next_time().await;
        }
    }
}

/// Initializes `usart` for operation at a fixed rate, and then re-transmits any
/// characters received through it.
async fn usart_echo(
    rcc: &device::RCC,
    gpio: &device::GPIOA,
    usart: &device::USART2,
    clock_hz: u32,
) -> ! {
    const BAUD_RATE: u32 = 115_200;

    // Turn on clock to the USART.
    rcc.apb1enr.modify(|_, w| w.usart2en().enabled());
    // Calculate baud rate divisor for the given peripheral clock. (Using the
    // default 16x oversampling this calculation is pretty straightforward.)
    let cycles_per_bit = clock_hz / BAUD_RATE;
    usart.brr.write(|w| w.div_mantissa().bits((cycles_per_bit >> 4) as u16)
        .div_fraction().bits(cycles_per_bit as u8 & 0xF));
    // Turn on the USART engine, transmitter, and receiver.
    usart.cr1.write(|w| w.ue().enabled()
        .te().enabled()
        .re().enabled());

    // Turn on clock to GPIOA, where our signals emerge.
    rcc.ahb1enr.modify(|_, w| w.gpioaen().enabled());
    // Configure our pins as AF7
    gpio.afrl.modify(|_, w| w.afrl2().af7()
        .afrl3().af7());
    gpio.otyper.modify(|_, w| w.ot2().push_pull()
        .ot3().push_pull());
    gpio.moder.modify(|_, w| w.moder2().alternate()
        .moder3().alternate());

    // Enable the UART interrupt that we'll use to wake tasks.
    // Safety: our ISR (below) is safe to enable at any time -- plus, we're in a
    // future at this point, so interrupts are globally masked.
    unsafe {
        cortex_m::peripheral::NVIC::unmask(device::Interrupt::USART2);
    }

    // Create a data queue for echoed bytes to flow through. While RX and TX
    // operate at the same rate, we can definitely receive a new byte while
    // waiting for the old one to go out, so even doing single-byte echoes it's
    // important to run RX and TX concurrently. (Note that the STM32F4's USART
    // has no hardware FIFO of any kind, just to make our lives difficult. This
    // queue is effectively replacing such a FIFO.)

    // First, storage. We'll put this on the stack as part of our async fn;
    // could also be static.
    let mut q_storage: [MaybeUninit<u8>; 16] = [MaybeUninit::uninit(); 16];
    // Now, the queue structure,
    let mut q = spsc::Queue::new(&mut q_storage);
    // ...and the two handles to it.
    let (q_push, q_pop) = q.split();

    // "Fork" into the rx and tx processes. This is a very convenient way to
    // manage the two sides of the link, but has the caveat that this task will
    // be woken and _both_ will be polled on either tx or rx interrupts (because
    // Notify designates a task, not a future within it). This may not matter
    // for your application.
    //
    // The trailing ".0" here is because we're joining two nonterminating
    // futures, giving type (!, !), which Rust doesn't think is uninhabited --
    // by extracting either one of the !s we prove that code past this point is
    // unreachable.
    futures::future::join(echo_rx(usart, q_push), echo_tx(usart, q_pop)).await.0
}

/// Echo receive task. Moves bytes from `usart` to `q`.
async fn echo_rx(
    usart: &device::USART2,
    mut q: spsc::Push<'_, u8>,
) -> ! {
    loop {
        q.push(recv(usart).await).await;
    }
}

/// Echo transmit task. Moves bytes from `q` to `usart`.
async fn echo_tx(
    usart: &device::USART2,
    mut q: spsc::Pop<'_, u8>,
) -> !  {
    loop {
        send(usart, q.pop().await).await;
    }
}

///////////////////////////////////////////////////////////////////////////////
// Interaction between tasks and ISRs.

/// Notification signal for waking a task from the USART TXE ISR.
static TXE: Notify = Notify::new();

/// Implementation factor of `echo_tx`: sends `c` out `usart`. This will resolve
/// once the USART's transmit holding register has freed up and `c` has been
/// loaded into it.
///
/// This will only work correctly if USART2's interrupt is enabled at the NVIC.
async fn send(usart: &device::USART2, c: u8) {
    usart.cr1.modify(|_, w| w.txeie().enabled());
    TXE.until(|| usart.sr.read().txe().bit()).await;
    usart.dr.write(|w| w.dr().bits(u16::from(c)));
}

/// Notification signal for waking a task from the USART RXE ISR.
static RXE: Notify = Notify::new();

/// Implementation factor of `echo_rx`: reads a byte from `usart`. This will
/// resolve once the USART's receive holding register has become non-empty and
/// we've read the value out.
///
/// This will only work correctly if USART2's interrupt is enabled at the NVIC.
async fn recv(usart: &device::USART2) -> u8 {
    usart.cr1.modify(|_, w| w.rxneie().enabled());
    RXE.until(|| usart.sr.read().rxne().bit()).await;
    usart.dr.read().dr().bits() as u8
}

///////////////////////////////////////////////////////////////////////////////
// Interrupt handlers.

/// Interrupt service routine for poking our two `Notify` objects on hardware
/// events.
#[interrupt]
fn USART2() {
    let usart = unsafe { &*device::USART2::ptr() };
    let cr1 = usart.cr1.read();
    let sr = usart.sr.read();

    // Note: we only honor the condition bits when the corresponding interrupt
    // sources are enabled on the USART, because otherwise they didn't cause
    // this interrupt.

    if cr1.txeie().bit() && sr.txe().bit() {
        TXE.notify();
        usart.cr1.modify(|_, w| w.txeie().disabled());
    }

    if cr1.rxneie().bit() && sr.rxne().bit() {
        RXE.notify();
        usart.cr1.modify(|_, w| w.rxneie().disabled());
    }
}

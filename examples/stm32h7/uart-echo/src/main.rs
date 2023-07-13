//! An example of receiving and retransmitting bytes through a UART on the
//! STM32H7xx.
//!
//! This defaults to using USART3, which is conveniently wired to the "virtual
//! COM port" exposed over USB by the built-in STLink V3 programmer. Bytes
//! received at 115200 baud will be retransmitted at the same rate. 
//!
//! Wiring:
//! - PD8 is USART3 TX
//! - PD9 is USART3 RX
//! - PB0 is the heartbeat LED.
//!
//! This demonstrates the same stuff included in `minimal`, plus:
//!
//! 1. How to fork a task into multiple child tasks and then re-join.
//! 2. Use of queues to transfer data between concurrent processes (here,
//!    supplementing the UART FIFO).
//! 3. Custom interrupt handlers and the use of `Notify`.
//!
//! # Theory of operation
//!
//! Here's what this does:
//!
//! - `main` sets up some hardware and then starts the `lilos` executor with two
//!   root tasks, `heartbeat` and `echo`.
//! - `heartbeat` periodically blinks an LED forever.
//! - `echo` configures USART3, creates a shared queue, and then forks into two
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

extern crate panic_halt;

use core::convert::{Infallible, TryFrom};
use core::mem::MaybeUninit;
use core::pin::pin;
use core::future::Future;

use stm32h7::stm32h743 as device;
use device::interrupt;

use lilos::exec::Notify;
use lilos::spsc;
use lilos::time::{Millis, PeriodicGate};

///////////////////////////////////////////////////////////////////////////////
// Entry point

#[cortex_m_rt::entry]
fn main() -> ! {
    // The H743 comes out of reset at 64MHz, and we don't change that:
    const CLOCK_HZ: u32 = 64_000_000;

    // Check out peripherals from the runtime. The programming model used by the
    // cortex_m crate expects that there's some common init code where this can
    // be done centrally -- so we pretty much have to do it here.
    let mut cp = cortex_m::Peripherals::take().unwrap();
    let p = device::Peripherals::take().unwrap();

    // Create and pin tasks.
    let heartbeat = pin!(heartbeat(&p.RCC, &p.GPIOB));
    let echo = pin!(usart_echo(
        &p.RCC,
        &p.GPIOD,
        &p.USART3,
        CLOCK_HZ,
    ));

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
/// Note that this captures only one of the two references it receives: the task
/// doesn't need the RCC after setup, and doesn't hang on to it.
fn heartbeat<'gpio>(
    rcc: &device::RCC,
    gpiob: &'gpio device::GPIOB,
) -> impl Future<Output = Infallible> + 'gpio {
    // This is implemented using an explicit `async` block, instead of as an
    // `async fn`, to make it clear which actions occur during setup, and which
    // are ongoing. In particular, we only need to borrow the RCC for *setup*
    // and don't need to retain access to it. This distinction is hard (or
    // impossible?) to express with an `async fn`.

    const PERIOD: Millis = Millis(500);

    // Turn on our GPIO port.
    rcc.ahb4enr.modify(|_, w| w.gpioben().enabled());
    cortex_m::asm::dmb();

    // Configure our output pin.
    gpiob.moder.modify(|_, w| w.moder0().output());

    // Set up our timekeeping to capture the current time (not whenever we first
    // get polled). This is usually not important but I'm being picky.
    let mut gate = PeriodicGate::from(PERIOD);

    // Return the task future. We use `move` so that the `gate` is transferred
    // from our stack into the future.
    async move {
        loop {
            gpiob.bsrr.write(|w| w.bs0().set_bit());
            gate.next_time().await;
            gpiob.bsrr.write(|w| w.br0().set_bit());
            gate.next_time().await;
        }
    }
}

/// Initializes `usart` for operation at a fixed rate, and then re-transmits any
/// characters received through it.
///
/// Note that the returned future captures only `usart` -- this shows that it
/// won't mess with `rcc` or `gpio` when polled.
fn usart_echo<'usart>(
    rcc: &device::RCC,
    gpio: &device::GPIOD,
    usart: &'usart device::USART3,
    clock_hz: u32,
) -> impl Future<Output = Infallible> + 'usart {
    const BAUD_RATE: u32 = 115_200;

    // Turn on clock to the peripherals we touch.
    rcc.apb1lenr.modify(|_, w| w.usart3en().enabled());
    rcc.ahb4enr.modify(|_, w| w.gpioden().enabled());
    cortex_m::asm::dmb();

    // Calculate baud rate divisor for the given peripheral clock. (Using the
    // default 16x oversampling this calculation is pretty straightforward.)
    let cycles_per_bit = u16::try_from(clock_hz / BAUD_RATE).unwrap();
    usart.brr.write(|w| w.brr().bits(cycles_per_bit));
    // Turn on the USART engine, transmitter, and receiver.
    usart.cr1.write(|w| w.ue().enabled()
        .te().enabled()
        .re().enabled());

    // Configure our pins (PD8, PD9) as AF7
    gpio.afrh.modify(|_, w| w.afr8().af7()
        .afr9().af7());
    // Ensure they're in push-pull mode
    gpio.otyper.modify(|_, w| w.ot8().push_pull()
        .ot9().push_pull());
    // And mux them to USART3.
    gpio.moder.modify(|_, w| w.moder8().alternate()
        .moder9().alternate());

    async move {
        // Enable the UART interrupt that we'll use to wake tasks.
        // Safety: our ISR (below) is safe to enable at any time -- plus, we're
        // in a future at this point, so interrupts are globally masked.
        unsafe {
            cortex_m::peripheral::NVIC::unmask(device::Interrupt::USART3);
        }

        // Create a data queue for echoed bytes to flow through. While RX and TX
        // operate at the same rate, we can definitely receive a new byte while
        // waiting for the old one to go out, so even doing single-byte echoes
        // it's important to run RX and TX concurrently. The STM32H7 has a
        // hardware FIFO that we're supplementing here.

        // First, storage. We'll put this on the stack as part of our future;
        // could also be static.
        let mut q_storage: [MaybeUninit<u8>; 16] = [MaybeUninit::uninit(); 16];
        // Now, the queue structure,
        let mut q = spsc::Queue::new(&mut q_storage);
        // ...and the two handles to it.
        let (q_push, q_pop) = q.split();

        // "Fork" into the rx and tx processes. This is a very convenient way to
        // manage the two sides of the link, but has the caveat that this task
        // will be woken and _both_ will be polled on either tx or rx interrupts
        // (because Notify designates a task, not a future within it). This may
        // not matter for your application.
        //
        // The trailing ".0" here is because we're joining two nonterminating
        // futures, giving type (!, !), which Rust doesn't think is uninhabited --
        // by extracting either one of the !s we prove that code past this point is
        // unreachable.
        futures::future::join(echo_rx(usart, q_push), echo_tx(usart, q_pop)).await.0
    }
}

/// Echo receive task. Moves bytes from `usart` to `q`.
async fn echo_rx(
    usart: &device::USART3,
    mut q: spsc::Pusher<'_, u8>,
) -> Infallible {
    loop {
        q.reserve().await.push(recv(usart).await);
    }
}

/// Echo transmit task. Moves bytes from `q` to `usart`.
async fn echo_tx(
    usart: &device::USART3,
    mut q: spsc::Popper<'_, u8>,
) -> Infallible  {
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
async fn send(usart: &device::USART3, c: u8) {
    // Enable the TxE interrupt so the ISR will signal the TXE Notify. Because
    // we're using lilos in normal (non-preemptive) mode, the ISR will not fire
    // right away.
    usart.cr1.modify(|_, w| w.txeie().enabled());
    // Block waiting for the TXE Notify to be signaled, which will give the ISR
    // an opportunity to run. Check the TxE bit each time we're awoken to filter
    // out spurious wakes.
    TXE.until(|| usart.isr.read().txe().bit()).await;
    // Now that TxE is set, stuff our byte into the holding register.
    usart.tdr.write(|w| w.tdr().bits(u16::from(c)));
}

/// Notification signal for waking a task from the USART RXNE ISR.
static RXNE: Notify = Notify::new();

/// Implementation factor of `echo_rx`: reads a byte from `usart`. This will
/// resolve once the USART's receive holding register has become non-empty and
/// we've read the value out.
///
/// This will only work correctly if USART2's interrupt is enabled at the NVIC.
async fn recv(usart: &device::USART3) -> u8 {
    // Enable the RxNE interrupt so the ISR will signal the RXNE Notify. Because
    // we're using lilos in normal (non-preemptive) mode, the ISR will not fire
    // right away.
    usart.cr1.modify(|_, w| w.rxneie().enabled());
    // Block waiting for the RXNE Notify to be signaled, which will give the ISR
    // an opportunity to run. Check the RxNE bit each time we're awoken to
    // filter out spurious wakes.
    RXNE.until(|| usart.isr.read().rxne().bit()).await;
    // Now that RxNE is set, pop data out of the holding register.
    usart.rdr.read().rdr().bits() as u8
}

///////////////////////////////////////////////////////////////////////////////
// Interrupt handlers.

/// Interrupt service routine for poking our two `Notify` objects on hardware
/// events.
#[interrupt]
fn USART3() {
    let usart = unsafe { &*device::USART3::ptr() };
    let cr1 = usart.cr1.read();
    let isr = usart.isr.read();

    // Note: we only honor the condition bits when the corresponding interrupt
    // sources are enabled on the USART, because otherwise they didn't cause
    // this interrupt.
    //
    // In each case, we signal the appropriate Notify and disable the interrupt
    // source to prevent it from reoccurring until we ask it to.

    if cr1.txeie().bit() && isr.txe().bit() {
        TXE.notify();
        usart.cr1.modify(|_, w| w.txeie().disabled());
    }

    if cr1.rxneie().bit() && isr.rxne().bit() {
        RXNE.notify();
        usart.cr1.modify(|_, w| w.rxneie().disabled());
    }
}

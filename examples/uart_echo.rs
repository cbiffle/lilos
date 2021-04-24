//! An example of receiving and retransmitting bytes through a UART on the
//! STM32F4xx.
//!
//! This defaults to using USART2, which is the one easily accessible on my
//! breakout board.

#![no_std]
#![no_main]
#![feature(never_type)]

extern crate panic_halt;

use core::mem::MaybeUninit;
use core::time::Duration;
use core::future::Future;
use core::pin::Pin;

use stm32f4::stm32f407 as device;
use device::interrupt;
use lilos::exec::Notify;

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

/// Pulses a GPIO pin connected to an LED, to show that the scheduler is still
/// running, etc.
fn heartbeat<'gpio>(
    rcc: &device::RCC,
    gpiod: &'gpio device::GPIOD,
) -> impl Future<Output = !> + 'gpio {
    // This is implemented using an explicit `async` block, instead of as an
    // `async fn`, to make it clear which actions occur during setup, and which
    // are ongoing. In particular, we only need to borrow the RCC for *setup*
    // and don't need to retain access to it. This distinction is hard (or
    // impossible?) to express with an `async fn`.

    // Configure our output pin.
    rcc.ahb1enr.modify(|_, w| w.gpioden().enabled());
    gpiod.moder.modify(|_, w| w.moder12().output());

    // Set up our timekeeping to capture the current time (not whenever we first
    // get polled). This is usually not important but I'm being picky.
    let mut gate = lilos::exec::PeriodicGate::new(
        Duration::from_millis(500)
    );

    // Return the task future.
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
    // Turn on power to the USART.
    rcc.apb1enr.modify(|_, w| w.usart2en().enabled());
    // Calculate baud rate divisor for the given peripheral clock.
    let cycles_per_bit = clock_hz / 115_200;
    usart.brr.write(|w| w.div_mantissa().bits((cycles_per_bit >> 4) as u16)
        .div_fraction().bits(cycles_per_bit as u8 & 0xF));
    // Turn on the USART engine, transmitter, and receiver.
    usart.cr1.write(|w| w.ue().enabled().te().enabled().re().enabled());

    // Turn on power to GPIOA, where our signals emerge.
    rcc.ahb1enr.modify(|_, w| w.gpioaen().enabled());
    // Configure our pins as AF7
    gpio.afrl.modify(|_, w| w.afrl2().af7().afrl3().af7());
    gpio.otyper.modify(|_, w| w.ot2().push_pull().ot3().push_pull());
    gpio.moder.modify(|_, w| w.moder2().alternate().moder3().alternate());

    // Enable the UART interrupt that we'll use to wake tasks.
    unsafe {
        cortex_m::peripheral::NVIC::unmask(device::Interrupt::USART2);
    }

    // Create a data queue for echoed bytes to flow through. While RX and TX
    // operate at the same rate, we can definitely receive a new byte while
    // waiting for the old one to go out, so even doing single-byte echoes it's
    // important to run RX and TX concurrently. (Note that the STM32F4's USART
    // has no hardware FIFO of any kind, just to make our lives difficult.)
    lilos::create_queue!(q, [MaybeUninit::<u8>::uninit(); 16]);

    // "Fork" into the rx and tx processes. The trailing ".0" here is because
    // we're joining two nonterminating futures, giving type (!, !), which Rust
    // doesn't think is uninhabited -- by extracting one of the !s we prove that
    // code past this point is unreachable.
    futures::future::join(echo_rx(usart, q), echo_tx(usart, q)).await.0
}

/// Echo receive task. Moves bytes from `usart` to `q`.
async fn echo_rx<B>(
    usart: &device::USART2,
    q: Pin<&lilos::queue::Queue<u8, B>>,
) -> !
where B: as_slice::AsMutSlice<Element = MaybeUninit<u8>>,
{
    loop {
        q.push(recv(usart).await).await;
    }
}

/// Echo transmit task. Moves bytes from `q` to `usart`.
async fn echo_tx<B>(
    usart: &device::USART2,
    q: Pin<&lilos::queue::Queue<u8, B>>,
) -> !
where B: as_slice::AsMutSlice<Element = MaybeUninit<u8>>,
{
    loop {
        send(usart, q.pop().await).await;
    }
}

/// Notification signal for waking a task from the USART TXE ISR.
static TXE: Notify = Notify::new();

/// Implementation factor of `echo_tx`: sends `c` out `usart`. This will resolve
/// once the USART's transmit holding register has freed up and `c` has been
/// loaded into it.
///
/// This will only work correctly if USART2's interrupt is enabled at the NVIC.
async fn send(usart: &device::USART2, c: u8) {
    usart.cr1.modify(|_, w| w.txeie().enabled());
    TXE.wait_until(|| usart.sr.read().txe().bit()).await;
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
    RXE.wait_until(|| usart.sr.read().rxne().bit()).await;
    usart.dr.read().dr().bits() as u8
}

/// Interrupt service routine for poking our two `Notify` objects on hardware
/// events.
#[interrupt]
fn USART2() {
    let usart = unsafe { &*device::USART2::ptr() };
    let cr1 = usart.cr1.read();
    let sr = usart.sr.read();

    if cr1.txeie().bit() && sr.txe().bit() {
        TXE.notify();
        usart.cr1.modify(|_, w| w.txeie().disabled());
    }

    if cr1.rxneie().bit() && sr.rxne().bit() {
        RXE.notify();
        usart.cr1.modify(|_, w| w.rxneie().disabled());
    }
}

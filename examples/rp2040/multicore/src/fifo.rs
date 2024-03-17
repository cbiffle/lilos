//! An async wrapper around the RP2040 FIFO, for lilos

use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

use rp_pico as bsp;

use bsp::{hal, hal::pac};
use hal::sio::SioFifo;
use pac::interrupt;

use lilos::exec::Notify;

use pin_project_lite::pin_project;

static CORE_CAN_SEND: [Notify; 2] = [Notify::new(), Notify::new()];
static CORE_CAN_READ: [Notify; 2] = [Notify::new(), Notify::new()];

/// Reset FIFO to make sure any previous error conditions have been cleared.
/// Only the read FIFO needs to be reset, so if you are only sending messages
/// from core 0 to core 1 then you only need to do the reset on core 1
pub fn reset_read_fifo(fifo: &mut hal::sio::SioFifo) {
    fifo.drain();
    // Currently no functionality to clear ROE/WOF in RP2040-HAL, but we own the
    // mutable reference to it anyway
    unsafe { &(*pac::SIO::ptr()) }.fifo_st.reset();
}

pin_project! {
    pub struct ReadFut<'a> {
        fifo: &'a mut SioFifo,
        core: u16,
        _marker: lilos::util::NotSendMarker,
    }
}

pin_project! {
    pub struct WriteFut<'a> {
        fifo: &'a mut SioFifo,
        value: u32,
        core: u16,
        _marker: lilos::util::NotSendMarker,
    }
}

pub trait AsyncFifo {
    fn read_async(&mut self) -> ReadFut;
    fn write_async(&mut self, value: u32) -> WriteFut;
}

impl AsyncFifo for hal::sio::SioFifo {
    /// Reads a value from the FIFO, asynchronously
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict.
    fn read_async(&mut self) -> ReadFut {
        let core = crate::cpu_core_id();
        ReadFut {
            fifo: self,
            core,
            _marker: Default::default(),
        }
    }

    /// Writes a value to the FIFO, asynchronously
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict, as `u32` is `Copy` so the value isn't moved.
    fn write_async(&mut self, value: u32) -> WriteFut {
        let core = crate::cpu_core_id();
        WriteFut {
            fifo: self,
            value,
            core,
            _marker: Default::default(),
        }
    }
}

impl Future for ReadFut<'_> {
    type Output = u32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let core = self.core as usize;
        match self.project().fifo.read() {
            Some(value) => {
                CORE_CAN_SEND[1 - core].notify();
                cortex_m::asm::sev();
                Poll::Ready(value)
            }
            None => {
                // Start listening to SIO FIFO IRQs
                // This is in interrupt free, because (if we are using
                // preemption) we could get an interrupt right after unmasking
                // it, but before subscribing, so we wouldn't be woken up
                cortex_m::interrupt::free(|_| {
                    unsafe {
                        use pac::Interrupt::{SIO_IRQ_PROC0, SIO_IRQ_PROC1};
                        pac::NVIC::unmask([SIO_IRQ_PROC0, SIO_IRQ_PROC1][core]);
                    }
                    CORE_CAN_READ[core].subscribe(cx.waker());
                });
                Poll::Pending
            }
        }
    }
}

impl Future for WriteFut<'_> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let core = self.core as usize;
        let value = self.value;
        let p = self.project();
        if p.fifo.is_write_ready() {
            p.fifo.write(value);
            Poll::Ready(())
        } else {
            CORE_CAN_SEND[core].subscribe(cx.waker());
            Poll::Pending
        }
    }
}

/// IRQ handler for core 0 inter-process mailbox/FIFO
/// Triggered on:
/// - VLD (Fifo contains valid data -- cleared when it is empty)
/// - ROE (Read on empty)
/// - WOF (Write on full)
#[interrupt]
fn SIO_IRQ_PROC0() {
    let fifo_status = unsafe { &(*pac::SIO::ptr()) }.fifo_st.read();
    if fifo_status.roe().bit_is_set() || fifo_status.wof().bit_is_set() {
        panic!(
            "On core 0 FIFO in bad state, indicating firmware bug in this module, FIFO state {}",
            fifo_status.bits(),
        );
    } else if fifo_status.vld().bit_is_set() {
        CORE_CAN_READ[0].notify();
        // If we are not actively reading *here* then the interrupt
        // will just fire again, so we disable it here and re-enable
        // it before subscribing to the notify.
        pac::NVIC::mask(pac::Interrupt::SIO_IRQ_PROC0);
    }
}

/// IRQ handler for core 1 inter-process mailbox/FIFO
/// Triggered on:
/// - VLD (Fifo contains valid data -- cleared when it is empty)
/// - ROE (Read on empty)
/// - WOF (Write on full)
#[interrupt]
fn SIO_IRQ_PROC1() {
    let fifo_status = unsafe { &(*pac::SIO::ptr()) }.fifo_st.read();
    if fifo_status.roe().bit_is_set() || fifo_status.wof().bit_is_set() {
        panic!(
            "On core 1 FIFO in bad state, indicating firmware bug in this module, FIFO state {}",
            fifo_status.bits(),
        );
    } else if fifo_status.vld().bit_is_set() {
        CORE_CAN_READ[1].notify();
        // If we are not actively reading *here* then the interrupt
        // will just fire again, so we disable it here and re-enable
        // it before subscribing to the notify.
        pac::NVIC::mask(pac::Interrupt::SIO_IRQ_PROC1);
    }
}

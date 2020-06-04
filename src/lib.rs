//! A simple RTOS based around Rust `Future`s.
//!
//! This provides a minimal operating environment for running async Rust code on
//! ARM Cortex-M microprocessors, plus some useful doodads and gizmos.
//!
//! # About the OS
//!
//! This OS is designed around the notion of a fixed set of concurrent tasks
//! that run forever. To use the OS, your application startup routine calls
//! [`exec::run_tasks`], giving it an array of tasks you've defined; `run_tasks`
//! never returns.
//!
//! The OS provides *cooperative* multitasking: while tasks are concurrent, they
//! are not preemptive, and are not "threads" in the traditional sense. Tasks
//! don't even have their own stacks -- they return completely whenever they
//! yield the CPU.
//!
//! This would be incredibly frustrating to program, were it not for `Future`
//! and `async`.
//!
//! Each task co-routine has the type `Future<Output = !>`, meaning a `Future`
//! that can be polled but will never complete (because, remember, tasks run
//! forever). The OS provides an *executor* that manages polling of a set of
//! `Future`s.
//!
//! Rust's `async` keyword provides a convenient way to have the compiler
//! rewrite a normal function into a co-routine-style `Future`. This means that
//! writing co-routines to run on the OS looks *very much* like programming with
//! threads.
//!
//! Here is the "hello world" of embedded programming, written as a task for
//! this OS. This task blinks an LED attached to port D12 of an STM32F4.
//!
//! ```ignore
//! async fn blinky(gpio: &GPIOD) -> ! {
//!     const PERIOD: Duration = Duration::from_millis(500);
//!
//!     loop {
//!         gpio.bsrr.write(|w| w.bs12().set_bit());
//!         os::exec::sleep_for(PERIOD).await;
//!         gpio.bsrr.write(|w| w.br12().set_bit());
//!         os::exec::sleep_for(PERIOD).await;
//!     }
//! }
//! ```
//!
//! # Concurrency and interrupts
//!
//! The OS supports the use of interrupt handlers to wake tasks through the
//! [`Notify`][exec::Notify] mechanism, but most OS facilities are not available
//! in interrupt context.
//!
//! When task code is running, interrupts are masked, so tasks can be confident
//! that they will not be preempted unless they `await`.
//!
//! Each time through the task polling loop, the OS unmasks interrupts to let
//! any pending interrupts run. Because the Cortex-M collects pending interrupts
//! while interrupts are masked, we don't run the risk of missing events.
//!
//! Interrupts are also unmasked whenever the idle processor is woken from
//! sleep, in order to handle the event that woke it up.
//!
//! # Cancellation
//!
//! Co-routine tasks in this OS are just `Future`s, which means they can be
//! dropped. `Future`s are typically dropped just after they resolve (often just
//! after an `await` keyword), but it's also possible to drop a `Future` while
//! it is pending. This can happen explicitly (by calling [`drop`]), or as a
//! side effect of other operations; for example, the future returned by
//! [`select!`](https://docs.rs/futures/0.3/futures/macro.select.html) will drop
//! any incompleted futures if you `await` it.
//!
//! This means it's useful to consider what cancellation *means* for any
//! particular task, and to ensure that its results are what you intend.

#![no_std]
#![feature(never_type)]

#[macro_use]
pub mod list;
pub mod exec;
pub mod mutex;
pub mod queue;
pub mod time;

use core::marker::PhantomData;

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Sync` (i.e. safe for sharing across threads).
///
/// A type that includes this may still be inferred as `Send`.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct NotSyncMarker(PhantomData<core::cell::Cell<()>>);

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Send` (i.e. safe for transfer across threads).
///
/// This also blocks `Sync`.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct NotSendMarker(PhantomData<*const ()>);

trait FromNever {
    type Output;

    fn from_never(self) -> Self::Output;
}

impl FromNever for core::task::Poll<!> {
    type Output = ();

    fn from_never(self) -> Self::Output {
        match self {
            core::task::Poll::Pending => (),
            core::task::Poll::Ready(never) => match never {},
        }
    }
}

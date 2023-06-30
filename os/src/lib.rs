//! A simple `async` RTOS based around Rust `Future`s.
//!
//! This provides a minimal operating environment for running async Rust code on
//! ARM Cortex-M microprocessors, plus some useful doodads and gizmos.
//!
//! # `lilos` design principles
//!
//! 1. Be compact. Avoid doing things that increase the minimum size of a useful
//!    application. In particular, try to avoid designing APIs that need
//!    internal asserts/panics, because those are quite costly in text size.
//!
//! 2. No magic. `lilos` doesn't use proc macros or other tricks to hide what
//!    it's doing. Some (normal) macros are available, but only as shorthand,
//!    and we'll explain how to do the thing without the macros. This is
//!    important, both for transparency, but also because you might need to
//!    customize what's happening, and you can't do that if we hide it in a box.
//!
//! 3. Be portable. `lilos` doesn't depend on any vendor-specific hardware, and
//!    can run on any ARM Cortex-M processor. This means you don't need to wait
//!    for `lilos` to be ported to your processor. (`lilos` is also not
//!    inherently ARM-specific -- I just don't have a lot of non-ARM dev
//!    hardware. Suggestions welcome!)
//!
//! 4. Be predictable. `lilos` doesn't use dynamic memory allocation, and the
//!    task polling behavior is well-defined in the executor. While you can
//!    certainly build unpredictable programs on top of `lilos`, we want to give
//!    you a solid predictable foundation.
//!
//! # About the OS
//!
//! `lilos` is designed around the notion of a fixed set of concurrent tasks
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
//! Each task co-routine must be a `Future` that can be polled but will never
//! complete (because, remember, tasks run forever). The OS provides an
//! *executor* that manages polling of a set of `Future`s.
//!
//! Rust's `async` keyword provides a convenient way to have the compiler
//! rewrite a normal function into a co-routine-style `Future`. This means that
//! writing co-routines to run on this OS looks *very much* like programming
//! with threads.
//!
//! Here is the "hello world" of embedded programming, written as a task for
//! this OS. This task blinks an LED attached to port D12 of an STM32F4.
//!
//! ```ignore
//! async fn blinky(gpio: &GPIOD) -> Infallible {
//!     const PERIOD: Duration = Duration::from_millis(500);
//!
//!     loop {
//!         gpio.bsrr.write(|w| w.bs12().set_bit());
//!         lilos::exec::sleep_for(PERIOD).await;
//!         gpio.bsrr.write(|w| w.br12().set_bit());
//!         lilos::exec::sleep_for(PERIOD).await;
//!     }
//! }
//! ```
//!
//! (Note: the natural way to write that function would be with a return type of
//! `!`, but doing this requires the unstable toolchain, so we rely on
//! `core::convert::Infallible` instead in this version.)
//!
//! # Composition and dynamic behavior
//!
//! The notion of a fixed set of tasks might seem limiting, but it's more
//! flexible than you might expect. Because `Future`s can be _composed_, the
//! fixed set of OS tasks can drive a _dynamic_ set of program `Future`s.
//!
//! For instance, a task can fork into several concurrent routines using macros
//! like [`select_biased!`] or [`join!`] from the `futures` crate.
//!
//! # Concurrency and interrupts
//!
//! The OS supports the use of interrupt handlers to wake tasks through the
//! [`Notify`][exec::Notify] mechanism, but most OS facilities are not available
//! in interrupt context.
//!
//! By default, interrupts are masked when task code is running, so tasks can be
//! confident that they will preempted if, and only if, they `await`.
//!
//! Each time through the task polling loop, the OS unmasks interrupts to let
//! any pending interrupts run. Because the Cortex-M collects pending interrupts
//! while interrupts are masked, we don't run the risk of missing events.
//!
//! Interrupts are also unmasked whenever the idle processor is woken from
//! sleep, in order to handle the event that woke it up.
//!
//! If your application requires tighter interrupt response time, you can
//! configure the OS at startup to permit preemption of various kinds --
//! including allowing preemption by only a subset of your interrupts. See the
//! [`exec`][crate::exec] module for more details and some customization
//! options.
//!
//! # Cancellation
//!
//! Co-routine tasks in this OS are just `Future`s, which means they can be
//! dropped. `Future`s are typically dropped just after they resolve (often just
//! after an `await` keyword in the calling code), but it's also possible to
//! drop a `Future` while it is pending. This can happen explicitly (by calling
//! [`drop`]), or as a side effect of other operations; for example, the macro
//! [`select_biased!`] waits for one future to resolve, and then drops the
//! others, whether they're done or not.
//!
//! This means it's useful to consider what cancellation *means* for any
//! particular task, and to ensure that its results are what you intend. There's
//! more about this in [The Intro Guide] and the technical note on
//! [Cancellation].
//!
//! `lilos` itself tries to make it easier for you to handle cancellation in
//! your programs, by providing APIs that have reasonable behavior on cancel.
//! Specifically,
//!
//! - Wherever possible, `lilos` futures strive for a _strict_ definition of
//!   cancel-safety, where dropping a future and retrying the operation that
//!   produced it is equivalent to not dropping the future, in terms of visible
//!   side effects. (Obviously doing more work will take more CPU cycles; that's
//!   not what we mean by side effects.)
//!
//! - Where that is not possible (in a few corner-case APIs) `lilos` will
//!   provide _weak_ cancel-safety, where the behavior of the operation at
//!   cancellation is well-defined and documented.
//!
//! Over time, we're trying to redesign APIs to move things out of the second
//! category into the first, with the goal of providing a fully cancel-safe OS
//! API. As far as we can tell nobody's ever done this before, so it might take
//! a bit. If you have suggestions or ideas, please file an issue!
//!
//! [`select_biased!`]: https://docs.rs/futures/latest/futures/macro.select_biased.html
//! [`join!`]: https://docs.rs/futures/latest/futures/macro.join.html
//! [The Intro Guide]: https://github.com/cbiffle/lilos/blob/main/doc/intro.adoc
//! [Cancellation]: https://github.com/cbiffle/lilos/blob/main/doc/cancellation.adoc

#![no_std]

#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    missing_debug_implementations,
    missing_docs,
    semicolon_in_expressions_from_macros,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_qualifications,
)]

/// Internal assert macro that doesn't stringify its expression or generate any
/// fancy messages. This means failures must be diagnosed by file:line only, so,
/// don't use this more than once on the same line. In exchange, this makes
/// asserts significantly smaller in terms of text size.
macro_rules! cheap_assert {
    ($x:expr) => {
        if !$x { panic!(); };
    }
}
pub(crate) use cheap_assert;

#[macro_use]
pub mod list;
pub mod exec;
#[cfg(feature = "systick")]
pub mod time;

#[cfg(feature = "mutex")]
pub mod mutex;
#[cfg(feature = "spsc")]
pub mod spsc;
#[cfg(feature = "handoff")]
pub mod handoff;

pub mod atomic;

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

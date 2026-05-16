// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A simple but powerful `async` RTOS based around Rust `Future`s.
//!
//! This provides a lightweight operating environment for running async Rust
//! code on ARM Cortex-M microprocessors, plus some useful doodads and gizmos.
//!
//! `lilos` is deliberately designed to be compact, to avoid the use of proc
//! macros, to be highly portable to different microcontrollers, and to be as
//! statically predictable as possible with no dynamic resource allocation.
//!
//! These are the API docs for the OS. If you'd like a higher-level introduction
//! with worked examples, please have a look at [the intro guide]!
//!
//! [the intro guide]: https://github.com/cbiffle/lilos/blob/main/doc/intro.adoc
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
//! For detailed discussion and some cookbook examples, see either [the intro
//! guide] or [the `examples` directory in the repo][examples].
//!
//! [examples]: https://github.com/cbiffle/lilos/tree/main/examples
//!
//!
//! # Feature flags
//!
//! `lilos` currently exposes the following Cargo features for
//! enabling/disabling portions of the system:
//!
//! - `systick` (on by default). Enables reliance on the ARM M-profile SysTick
//!   timer for portable timekeeping. Disabling makes the executor smaller at
//!   the cost of losing all `time` API. On platforms where the SysTick timer
//!   stops during sleep, such as Nordic nRF52, you may want to disable this
//!   feature and use a different timekeeping mechanism.
//!
//! - `mutex` (on by default). Enables access to the [`mutex`] module for
//!   blocking access to shared data. Leaving this feature enabled has no cost
//!   if you're not actually using `mutex`.
//!
//! - `spsc` (on by default). Enables access to the [`spsc`] module for
//!   single-producer single-consumer inter-task queues. Leaving this feature
//!   enabled has no cost if you're not actually using `spsc`.
//!
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
//! [`exec`] module for more details and some customization options.
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
//! All of the core APIs aim for _strict_ cancel-safety, where dropping a future
//! and retrying the operation that produced it is equivalent to not dropping
//! the future, in terms of visible side effects. (Obviously doing more work
//! will take more CPU cycles; that's not what we mean by side effects.)
//!
//! If some code is useful, but can't achieve strict cancel safety, it should go
//! in a separate crate. For example, the `lilos-handoff` crate _used to_ be
//! part of the core OS, but was evicted because it can only achieve a weaker
//! notion of cancel safety.
//!
//! Any deviations from this principle are considered bugs, and should be
//! reported if you notice them!
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
#![warn(clippy::undocumented_unsafe_blocks)]

/// Internal assert macro that doesn't stringify its expression or generate any
/// fancy messages. This means failures must be diagnosed by file:line only, so,
/// don't use this more than once on the same line. In exchange, this makes
/// asserts significantly smaller in terms of text size.
#[cfg(any(debug_assertions, feature = "systick"))]
macro_rules! cheap_assert {
    ($x:expr) => {
        if !$x { panic!(); };
    }
}

pub mod exec;
#[deprecated(since = "1.3.0", note = "please use the portable-atomic crate")]
#[cfg(target_arch = "arm")]
pub mod atomic;
pub mod util;

#[macro_use]
#[deprecated(since = "1.2.0", note = "please move to the lilos-list crate")]
pub mod list;

#[cfg(feature = "systick")]
pub mod time;
#[cfg(all(feature = "systick", any(target_arch = "riscv64", target_arch = "riscv32")))]
pub mod clint;
#[cfg(all(feature = "systick", target_arch = "arm"))]
pub mod cortex_m_timer;


#[cfg(feature = "mutex")]
pub mod mutex;
#[cfg(feature = "spsc")]
pub mod spsc;

#[doc(hidden)]
pub use portable_atomic;

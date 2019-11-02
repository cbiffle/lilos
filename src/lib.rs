//! A simple RTOS based around Rust `Future`s.
//!
//! This provides the minimal operating environment for running async Rust code
//! on ARM Cortex-M microprocessors, plus some useful doodads and gizmos.

#![no_std]
#![feature(never_type)]

#[macro_use] pub mod list;
pub mod time;
pub mod exec;
pub mod mutex;

use core::marker::PhantomData;

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Sync` (i.e. safe for sharing across threads).
///
/// A type that includes this may still be inferred as `Send`.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NotSyncMarker(PhantomData<core::cell::Cell<()>>);

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Send` (i.e. safe for transfer across threads).
///
/// This also blocks `Sync`.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NotSendMarker(PhantomData<*const ()>);

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

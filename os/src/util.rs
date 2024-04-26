//! Utility code for use by applications.
//!
//! Like `atomic`, this module exposes odds and ends that might be useful for
//! applications. Unlike `atomic`, it's not particularly focused on a single
//! topic.

use core::{future::Future, pin::Pin, task::{Context, Poll}};
use core::marker::PhantomData;

use pin_project::{pin_project, pinned_drop};

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Sync` (i.e. safe for sharing across threads).
///
/// A type that includes this may still be inferred as `Send`. If that's a
/// problem, see [`NotSendMarker`].
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NotSyncMarker(PhantomData<core::cell::Cell<()>>);

/// Zero-sized marker type that can be included to ensure that a data structure
/// is not automatically made `Send` (i.e. safe for transfer across threads).
///
/// This also blocks `Sync`.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NotSendMarker(PhantomData<*const ()>);

/// Marker trait implementing the "Captures Trick" from Rust RFC 3498, ensuring
/// that we do lifetime capturing right in the 2021 edition.
///
/// TODO: revisit this when we can switch to the 2024 edition, where the default
/// behavior makes this less necessary.
pub trait Captures<T> {}

impl<U: ?Sized, T> Captures<T> for U {}

/// Extension trait for `Future` that adds common utility operations.
///
/// This is intended to complement the `futures` crate and reduce the number of
/// dependencies a typical application needs to pull in. It's
/// blanket-implemented for any type that implements `Future`.
///
/// If you `use` both `futures::future::FutureExt` and `lilos::util::FutureExt`
/// in the same module, you'll get a compile error because you can't have two
/// things in scope both named `FutureExt`. The easiest way to resolve this is
/// to bring the trait operations into scope _without bringing the trait
/// itself,_ using this syntax:
///
/// ```ignore
/// use lilos::util::FutureExt as _;
/// ```
pub trait FutureExt {
    /// Wraps this future such that `action` will be called if it is dropped
    /// before it resolves.
    fn on_cancel<A>(self, action: A) -> OnCancel<Self, A>
        where A: FnOnce(),
              Self: Sized,
    {
        OnCancel {
            inner: self,
            action: Some(action),
        }
    }
}

impl<F: Future> FutureExt for F {}

/// Future wrapper that adds a cancel action (result of [`FutureExt::on_cancel`]).
#[must_use = "futures do nothing unless you `.await` or poll them"]
#[derive(Debug)]
#[pin_project(PinnedDrop)]
pub struct OnCancel<F, A>
    where A: FnOnce(),
{
    #[pin]
    inner: F,
    action: Option<A>,
}

#[pinned_drop]
impl<F, A> PinnedDrop for OnCancel<F, A>
    where A: FnOnce(),
{
    fn drop(self: Pin<&mut Self>) {
        if let Some(a) = self.project().action.take() {
            a();
        }
    }
}

impl<F, A> Future for OnCancel<F, A>
    where F: Future,
          A: FnOnce() + Unpin,
{
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let inner = self.as_mut().project().inner;
        let result = inner.poll(cx);
        if result.is_ready() {
            // Disarm the cancel handler.
            //
            // Safety: this is structural non-pinned projection of the `action`
            // field; same argument as above.
            unsafe { Pin::get_unchecked_mut(self) }.action = None;
        }
        result
    }
}

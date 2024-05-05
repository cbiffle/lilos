// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Mechanism for handing data from one task to another, minimizing copies.
//!
//! This crate provides the `Handoff` abstraction for `lilos`.
//!
//! There are two sides to a `Handoff<T>`, the sender and the receiver. When both
//! the sender and receiver are ready, a single `T` gets transferred from the
//! sender's ownership to the receiver's. In this case, "ready" means that
//! either the sender or receiver was already blocked waiting for its peer when
//! that peer arrived -- with both tasks waiting at the handoff, we can copy the
//! data and then unblock both.
//!
//! Because we don't need any sort of holding area for a copy of the `T`, a
//! `Handoff<T>` is very small -- about the size of two pointers.
//!
//! In computer science this is referred to as a _rendezvous_, but that's harder
//! to spell than handoff.
//!
//! # Creating and using a `Handoff`
//!
//! Because the `Handoff` itself contains no storage, they're cheap to create on
//! the stack. You then need to `split` then into their `Pusher` and `Popper`
//! ends -- these both _borrow_ the `Handoff`, so you need to keep it around.
//! You can then hand the ends off to other futures. A typical use case looks
//! like this:
//!
//! ```ignore
//! let mut handoff = Handoff::new();
//! let (push, pop) = handoff.split();
//! join!(data_producer(push), data_consumer(pop));
//! ```
//!
//! If you just want to synchronize two tasks at a rendezvous point, and don't
//! need to move data, use `Handoff<()>`. It does the right thing.
//!
//! # Caveats and alternatives
//!
//! Only one `Pusher` and `Popper` can exist at a time -- the compiler ensures
//! this.  This simplifies the implementation quite a bit, but it means that if
//! you want a multi-party rendezvous this isn't the right tool.
//!
//! If you would like to be able to push data and go on about your business
//! without waiting for it to be popped, you want a queue, not a handoff. See
//! the `lilos::spsc` module.
//!
//! Note that none of these types are `Send` or `Sync` -- they are very much not
//! thread safe, so they can be freely used across `async` tasks but cannot be
//! shared with an interrupt handler. For the same reason, you probably don't
//! want to attempt to store one in a `static` -- you will succeed with enough
//! `unsafe`, but the result will not be useful! The queues provided in `spsc`
//! do not have this limitation, at the cost of being more work to set up.
//!
//! # Cancel safety
//!
//! `Handoff` is not strictly cancel-safe, unlike most of `lilos`. Concretely,
//! dropping a `push` or `pop` future before it resolves can cause the loss of
//! at most one data item.
//!
//! While technically cancel-unsafe, this is usually okay given the way handoffs
//! are used in practice. Please read the docs for [`Pusher::push`] and
//! [`Popper::pop`] carefully or you risk losing data.
//!
//! If the push and pop ends of the handoff are "long-lived," held by tasks that
//! won't be cancelled (such as top-level tasks in `lilos`) and never used in
//! contexts where the future might be cancelled (such as `with_timeout`), then
//! you don't need to worry about that. This is not a property you can check
//! with the compiler, though, so again -- be careful.

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

use core::cell::Cell;
use core::ptr::NonNull;

use scopeguard::ScopeGuard;

use lilos::exec::Notify;

/// Shared control block for a `Handoff`. See the module docs for more
/// information.
#[derive(Default)]
pub struct Handoff<T> {
    state: Cell<State<T>>,
    ping: Notify,
}

impl<T> Handoff<T> {
    /// Creates a new Handoff in idle state.
    pub const fn new() -> Self {
        Self {
            state: Cell::new(State::Idle),
            ping: Notify::new(),
        }
    }

    /// Borrows `self` exclusively and produces `Pusher` and `Popper` endpoints.
    /// The endpoints are guaranteed to be unique, since they can't be cloned
    /// and you can't call `split` to make new ones until both are
    /// dropped/forgotten.
    pub fn split(&mut self) -> (Pusher<'_, T>, Popper<'_, T>) {
        (Pusher(self), Popper(self))
    }
}

impl<T> Drop for Handoff<T> {
    fn drop(&mut self) {
        // It should be impossible to drop a Handoff while anyone is waiting on
        // it, but let's check.
        debug_assert!(matches!(self.state.get(), State::Idle));
    }
}

/// Implement Debug by hand so it doesn't require T: Debug.
impl<T> core::fmt::Debug for Handoff<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Handoff")
            .field("state", &self.state)
            .field("ping", &self.ping)
            .finish()
    }
}

/// Internal representation of handoff state.
///
/// Note that we store pointers to the inside of the futures. This is OK because
/// they're only stored during `poll`, which in turn can only be called on a
/// pinned future. So we know the futures cannot move without being dropped, and
/// thus the pointers will remain valid (the futures take care to reset these
/// pointers on drop).
#[derive(Default)]
enum State<T> {
    /// Nobody's waiting.
    #[default]
    Idle,
    /// Push side is blocked, and here is a pointer to the value they're
    /// offering. (The `Option` will be `Some(value)`, and to pop you must reset
    /// it to `None` and then write the state to `Idle`.)
    PushWait(NonNull<Option<T>>),
    /// Pop side is blocked, and here is a pointer to the buffer where a value
    /// shall be deposited. (The `Option` will be `None`, and to push you must
    /// set it to `Some(value)` and then write the state to `Idle`.)
    PopWait(NonNull<Option<T>>),
}

/// Implement Debug by hand so it doesn't require T: Debug.
impl<T> core::fmt::Debug for State<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Idle => f.write_str("Idle"),
            Self::PushWait(p) => f.debug_tuple("PushWait").field(p).finish(),
            Self::PopWait(p) => f.debug_tuple("PopWait").field(p).finish(),
        }
    }
}

// Manually deriving Copy and Clone so they don't require T: Copy/Clone.
impl<T> Copy for State<T> {}
impl<T> Clone for State<T> {
    fn clone(&self) -> Self {
        *self  // thanks, Copy impl!
    }
}

/// Push endpoint for a `Handoff<T>`. Holding this allows you to offer a single
/// item at a time to whoever's holding the `Popper` side.
pub struct Pusher<'a, T>(&'a Handoff<T>);

impl<T> Pusher<'_, T> {
    /// Offers `value` to our peer, if they are waiting to receive it.
    ///
    /// If someone is blocked on the `Popper` side, `value` is transferred to
    /// them, they are unblocked, and this returns `Ok(())`.
    ///
    /// Otherwise, it returns `Err(value)`, giving `value` back to you.
    pub fn try_push(&mut self, value: T) -> Result<(), T> {
        match self.0.state.get() {
            State::PopWait(dest_ptr) => {
                // Our peer is waiting.
                unsafe {
                    dest_ptr.as_ptr().write(Some(value));
                }
                self.0.state.set(State::Idle);
                self.0.ping.notify();
                Ok(())
            },
            #[cfg(debug_assertions)]
            State::PushWait(_) => panic!(),
            _ => Err(value),
        }
    }

    /// Produces a future that resolves when `value` can be handed off to our
    /// peer.
    ///
    /// # Cancellation
    ///
    /// **Cancel Safety:** Weak.
    ///
    /// If this future is dropped before it resolves, `value` is dropped, i.e.
    /// both you and the peer lose access to it. This means the operation can't
    /// reasonably be retried, and means that if collecting `value` in the first
    /// place had side effects, there's no good way to roll those back.
    ///
    /// If the code using `push` can hang on to a copy of `value`, or if losing
    /// `value` on cancellation is okay, then this operation _can_ be used
    /// safely.
    ///
    /// I'm trying to figure out a version of this with strict safety.
    /// Suggestions welcome.
    pub async fn push(&mut self, value: T) {
        let mut guard = scopeguard::guard(Some(value), |v| {
            if v.is_some() {
                // Cancelled while waiting to push! We know that...
                // - We have been polled at least once (or we wouldn't be here)
                // - All paths to await in this function set the state to
                //   PushWait.
                // - If the peer sets the state to something other than
                //   PushWait, they take the value.
                // - Thus the current state is...
                debug_assert!(matches!(self.0.state.get(), State::PushWait(_)));
                // ...and we want to eliminate the suggestion that a pusher is
                // waiting.
                self.0.state.set(State::Idle);
            }
        });
        loop {
            if guard.is_some() {
                // Value has not yet been taken. What can we do about that?
                match self.0.state.get() {
                    State::Idle => {
                        // Our peer is not waiting, we must block.
                        self.0.state.set(State::PushWait(
                            NonNull::from(&mut *guard)
                        ));
                        self.0.ping.until_next().await;
                        continue;
                    }
                    State::PushWait(_) => {
                        // We are already blocked; spurious wakeup.
                        self.0.ping.until_next().await;
                        continue;
                    }
                    State::PopWait(dest_ptr) => {
                        // Our peer is waiting. We can do the handoff
                        // immediately. Defuse the guard.
                        unsafe {
                            dest_ptr.as_ptr().write(ScopeGuard::into_inner(guard));
                        }
                        self.0.state.set(State::Idle);
                        self.0.ping.notify();
                        return;
                    },
                }
            } else {
                // Value must have been taken while we were sleeping.
                // Pop side should have left state in either of....
                debug_assert!(matches!(self.0.state.get(), State::Idle | State::PopWait(_)));
                break;
            }
        }
    }
}

/// Implement Debug by hand so it doesn't require T: Debug.
impl<T> core::fmt::Debug for Pusher<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Pusher").field(&self.0).finish()
    }
}

/// Pop endpoint for a `Handoff<T>`. Holding this allows you to take a single
/// item at a time from whoever's holding the `Pusher` side.
pub struct Popper<'a, T>(&'a Handoff<T>);

impl<T> Popper<'_, T> {
    /// Takes data from the `Pusher` peer if it's waiting.
    ///
    /// If the peer is blocked offering us data, this unblocks them and returns
    /// `Some(value)`.
    ///
    /// Otherwise, returns `None`.
    pub fn try_pop(&mut self) -> Option<T> {
        match self.0.state.get() {
            State::PushWait(src_ptr) => {
                // Our peer is waiting. Take the thingy.
                //
                // Safety: if we're in this state the source pointer is valid
                // and the backing memory is not being used -- since if the peer
                // had resumed, it would have knocked us out of this state.
                let value = unsafe { &mut *src_ptr.as_ptr() }.take();

                self.0.state.set(State::Idle);
                self.0.ping.notify();
                value
            },
            #[cfg(debug_assertions)]
            State::PopWait(_) => panic!(),
            _ => None,
        }
    }

    /// Produces a future that resolves when the peer offers a value.
    ///
    /// # Cancellation
    ///
    /// **Cancel Safety:** Weak.
    ///
    /// If this is dropped before it resolves, no data will be lost: we have
    /// either taken data from the `Pusher` side and resolved, or we have not
    /// taken data.
    ///
    /// *However,* if this future is pending when another task successfully
    /// `push`-es, and _then_ this future is dropped before resolving, the
    /// pushed data is lost with no feedback to the pusher.
    pub async fn pop(&mut self) -> T {
        let mut guard = scopeguard::guard(None, |v| {
            if v.is_none() {
                // Cancelled while waiting to pop! We know that...
                // - We have been polled at least once (or we wouldn't be here)
                // - All paths to await in this function set the state to
                //   PopWait.
                // - If the peer sets the state to something other than
                //   PopWait, they deliver a value.
                // - Thus the current state is...
                debug_assert!(matches!(self.0.state.get(), State::PopWait(_)));
                // ...and we want to eliminate the suggestion that a popper is
                // waiting.
                self.0.state.set(State::Idle);
            }
        });
        loop {
            if guard.is_some() {
                // Value must have been deposited while we slept. The push side
                // should either have left the state idle, or began blocking for
                // our next item:
                debug_assert!(matches!(self.0.state.get(), State::Idle | State::PushWait(_)));

                return ScopeGuard::into_inner(guard).unwrap();
            } else {
                // Value has not yet been delivered. What can we do about that?
                match self.0.state.get() {
                    State::Idle => {
                        // Our peer is not waiting, we must block.
                        self.0.state.set(State::PopWait(
                            NonNull::from(&mut *guard)
                        ));
                        self.0.ping.until_next().await;
                        continue;
                    }
                    State::PopWait(_) => {
                        // We are still blocked; spurious wakeup.
                        self.0.ping.until_next().await;
                        continue;
                    },
                    State::PushWait(src_ptr) => {
                        // Our peer is waiting. We can do the handoff
                        // immediately.
                        core::mem::swap(
                            unsafe { &mut *src_ptr.as_ptr() },
                            &mut *guard,
                        );
                        self.0.state.set(State::Idle);
                        self.0.ping.notify();
                        return ScopeGuard::into_inner(guard).unwrap();
                    },
                }
            }
        }
    }
}

/// Implement Debug by hand so it doesn't require T: Debug.
impl<T> core::fmt::Debug for Popper<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Popper").field(&self.0).finish()
    }
}

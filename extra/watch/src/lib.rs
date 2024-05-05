//! A simple mechanism for sharing a piece of data and being notified if it
//! changes.
//!
//! This module provides [`Watch<T>`], a data structure that lets you share some
//! data of type `T`, update it from multiple producers, and efficiently notify
//! multiple consumers when it changes.
//!
//! A `Watch<T>` is particularly useful for things like configuration data,
//! which are effectively "global" (shared by many tasks) but may need special
//! handling of changes.
//!
//! ```
//! let shared_number = Watch::new(1234_u32);
//! ```
//!
//! You can create a _receive handle_ to the `Watch<T>` by calling
//! [`subscribe`][Watch::subscribe]. This produces a [`Receiver<T>`] that allows
//! its holder to inspect the shared data, and be notified when it changes.
//!
//! ```
//! let rcvr = shared_number.subscribe();
//! // A receiver only tracks changes made _after_ it's created:
//! assert_eq!(rcvr.is_changed(), false);
//! ```
//!
//! You can create a _send handle_ to the `Watch<T>` by calling
//! [`sender`][Watch::sender]. This produces a [`Sender<T>`] that allows its
//! holder to update the shared data.
//!
//! ```
//! let sender = shared_number.sender();
//!
//! // Update the shared data:
//! sender.send(4567);
//!
//! // Now the receiver sees a change:
//! assert_eq!(rcvr.is_changed(), true);
//!
//! // We can inspect it and mark it as seen:
//! rcvr.glimpse_and_update(|value| assert_eq!(*value, 4567));
//! ```
//!
//! Code that wants to monitor changes to the data can use the
//! [`Receiver::changed`] future to do so:
//!
//! ```
//! loop {
//!     rcvr.changed().await;
//!     rcvr.glimpse_and_update(|value| process(value));
//! }
//! ```
//!
//! # Reentrancy and panics
//!
//! It is possible to attempt to use handles for a single `Watch<T>` reentrantly
//! if you try hard enough. The implementation checks for this and will panic.
//! For instance, attempting to send a new value from _inside_ the closure
//! passed to [`Receiver::glimpse`]:
//!
//! ```
//! let shared = Watch::new(some_data);
//! let sender = shared.sender();
//! let rcvr = shared.subscribe();
//!
//! // This line will panic at runtime.
//! rcvr.glimpse(|contents| sender.send(*contents));
//! ```
//!
//! It is perfectly safe to send or inspect a _different_ `Watch<T>` instance
//! from within one of these closures, just not the same one.
//!
//! In practice it's pretty hard to do this accidentally, but, now you know.
//!
//! # Implementation
//!
//! Specifically, the `Watch<T>` contains a _change count_. Each time its
//! contents are updated by any `Sender`, the change count gets incremented.
//!
//! Each `Receiver` has its own copy of the change count, reflecting what the
//! count was at the last time that `Receiver` accessed the shared data. If the
//! change count stored in the `Watch` is different from the one stored in the
//! `Receiver`, then there is an update that hasn't been seen by its holder yet.
//!
//! Because the `Watch<T>` only stores a single copy of the data and a counter,
//! a `Receiver` may not see _every_ update to the data. If multiple updates
//! happen between checks, the `Receiver` will only ever see the last one. This
//! keeps both the storage requirements, and the cost of updates, low.
//!
//! `Watch<T>` contains a [`Notify`] internally, which it uses to efficiently
//! wake tasks that are awaiting [`Receiver::changed`].

#![no_std]

#![forbid(unsafe_code)]
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

use core::cell::{Cell, RefCell};

use lilos::exec::Notify;

/// Store some data of type `T` and efficiently notify multiple consumers if it
/// changes.
///
/// See the [module docs][crate] for more specifics and examples.
#[derive(Debug)]
pub struct Watch<T> {
    version: Cell<u64>,
    contents: RefCell<T>,
    update: Notify,
}

impl<T> Watch<T> {
    /// Creates a new `Watch<T>` that will initially contain `contents`.
    pub const fn new(contents: T) -> Self {
        Self {
            version: Cell::new(0),
            contents: RefCell::new(contents),
            update: Notify::new(),
        }
    }

    /// Creates a new send-only handle to the watched data.
    pub fn sender(&self) -> Sender<'_, T> {
        Sender {
            shared: self,
        }
    }

    /// Creates a new receive-only handle to the watched data.
    ///
    /// The returned `Receiver` treats the current contents as "seen," and any
    /// attempt to wait for changes will wait for the _next_ change. If this
    /// isn't what you want, you can force the `Receiver` to treat its initial
    /// contents as novel by calling [`Receiver::mark_as_unseen`].
    pub fn subscribe(&self) -> Receiver<'_, T> {
        let version = self.version.get();
        Receiver {
            version,
            shared: self,
        }
    }
}

/// Posts new values to a `Watch<T>`.
///
/// There can be many `Sender`s for a single `Watch<T>`. They're not
/// distinguished from each other --- any code observing the watched data will
/// just see a change, and won't be told where the change was made.
#[derive(Clone, Debug)]
pub struct Sender<'a, T> {
    shared: &'a Watch<T>,
}

impl<'a, T> Sender<'a, T> {
    /// Replaces the watched data with `value` and signals that a change has
    /// occurred.
    ///
    /// This advances the internal change count and wakes any tasks that have
    /// blocked waiting for changes.
    ///
    /// # Panics
    ///
    /// If called from inside the closure passed to [`Receiver::glimpse`] or
    /// [`Receiver::glimpse_and_update`], on a `Receiver` that would receive
    /// `value`, this will panic. Don't do that.
    pub fn send(&self, value: T) {
        self.send_replace(value);
    }

    /// Replaces the watched data with `value` and signals that a change has
    /// occurred.
    ///
    /// This advances the internal change count and wakes any tasks that have
    /// blocked waiting for changes.
    ///
    /// # Panics
    ///
    /// If called from inside the closure passed to [`Receiver::glimpse`] or
    /// [`Receiver::glimpse_and_update`], on a `Receiver` that would receive
    /// `value`, this will panic. Don't do that.
    pub fn send_replace(&self, value: T) -> T {
        self.send_modify(|r| core::mem::replace(r, value))
    }

    /// Applies `body` to the watched data and then signals that a change has
    /// occurred. `body` is free to update the watched data however it likes,
    /// but even if it leaves it unchanged, observers will still be signaled.
    ///
    /// This advances the internal change count and wakes any tasks that have
    /// blocked waiting for changes.
    ///
    /// # Panics
    ///
    /// Calling this inside the closure passed to a `Receiver` on the _same
    /// watched data,_ or vice versa, will panic. Don't do that.
    pub fn send_modify<R>(&self, body: impl FnOnce(&mut T) -> R) -> R {
        let w = self.shared;
        let Ok(mut r) = w.contents.try_borrow_mut() else {
            panic!("attempt to send during glimpse or send_modify");
        };
        let result = body(&mut *r);
        w.version.set(w.version.get().wrapping_add(1));

        self.shared.update.notify();

        result
    }

    /// Makes a `Receiver` that will watch the data posted by this `Sender`.
    ///
    /// This is the same operation as `Watch::subscribe`, provided here because
    /// it's sometimes convenient to use directly on a `Sender`.
    pub fn subscribe(&self) -> Receiver<'a, T> {
        self.shared.subscribe()
    }
}

/// Receives changes made to the data in a `Watch<T>`.
///
/// Each `Receiver` keeps track of which versions of the watched data it has
/// seen. This is updated in one of three ways:
///
/// - When a future produced by [`Receiver::changed`] resolves.
/// - When you call [`Receiver::glimpse_and_update`].
/// - When you call [`Receiver::mark_as_seen`].
#[derive(Clone, Debug)]
pub struct Receiver<'a, T> {
    version: u64,
    shared: &'a Watch<T>,
}

impl<T> Receiver<'_, T> {
    /// Returns a future that resolves when the value being observed has
    /// been updated.
    ///
    /// When this future resolves, it will mark the most recent version as
    /// having been seen. This means calling `changed` again will produce a
    /// future that waits until _another_ change to the watched value.
    ///
    /// To actually observe the value when this resolves, use
    /// [`glimpse`][Receiver::glimpse].
    ///
    /// Note that the value may have been updated _multiple times_ before this
    /// future resolves; those updates will all be collapsed from this
    /// receiver's perspective.
    ///
    /// # Cancellation
    ///
    /// This is cancel safe. If you drop the future before it resolves, nothing
    /// will happen --- in particular, the notion of which data the `Receiver`
    /// has or has not seen won't change.
    pub async fn changed(&mut self) {
        let w = self.shared;
        let v = w.update.until(|| {
            let v = w.version.get();
            if v != self.version {
                Some(v)
            } else {
                None
            }
        }).await;
        self.version = v;
    }

    /// Checks whether the watched data has changed since it was last marked as
    /// seen by this `Receiver`.
    pub fn is_changed(&self) -> bool {
        let w = self.shared;
        let v = w.version.get();
        v != self.version
    }

    /// Gets a brief look at the watched value.
    ///
    /// `glimpse` runs its `body` parameter with a reference to the watched
    /// value. This lets you inspect the contents without necessarily having to
    /// copy them out, which might be expensive or undesirable for some other
    /// reason (perhaps the watched value does not impl `Clone`).
    ///
    /// This takes a closure instead of returning a guard to ensure that there's
    /// no way to `await` with access to the watched value. Because this can't
    /// hold a reference to the watched value across an `await`, _and_ the
    /// sending side can't hold a reference across an `await`, this is
    /// guaranteed to complete promptly without blocking or deadlocks.
    ///
    /// `glimpse` does not, itself, mark the latest value as having been seen.
    /// Generally you'll use `glimpse` along with `changed` like so:
    ///
    /// ```rust
    /// loop {
    ///     watcher.changed().await;
    ///     watcher.glimpse(|value| {
    ///         do_stuff_with(value);
    ///     });
    /// }
    /// ```
    ///
    /// In that example, `changed` is responsible for making the value as seen.
    ///
    /// If you'd like to access the value and simultaneously mark it as seen
    /// without blocking or messing around with `changed`, use
    /// [`glimpse_and_update`][Receiver::glimpse_and_update].
    ///
    /// **Note:** Even though `glimpse` does not mark the contents as seen, that
    /// doesn't mean multiple calls to `glimpse` will see the same contents!
    ///
    /// # Panics
    ///
    /// If you attempt to use [`Sender::send`] to post to the same watched data
    /// you are observing during `glimpse`, it'll panic. Don't do that.
    pub fn glimpse<R>(&self, body: impl FnOnce(&T) -> R) -> R {
        let Ok(r) = self.shared.contents.try_borrow() else {
            panic!("attempt to glimpse during send_modify");
        };
        body(&*r)
    }

    /// Makes a copy of the current state of the watched data, without marking
    /// it as seen.
    ///
    /// This can be useful when `T` is relatively small --- and implements
    /// `Copy`, of course. This is equivalent to the handwritten version:
    ///
    /// ```
    /// let copy = watch.glimpse(|current| *current);
    /// ```
    ///
    /// To copy the contents and also mark them as seen, see
    /// [`copy_current_and_update`][Self::copy_current_and_update].
    #[inline(always)]
    pub fn copy_current(&self) -> T
        where T: Copy
    {
        self.glimpse(|value| *value)
    }

    /// Gets a brief look at the watched value, and records that it has been
    /// seen.
    ///
    /// `glimpse_and_update` runs its `body` parameter with a reference to the
    /// watched value. This lets you inspect the contents without necessarily
    /// having to copy them out, which might be expensive or undesirable for
    /// some other reason (perhaps the watched value does not impl `Clone`).
    ///
    /// This takes a closure instead of returning a guard to ensure that there's
    /// no way to `await` with access to the watched value. Because this can't
    /// hold a reference to the watched value across an `await`, _and_ the
    /// sending side can't hold a reference across an `await`, this is
    /// guaranteed to complete promptly without blocking or deadlocks.
    ///
    /// `glimpse_and_update` marks the latest value as having been seen, under
    /// the assumption that you're not interested in waiting for changes to
    /// occur. If you'd like to only process data in response to changes, you'll
    /// probably use [`changed`][Receiver::changed] to do so, in which case it's
    /// slightly cheaper (and less typing) to use [`glimpse`][Receiver::glimpse]
    /// instead.
    ///
    /// # Panics
    ///
    /// If you attempt to use [`Sender::send`] to post to the same watched data
    /// you are observing during `glimpse_and_update`, it'll panic. Don't do
    /// that.
    pub fn glimpse_and_update<R>(&mut self, body: impl FnOnce(&T) -> R) -> R {
        let r = self.glimpse(body);
        self.mark_as_seen();
        r
    }

    /// Makes a copy of the current state of the watched data, and marks it as
    /// seen.
    ///
    /// This can be useful when `T` is relatively small --- and implements
    /// `Copy`, of course. This is equivalent to the handwritten version:
    ///
    /// ```
    /// let copy = watch.glimpse_and_update(|current| *current);
    /// ```
    ///
    /// To copy the contents _without_ marking them as seen, see
    /// [`copy_current`][Self::copy_current].
    pub fn copy_current_and_update(&mut self) -> T
        where T: Copy
    {
        self.glimpse_and_update(|value| *value)
    }

    /// Resets this `Receiver`'s notion of what data has been seen, ensuring
    /// that the current contents of the watched data will be treated as new for
    /// the purposes of [`changed`][Self::changed].
    pub fn mark_as_unseen(&mut self) {
        // What's an integer that is guaranteed to not be equal to the current
        // version, and is also quite unlikely to be equal to any version in the
        // near future? How about the _previous_ version!
        self.version = self.shared.version.get().wrapping_sub(1);
    }

    /// Marks the current contents of the watched data as having been seen,
    /// whether or not this `Receiver` has actually seen them.
    pub fn mark_as_seen(&mut self) {
        self.version = self.shared.version.get();
    }
}

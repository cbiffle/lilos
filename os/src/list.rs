// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Doubly-linked intrusive lists for scheduling and waking (old version).
//!
//! **Please use the `lilos_list` crate instead. It's better in literally every
//! way.**
//!
//! A [`List<T>`][List] keeps track of nodes (of type [`Node<T>`][Node]) that
//! each contain some value `T`. The list is kept in *sorted* order by comparing
//! the `T`s:
//!
//! - [`List::insert_and_wait`] traverses the list to insert the `Node` in its
//!   proper place, and then waits for the node to be kicked back out.
//! - [`List::wake_thru`] starts at one end and removes every `Node` with a
//!   value less than or equal to a threshold.
//!
//! The sort order is used to order things by timestamps, but you may find other
//! uses for it.
//!
//! If you just want to keep things in a list, and don't care about order or
//! need to associate a timestamp, simply use `List<()>`. This disables the
//! sorting and removes the order-related fields from both the list and node.
//! Such a list will track its nodes in the order in which they were inserted.
//!
//!
//! # Using as a timer list, or other type of ordered list
//!
//! - Create a `List<YourTimestamp>`.
//! 
//! - To track a waiter in the list, create a `Node<YourTimestamp>` and pass it
//!   to [`List::insert_and_wait`]. The node will be inserted in timestamp
//!   order, after any existing nodes with the same timestamp. Note that you
//!   must `await` (or poll) the future produced by `insert_and_wait` for the
//!   node to actually join the list in its proper place.
//!
//! - At some future point, wake all nodes in a timestamp range by using either
//!   [`List::wake_while`] or, as a convenience for writing timers,
//!   [`List::wake_thru`].
//!
//!
//! # Using as a wait queue
//!
//! - Create a `List<()>`.
//!
//! - To track a waiter in the list, create a `Node<()>` and pass it to
//!   [`List::insert_and_wait`]. The node will be inserted at the tail of the
//!   list. Note that you must `await` (or poll) the future produced by
//!   `insert_and_wait` for the node to actually join the list in its proper
//!   place.
//!
//! - To wake one waiter, use [`List::wake_one`].
//!
//! - To wake a series of waiters, us [`List::wake_while`].
//!
//!
//! # Pinning
//!
//! Because `List` and `Node` create circular, self-referential data structures,
//! all operations require that they be
//! [pinned](https://doc.rust-lang.org/core/pin/). Because we don't use the
//! heap, we provide ways to create and use pinned data structures on the stack.
//! This is, unfortunately, kind of involved -- but the
//! [`create_node!`][crate::create_node] and
//! [`create_list!`][crate::create_list] convenience macros help.
//!
//! Here is an example of creating a `Node`, since that's what user code creates
//! most often; see the sources for [`mutex`](crate::mutex) for a real-world
//! example.
//!
//! ```ignore
//! # fn foo() {
//! // This creates a local variable called "my_node"
//! os::create_node!(my_node, ());
//!
//! // Join a wait list
//! wait_list.insert_and_wait(my_node.as_mut()).await;
//!
//! // All done, my_node can be dropped
//! # }
//! ```
//!
//! Creating a list or node is a three-step process. We'll use `Node` as a
//! running example here, but the same applies to `List`.
//!
//! 1. Create a partially-initialized version using [`Node::new`] and extract it
//!    from the `ManuallyDrop` container. This is unsafe, because the object
//!    you're now holding will dereference bogus pointers if dropped. This makes
//!    it very important to proceed to the next two steps *without doing
//!    anything else*, particularly anything that could panic.
//!
//! 2. Put the `Node` in its final resting place (which may be a local, or might
//!    be a field of a struct, etc.) and pin it. The
//!    [`pin!`](https://doc.rust-lang.org/stable/core/pin/macro.pin.html)
//!    macro makes doing this on the stack easier.
//!
//! 3. Finish setting it up by calling [`Node::finish_init`].
//!
//! While each of these steps is unsafe, if you do them in sequence without
//! panicking, the result can be used safely -- and so the `create_node!` and
//! `create_list!` macros themselves are safe.
//!
//! (These operations must be macros, not functions, because we can't return an
//! object by-value once it's pinned.)
//!
//! So, with that in mind, the fully-manual version of the example above reads
//! as follows:
//!
//! ```ignore
//! # fn foo() {
//! // Create a partially initialized node, pinned on the stack.
//! //
//! // Safety: this is safe as long as we fulfill the rest of the conditions
//! // required by Node::new before doing anything that could result in dropping
//! // the node, including `panic!` or `await`.
//! let mut my_node = core::pin::pin!(unsafe {
//!     core::mem::ManuallyDrop::into_inner(
//!         os::list::Node::new((), os::exec::noop_waker())
//!     )
//! });
//! // Finish initialization.
//! //
//! // Safety: this discharges the rest of the obligations laid out by
//! // Node::new.
//! unsafe {
//!     os::list::Node::finish_init(my_node.as_mut());
//! }
//!
//! // Join a wait list
//! wait_list.insert_and_wait(my_node.as_mut()).await;
//!
//! // All done, my_node can be dropped
//! # }
//! ```
//!
//!
//! # The metadata (`M`) parameter
//!
//! `List<T>` is actually `List<T, M>`, but the `M` parameter defaults to `()`
//! and is ignored by most users.
//!
//! `M` is for metadata, and allows you to associate an arbitrary,
//! application-specific piece of data with each node in the list. For instance,
//! if a wait queue distinguishes between different _kinds_ of waiters, you
//! could declare an `enum` listing the kinds, and use that as the metadata
//! parameter.
//!
//! Metadata is available for inspection in the [`List::wake_one_if`] and
//! [`List::wake_while`] operations, through the [`Node::meta`] function.
//!
//!
//! # How is this safe?
//!
//! The `List` API relies on *blocking* for safety. Because `insert_and_wait`
//! takes control away from the caller until the node is kicked back out of the
//! list, it is borrowing the `&mut Node` for the duration of its membership in
//! the list. If the API were instead `insert`, we'd return to the caller, who
//! is still holding a `&mut Node` -- a supposedly exclusive reference to a
//! structure that is now also reachable through the `List`!
//!
//! This is why there is no `insert` operation, or a `take` operation that
//! returns a node -- both operations would compromise memory safety.

// Implementation safety notes:
//
// The safety comments in this module reference the following invariants:
//
// Link Valid Invariant: all the link pointers (that is, `Node::prev` and
// `Node::next`) transitively reachable from either `List` or `Node` are valid /
// not dangling. We maintain this by only setting them to the addresses of
// pinned structures, and ensuring that the `Drop` impl of those pinned
// structures will remove their addresses from any link.

use core::cell::{Cell, UnsafeCell};

use core::future::Future;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::ptr::NonNull;
use core::task::{Poll, Waker};
use pin_project::{pin_project, pinned_drop};

use crate::util::{NotSendMarker, Captures};

/// A cell specialized for holding `Waker`s. This is functionally equivalent to
/// `Cell` except that it will allow one operation to be performed on its
/// contents by reference: `wake_by_ref`.
///
/// # Why we can do this
///
/// We satisfy a narrow form of `UnsafeCell`'s safety contract:
///
/// - This type is not `Sync` and can't be accessed from multiple threads. This
///   means at most once of its operations (below) is executing at a time.
///
/// - The operations will produce temporary references (both `&` and `&mut`)
///   into the `UnsafeCell`, but will only produce one such reference at a time,
///   and won't let it escape the function. This prevents aliasing in both
///   directions, and deallocation of data while a reference exists.
///
/// This puts us into the corner of `UnsafeCell`'s contract that, at the time of
/// this writing, reads "explicitly declared legal for single-threaded code."
struct WakerCell(UnsafeCell<Waker>);

impl WakerCell {
    fn new(waker: Waker) -> Self {
        Self(UnsafeCell::new(waker))
    }

    fn update(&self, waker: Waker) {
        // Safety: this is unsafe because we're generating a &mut to the
        // contents of the UnsafeCell. We can do this thanks to our type-level
        // invariant that we don't generate more than one reference into the
        // cell at a time.
        //
        // Note: as tempting as it might be to use `ptr::write` directly on the
        // pointer returned from `get`, this would leak the previous waker
        // without calling its destructor. This happens to be just fine on
        // current versions of this executor, but is wrong in the general case.
        *unsafe { &mut *self.0.get() } = waker;
    }

    fn wake_by_ref(&self) {
        // Safety: this is unsafe because we're creating a shared reference into
        // the UnsafCell. We can do this thanks to our type-level invariant that
        // we don't generate more than one reference into the cell at a time.
        unsafe { &*self.0.get() }.wake_by_ref()
    }
}

/// A member of a list.
///
/// A node is either *detached* (not in a list) or *attached* (in a list). After
/// creation it is initially detached; you can attach it to a list using
/// `List::insert_and_wait`. To detach it, either call `Node::detach` or drop
/// the node.
///
/// Because the list data structure uses pointer cycles extensively, nodes must
/// always be pinned. Because we avoid the heap, creating a pinned node is a
/// slightly involved two-step process. The `create_node` macro helps with this;
/// see `Node::new` if you want to do it yourself.
///
/// A node contains three pieces of data: the `waker`, the `contents`, and the
/// `metadata`.
///
/// - The `waker` is a `core::task::Waker`, an abstract reference to a task that
///   wishes to be woken up at some point. You'll generally provide
///   [`noop_waker`][crate::exec::noop_waker] and the OS will replace it with an
///   appropriate one when the node is inserted into a list. (The `create_node!`
///   macro will provide `noop_waker` automatically if not overridden.)
///
/// - The `contents` is some `T`, and is typically a timestamp. Inserting a node
///   into a list requires that `T` be `PartialOrd`, and the list will be
///   maintained in ascending sorted order by each node's `contents`. If you
///   don't need your list to be sorted, `Node<()>` degenerates into an
///   insertion-order list.
///
/// - The `metadata` (`M`) allows you to associate data of your choice with a
///   node. This data cannot affect insertion order, but can be used to decide
///   which nodes to detach or wake, by inspecting it through [`Node::meta`]
///   during [`List::wake_one_if`] or [`List::wake_while`]. Note that `M` can be
///   omitted, in which case it defaults to `()`.
#[pin_project(PinnedDrop)]
pub struct Node<T, M = ()> {
    prev: Cell<NonNull<Self>>,
    next: Cell<NonNull<Self>>,
    waker: WakerCell,
    contents: T,
    meta: M,
    _marker: NotSendMarker,
}

impl<T> Node<T> {
    /// Creates a `Node` in a semi-initialized state.
    ///
    /// If you need to attach metadata to the node, see [`Node::new_with_meta`].
    ///
    /// Note that you probably don't need to use this directly. See
    /// [`create_node!`][crate::create_node] for a more convenient option.
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call `finish_init`.
    #[inline(always)]
    pub unsafe fn new(contents: T, waker: Waker) -> ManuallyDrop<Self> {
        // Safety: our safety contract is exactly the same as `new_with_meta`.
        unsafe {
            Self::new_with_meta(contents, (), waker)
        }
    }
}

impl<T, M> Node<T, M> {
    /// Creates a `Node` in a semi-initialized state, attaching the given
    /// metadata. If your metadata is `()`, please use [`Node::new`] instead.
    ///
    /// Note that you probably don't need to use this directly. See
    /// [`create_node_with_meta!`][crate::create_node_with_meta] for a more
    /// convenient option.
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call `finish_init`.
    pub unsafe fn new_with_meta(contents: T, meta: M, waker: Waker) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Node {
            prev: Cell::new(NonNull::dangling()),
            next: Cell::new(NonNull::dangling()),
            waker: WakerCell::new(waker),
            contents,
            meta,
            _marker: NotSendMarker::default(),
        })
    }

    /// Finishes initialization of a node, discharging the obligations placed on
    /// you by `new` or `new_with_meta`.
    ///
    /// # Safety
    ///
    /// To use this safely, you must call this on the pinned result of `new`
    /// or `new_with_meta` before doing *anything else* with it.
    pub unsafe fn finish_init(node: Pin<&mut Self>) {
        // Note: this takes a &mut despite the code below not requiring it. We
        // do this to prove that the caller still has exclusive ownership.
        let nnn = NonNull::from(&*node);
        node.next.set(nnn);
        node.prev.set(nnn);
    }

    /// Disconnects a node from any list. This is idempotent, since an unlinked
    /// node points to itself.
    pub fn detach(self: Pin<&Self>) {
        // Un-link from the neighbors. Note: it is entirely possible that we
        // are our own neighbor. This turns into an expensive no-op in that
        // case, since self.prev == self.prev.prev, etc.
        //
        // Safety: Link Valid Invariant allows deref of prev/next, and as_ref
        // ensures that the temporary reference produced to get at next/prev can
        // safely alias &self
        unsafe {
            self.prev.get().as_ref().next.set(self.next.get());
            self.next.get().as_ref().prev.set(self.prev.get());
        }
        // Link to ourselves.
        self.prev.set(NonNull::from(&*self));
        self.next.set(NonNull::from(&*self));
    }

    /// Checks if a node is detached.
    pub fn is_detached(&self) -> bool {
        // We only need to check one of the two pointers, since a half-detached
        // node would violate our invariants.
        self.prev.get() == NonNull::from(self)
    }

    /// Inspects the metadata contents of a `Node`.
    pub fn meta(&self) -> &M {
        &self.meta
    }
}

/// A `Node` will detach itself from any list on drop.
#[pinned_drop]
impl<T, M> PinnedDrop for Node<T, M> {
    fn drop(self: Pin<&mut Self>) {
        self.as_ref().detach();
    }
}

/// Returns a decent `Debug` impl for the contents of `cell`, correctly
/// indicating both dangling/uninitialized and self-linked pointers.
fn debug_link<'a, T>(parent: &T, cell: &'a Cell<NonNull<T>>) -> &'a dyn core::fmt::Debug {
    #[derive(Debug)]
    struct Uninitialized;

    #[derive(Debug)]
    struct SelfLinked;

    let ptr = cell.get();
    let rawptr: *const _ = ptr.as_ptr();
    if ptr == NonNull::dangling() {
        &Uninitialized
    } else if rawptr == parent {
        &SelfLinked
    } else {
        cell
    }
}

impl<T: core::fmt::Debug, M: core::fmt::Debug> core::fmt::Debug for Node<T, M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Node")
            .field("prev", debug_link(self, &self.prev))
            .field("next", debug_link(self, &self.next))
            .field("waker", &"...")
            .field("contents", &self.contents)
            .field("meta", &self.meta)
            .finish()
    }
}

/// A list of `Node`s.
///
/// The list *references*, but does not *own*, the nodes. The creator of each
/// node keeps ownership of it, and if they drop the node, it leaves the list.
///
/// Because lists contain self-referential pointers, creating one is somewhat
/// involved. Use the [`create_list!`][crate::create_list] macro when possible,
/// or see `List::new` for instructions.
///
/// # Type parameters
///
/// `List` has two type parameters, `T` and `M`. Only `T` must be provided.
///
/// `T` is used to order nodes in the list, according to its `PartialOrd` impl.
/// If you don't need ordering, pass `()` to disable this.
///
/// `M` is used to associate arbitrary uninterpreted metadata to each node. If
/// you don't need this, omit it or pass `()` (which is the default if it's
/// omitted).
///
/// # Drop
///
/// You must remove/wake all the nodes in a list before dropping the list.
/// Dropping a list without emptying it is treated as a programming error, and
/// will panic.
///
/// This isn't the only way we could do things, but it is the safest. If you're
/// curious about the details, see the source code for `Drop`.
#[pin_project(PinnedDrop)]
pub struct List<T, M = ()> {
    #[pin]
    root: Node<T, M>,
    _marker: NotSendMarker,
}

/// Creating a `List` requires `T: Default` because we store a useless `T`
/// inside the list to reduce code duplication. This is mildly annoying and
/// might be worth fixing later.
impl<T: Default> List<T> {
    /// Creates a `List` in an initialized but unsafe state.
    ///
    /// The returned list is not safe to operate on or drop, which is why it's
    /// returned in a `ManuallyDrop` wrapper.
    ///
    /// # Safety
    ///
    /// For this to be safe, you must do only one of two things with the result:
    ///
    /// 1. Drop it immediately (i.e. without removing it from `ManuallyDrop`).
    /// 2. Unwrap it, pin it, and then call `List::finish_init`.
    ///
    /// You must *not* do anything that might `panic!` or `await` between these
    /// steps! To make this process easier, consider using the
    /// [`create_list!`][crate::create_list] macro where possible.
    pub unsafe fn new() -> ManuallyDrop<List<T>> {
        // Safety: our safety contract matches new_with_meta's.
        unsafe {
            Self::new_with_meta(())
        }
    }
}

impl<T: Default, M> List<T, M> {
    /// Creates a `List` in an initialized but unsafe state, filling in the
    /// list's generally-unused internal metadata slot with the value `meta`.
    /// This value basically doesn't matter, and is passed in here only to avoid
    /// requiring `M: Default`.
    ///
    /// The returned list is not safe to operate on or drop, which is why it's
    /// returned in a `ManuallyDrop` wrapper.
    ///
    /// # Safety
    ///
    /// For this to be safe, you must do only one of two things with the result:
    ///
    /// 1. Drop it immediately (i.e. without removing it from `ManuallyDrop`).
    /// 2. Unwrap it, pin it, and then call `List::finish_init`.
    ///
    /// You must *not* do anything that might `panic!` or `await` between these
    /// steps! To make this process easier, consider using the
    /// [`create_list!`][crate::create_list] macro where possible.
    pub unsafe fn new_with_meta(meta: M) -> ManuallyDrop<List<T, M>> {
        // Safety: Node::new is unsafe because it produces a node that cannot be
        // safely dropped. We punt its obligations down the road by re-wrapping
        // it in our _own_ unsafe ManuallyDrop structure.
        let node = unsafe {
            Node::new_with_meta(
                T::default(),
                meta,
                #[allow(deprecated)]
                crate::exec::noop_waker(),
            )
        };
        ManuallyDrop::new(List {
            root: ManuallyDrop::into_inner(node),
            _marker: NotSendMarker::default(),
        })
    }
}

impl<T, M> List<T, M> {
    /// Completes the initialization process, discharging the obligations put in
    /// place by `new`.
    ///
    /// # Safety
    ///
    /// For this to be safe, you must call it on the pinned result of a call to
    /// `new()` before doing *anything else* to the `List`.
    pub unsafe fn finish_init(list: Pin<&mut Self>) {
        // Safety: this is safe if our own safety contract is upheld.
        unsafe {
            Node::finish_init(list.project().root);
        }
    }

    /// Checks if the list is empty (i.e. there are no nodes waiting). Returns
    /// `true` if the list is empty, `false` if there are nodes waiting.
    pub fn is_empty(&self) -> bool {
        self.root.is_detached()
    }
}

impl<T: PartialOrd, M> List<T, M> {
    /// Inserts `node` into this list, maintaining ascending sort order, and
    /// then waits for it to be kicked back out.
    ///
    /// Specifically, `node` will be placed just *after* the first item in the
    /// list whose `contents` are less than or equal to `node.contents`, if such
    /// an item exists, or at the end if not. This ensures that, within
    /// stretches of nodes with equal `contents`, the nodes are sorted in
    /// insertion order.
    ///
    /// (For a `Node<()>` (an insertion-ordered list), all nodes have the same
    /// contents, so this degenerates into maintaining insertion order.)
    ///
    /// When the returned future completes, `node` has been detached again.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict, but see `insert_and_wait_with_cleanup` if the
    /// context this is used needs help being cancel-safe.
    ///
    /// Dropping the future returned by `insert_and_wait` will forceably detach
    /// `node` from `self`. This is important for safety: the future borrows
    /// `node`, preventing concurrent modification while there are outstanding
    /// pointers in the list. If the future did not detach on drop, the caller
    /// would regain access to their `&mut Node` while the list also has
    /// pointers, violating aliasing.
    ///
    /// If the node is detached on drop, but this future has not yet been
    /// polled, then you, the user, have a decision to make. If the node being
    /// detached from the list represents a meaningful change to state, such as
    /// the continued locking of a mutex, then failing to poll the future before
    /// drop may corrupt state by e.g. leaving that mutex locked. To handle
    /// this, use `insert_and_wait_with_cleanup` instead.
    ///
    /// For the common case of a timer list, cleanup is typically not needed.
    ///
    /// # Panics
    ///
    /// If `node` is not detached (if it's in another list) when this is called.
    /// This should be pretty difficult to achieve in practice.
    pub fn insert_and_wait<'list, 'node>(
        self: Pin<&'list Self>,
        node: Pin<&'node mut Node<T, M>>,
    ) -> impl Future<Output = ()> + Captures<(&'list Self, &'node mut Node<T>)> {
        // We required `node` to be `mut` to prove exclusive ownership, but we
        // don't actually need to mutate it -- and we're going to alias it. So,
        // downgrade.
        let node = node.into_ref();

        WaitForDetach {
            node,
            list: self,
            state: Cell::new(WaitState::NotYetAttached),
        }
    }

    /// Inserts `node` into this list, maintaining ascending sort order, and
    /// then waits for it to be kicked back out.
    ///
    /// Specifically, `node` will be placed just *after* the last item in the
    /// list whose `contents` are less than or equal to `node.contents`, if such
    /// an item exists, or at the end if not.
    ///
    /// When the returned future completes, `node` has been detached again.
    ///
    /// The `cleanup` action is performed in only one circumstance:
    ///
    /// 1. `node` has been detached by some other code,
    /// 2. The returned `Future` has not yet been polled, and
    /// 3. It is being dropped.
    ///
    /// This gives you an opportunity to e.g. wake another node or otherwise fix
    /// up state.
    ///
    /// # Cancellation
    ///
    /// **Cancel safety:** Strict, plus cleanup opportunity.
    ///
    /// Dropping the future returned by `insert_and_wait_with_cleanup` will
    /// forceably detach `node` from `self`. This is important for safety: the
    /// future borrows `node`, preventing concurrent modification while there
    /// are outstanding pointers in the list. If the future did not detach on
    /// drop, the caller would regain access to their `&mut Node` while the list
    /// also has pointers, violating aliasing.
    ///
    /// If the node is detached on drop, but this future has not yet been
    /// polled, `cleanup` will be run. You can use this to cause a more complex
    /// abstraction built around a `List` to also be strictly cancel-safe. This
    /// is a subtle topic, but, see the `mutex` implementation for a worked
    /// example. If you find yourself passing a no-op closure for `cleanup`,
    /// have a look at `insert_and_wait` for your convenience.
    ///
    /// # Panics
    ///
    /// If `node` is not detached (if it's in another list) when this is called.
    /// This should be pretty difficult to achieve in practice.
    pub fn insert_and_wait_with_cleanup<'list, 'node, F: 'node + FnOnce()>(
        self: Pin<&'list Self>,
        node: Pin<&'node mut Node<T, M>>,
        cleanup: F,
    ) -> impl Future<Output = ()> + Captures<(&'list Self, &'node mut Node<T>)> {
        // We required `node` to be `mut` to prove exclusive ownership, but we
        // don't actually need to mutate it -- and we're going to alias it. So,
        // downgrade.
        let node = node.into_ref();

        WaitWithCleanup {
            inner: WaitForDetach {
                node,
                list: self,
                state: Cell::new(WaitState::NotYetAttached),
            },
            cleanup: Some(cleanup),
        }
    }

    /// Beginning at the head of the list, removes nodes whose `contents` are
    /// `<= threshold` and wakes their tasks.
    ///
    /// After this completes:
    ///
    /// - Any `Node` previously inserted into this list with `contents <=
    ///   threshold` is now detached, and its waker has been called.
    ///
    /// - All `Node`s remaining in this list have `contents > threshold`.
    pub fn wake_thru(self: Pin<&Self>, threshold: T) {
        self.wake_while(|n| n.contents <= threshold);
    }

    /// Beginning at the head of the list, removes nodes whose `contents` are
    /// `<= threshold` and wakes their tasks.
    ///
    /// **Caution:** Despite the name of this function, this removes nodes whose
    /// `contents` are _less than or equal to_ `threshold`! This name has been
    /// deprecated, and you should use [`List::wake_thru`] instead.
    ///
    /// After this completes:
    ///
    /// - Any `Node` previously inserted into this list with `contents <=
    ///   threshold` is now detached, and its waker has been called.
    ///
    /// - All `Node`s remaining in this list have `contents > threshold`.
    pub fn wake_less_than(self: Pin<&Self>, threshold: T) {
        self.wake_thru(threshold)
    }

    /// Beginning at the head of the list, removes nodes that are accepted by
    /// `pred` (i.e. where `pred(node)` returns `true`), and wakes the
    /// associated tasks.
    ///
    /// Stops at the first node for which `pred` returns `false`. That node is
    /// left in the list, and its task is not awoken.
    ///
    /// Note that there may be _other_ nodes farther in the list for which
    /// `pred` would return `true`, unless `pred` is comparing the `contents`
    /// field used to order the list.
    ///
    /// Returns `true` if at least one node was removed, `false` otherwise.
    pub fn wake_while(self: Pin<&Self>, mut pred: impl FnMut(Pin<&Node<T, M>>) -> bool) -> bool {
        let mut changes = false;

        // Work through the nodes from the head, using the root as a sentinel to
        // stop iteration.
        let mut candidate = self.root.next.get();
        while candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant
            let cref = unsafe { Pin::new_unchecked(candidate.as_ref()) };
            if !pred(cref) {
                break;
            }
            // Copy the next pointer before detaching.
            let next = cref.next.get();
            cref.detach();
            cref.waker.wake_by_ref();

            changes = true;
            candidate = next;
        }

        changes
    }


    /// Inspects the head node `n` in the list and wakes it if `pred(&n)`
    /// returns `true`.
    ///
    /// Returns `true` if a node was awoken, `false` if `pred` didn't accept the
    /// node or the list was empty.
    pub fn wake_one_if(self: Pin<&Self>, pred: impl FnOnce(Pin<&Node<T, M>>) -> bool) -> bool {
        // Inspect the head of the list, assuming it is not the root.
        let candidate = self.root.next.get();
        if candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant
            let cref = unsafe { Pin::new_unchecked(candidate.as_ref()) };
            if pred(cref) {
                cref.detach();
                cref.waker.wake_by_ref();
                return true;
            }
        }
        false
    }
}

impl<M> List<(), M> {
    /// Convenience method for waking all the waiters on an unsorted list,
    /// because `wake_thru(())` looks weird.
    ///
    /// Note that using this operation tends to trigger the amusingly named
    /// ["thundering herd problem"][th], by making a bunch of waiting tasks
    /// compete to decide who gets to do something next. More surgical wake
    /// methods like [`List::wake_one`] are often a better choice when
    /// applicable.
    ///
    /// [th]: https://en.wikipedia.org/wiki/Thundering_herd_problem
    pub fn wake_all(self: Pin<&Self>) {
        self.wake_thru(())
    }

    /// Wakes the oldest waiter on an unsorted list (the head).
    ///
    /// Returns a flag indicating whether anything was done (i.e. whether the
    /// list was found empty).
    pub fn wake_one(self: Pin<&Self>) -> bool {
        self.wake_one_if(|_| true)
    }
}

/// Dropping a non-empty list currently indicates a programming error in the OS,
/// and so it will `panic!`.
///
/// This is because any node in the list should only be in the list for the
/// duration of an insert future, which borrows the list -- preventing it from
/// being dropped.
///
/// This code should be unreachable in practice, because lists are borrowed by
/// the insert futures, and thus kept alive while non-empty.
#[pinned_drop]
impl<T, M> PinnedDrop for List<T, M> {
    fn drop(self: Pin<&mut Self>) {
        // It's not immediately clear to me what the Drop behavior should
        // be. In particular, if the list is dropped while non-empty, should
        // its nodes be awoken? On the one hand, whatever condition they're
        // waiting for hasn't happened, so waking them seems misleading; on
        // the other hand, the condition *will never happen,* so if we don't
        // wake them now, they'll sleep, possibly forever.
        //
        // When in doubt: panic and set the behavior later.
        #[cfg(debug_assertions)]
        cheap_assert!(self.is_empty());
    }
}

impl<T: core::fmt::Debug, M: core::fmt::Debug> core::fmt::Debug for List<T, M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("List")
            .field("last", debug_link(&self.root, &self.root.prev))
            .field("first", debug_link(&self.root, &self.root.next))
            .finish()
    }
}

/// Internal future type used for `insert_and_wait`. Gotta express this as a
/// named type because it needs a custom `Drop` impl.
struct WaitForDetach<'node, 'list, T, M> {
    node: Pin<&'node Node<T, M>>,
    list: Pin<&'list List<T, M>>,
    state: Cell<WaitState>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum WaitState {
    NotYetAttached,
    Attached,
    DetachedAndPolled,
}

impl<T: PartialOrd, M> Future for WaitForDetach<'_, '_, T, M> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut core::task::Context<'_>)
        -> Poll<Self::Output>
    {
        match self.state.get() {
            WaitState::NotYetAttached => {
                // Do the insertion part. This used to be a separate `insert`
                // function, but that function had soundness risks and so I've
                // inlined it.
                let node = self.node;
                let nnn = NonNull::from(&*node);
                {
                    // Node should not already belong to a list. This is a
                    // debug_assert because this property _should be_ handled at
                    // compile time by taking ownership of the &mut Node while
                    // it's in a list.
                    debug_assert!(node.prev.get() == nnn);
                    debug_assert!(node.next.get() == nnn); // technically redundant

                    // Work through the nodes starting at the tail, looking for
                    // the soon-to-be `prev` of `node`. Use the root as a
                    // sentinel to stop iteration.
                    let mut candidate = self.list.root.prev.get();
                    while candidate != NonNull::from(&self.list.root) {
                        // Safety: Link Valid Invariant means we can deref this
                        let cref = unsafe { candidate.as_ref() };

                        if cref.contents <= node.contents {
                            break;
                        }
                        candidate = cref.prev.get();
                    }

                    // `candidate` is either a neighbor node, or the root; in
                    // the latter case, `node` is becoming the new tail of the
                    // list.
                    node.prev.set(candidate);
                    // Safety: Link Valid Invariant
                    let cref = unsafe { candidate.as_ref() };
                    node.next.set(cref.next.get());
                    // Safety: Link Valid Invariant
                    unsafe {
                        cref.next.get().as_ref().prev.set(nnn);
                    }
                    cref.next.set(nnn);
                }

                self.state.set(WaitState::Attached);
                self.node.waker.update(cx.waker().clone());
                Poll::Pending
            }
            WaitState::Attached => {
                // See if we've detached.
                if self.node.is_detached() {
                    // The node is not attached to any list, but we're still borrowing
                    // it until we're dropped, so we don't need to replace the node
                    // field contents -- just set a flag to skip work in the Drop impl.
                    self.state.set(WaitState::DetachedAndPolled);
                    Poll::Ready(())
                } else {
                    // The node remains attached to the list. While unlikely, it's
                    // possible that the waker has changed. Update it.
                    self.node.waker.update(cx.waker().clone());
                    Poll::Pending
                }
            }
            // This effectively "fuses" the future.
            WaitState::DetachedAndPolled => Poll::Ready(()),
        }
    }
}

impl<T, M> Drop for WaitForDetach<'_, '_, T, M> {
    fn drop(&mut self) {
        if self.state.get() == WaitState::Attached {
            self.node.detach();
        }
    }
}

#[pin_project(PinnedDrop)]
struct WaitWithCleanup<'node, 'list, T, M, F: FnOnce()> {
    #[pin]
    inner: WaitForDetach<'node, 'list, T, M>,
    cleanup: Option<F>,
}

impl<T: PartialOrd, M, F: FnOnce()> Future for WaitWithCleanup<'_, '_, T, M, F> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut core::task::Context<'_>)
        -> Poll<Self::Output>
    {
        self.project().inner.poll(cx)
    }
}

#[pinned_drop]
impl<T, M, F: FnOnce()> PinnedDrop for WaitWithCleanup<'_, '_, T, M, F> {
    fn drop(self: Pin<&mut Self>) {
        if self.inner.state.get() == WaitState::Attached && self.inner.node.is_detached() {
            // Uh oh, we have not had a chance to handle the detach.
            if let Some(cleanup) = self.project().cleanup.take() {
                cleanup();
            }
        }
    }
}

/// Convenience macro for creating a pinned list on the stack.
///
/// `create_list!(ident)` is equivalent to `let ident = ...;` -- it creates a
/// local variable called `ident`, holding an initialized list.
#[macro_export]
macro_rules! create_list {
    ($var:ident) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        #[allow(unused_unsafe)]
        let mut $var = core::pin::pin!(unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::List::new())
        });
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        #[allow(unused_unsafe)]
        unsafe {
            $crate::list::List::finish_init($var.as_mut());
        }
    };
}

/// Convenience macro for creating a pinned list on the stack, when the list is
/// using metadata.
///
/// `create_list_with_meta!(ident, meta)` is equivalent to `let ident = ...;` --
/// it creates a local variable called `ident`, holding an initialized list.
///
/// The `meta` value passed doesn't matter at all. It's requested here to avoid
/// requiring `M: Default`.
#[macro_export]
macro_rules! create_list_with_meta {
    ($var:ident, $met:expr) => {
        // Safety: we discharge the obligations of `new_with_meta` by pinning
        // and finishing the value, below, before it can be dropped.
        let $var = $met;
        #[allow(unused_unsafe)]
        let mut $var = core::pin::pin!(unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::List::new_with_meta($var))
        });
        // Safety: the value has not been operated on since `new_with_meta`
        // except for being pinned, so this operation causes it to become valid
        // and safe.
        #[allow(unused_unsafe)]
        unsafe {
            $crate::list::List::finish_init($var.as_mut());
        }
    };
    ($var:ident) => { $crate::create_list_with_meta!($var, core::default::Default::default()) };
}

/// Convenience macro for creating a pinned node on the stack.
///
/// `create_node!(ident, val)` is equivalent to `let ident = ...;` -- it
/// creates a local variable called `ident`, holding an initialized node. The
/// node's contents are set to `val` and it uses the `noop_waker` by default.
#[macro_export]
macro_rules! create_node {
    ($var:ident, $dl:expr, $w: expr) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let mut $var = core::pin::pin!(unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::Node::new(
                $dl, $w,
            ))
        });
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::list::Node::finish_init($var.as_mut());
        }
    };
    ($var:ident, $dl:expr) => {
        #[allow(deprecated)]
        $crate::create_node!($var, $dl, $crate::exec::noop_waker())
    };

}

/// Convenience macro for creating a pinned node on the stack with attached
/// metadata.
///
/// `create_node_with_meta!(ident, val, meta)` is equivalent to `let
/// ident = ...;` -- it creates a local variable called `ident`, holding an
/// initialized node. The node's contents are set to `val`, metadata is set to
/// `meta, and it uses the `noop_waker` by default.
#[macro_export]
macro_rules! create_node_with_meta {
    ($var:ident, $dl:expr, $meta:expr, $w: expr) => {
        let $var = ($dl, $meta, $w);
        // Safety: we discharge the obligations of `new_with_meta` by pinning and
        // finishing the value, below, before it can be dropped.
        let mut $var = core::pin::pin!(unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::Node::new_with_meta(
                $var.0, $var.1, $var.2,
            ))
        });
        // Safety: the value has not been operated on since `new_with_meta`
        // except for being pinned, so this operation causes it to become valid
        // and safe.
        unsafe {
            $crate::list::Node::finish_init($var.as_mut());
        }
    };
    ($var:ident, $dl:expr, $meta:expr) => {
        $crate::create_node_with_meta!($var, $dl, $meta, $crate::exec::noop_waker())
    }
}

//! Doubly-linked intrusive lists for scheduling and waking.
//!
//! A [`List<T>`][List] keeps track of nodes (of type [`Node<T>`][Node]) that
//! each contain some value `T`. The list is kept in *sorted* order by comparing
//! the `T`s:
//!
//! - [`List::insert_and_wait`] traverses the list to insert the `Node` in its
//!   proper place, and then waits for the node to be kicked back out.
//! - [`List::wake_less_than`] starts at one end and removes every `Node` with a
//!   value less than a threshold.
//!
//! The sort order is used to order things by timestamps, but you may find other
//! uses for it.
//!
//! If you just want to keep things in a list, and don't care about order or
//! need to associate a timestamp, simply use `List<()>`. This disables the
//! sorting and removes the order-related fields from both the list and node.
//!
//! # How to use for sleep/wake
//!
//! The basics are straightforward: given a `List` tracking waiters on a
//! particular event, create a `Node` and `insert_and_wait` it. At some future
//! point in a concurrent process or interrupt handler, one of the `wake_*`
//! methods on `List` gets called, and the `Node` will be removed and its
//! associated `Waker` invoked, causing `insert_and_wait` to return.
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
//! os::create_node!(my_node, (), os::exec::noop_waker());
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
use core::task::{Poll, RawWaker, RawWakerVTable, Waker};
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
/// means at most once of its operations (below) is executing at a time.
///
/// - The operations will produce temporary references (both `&` and `&mut`)
/// into the `UnsafeCell`, but will only produce one such reference at a time,
/// and won't let it escape the function. This prevents aliasing in both
/// directions, and deallocation of data while a reference exists.
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
/// A node contains two pieces of metadata: the `waker` and the `contents`. The
/// `waker` is a `core::task::Waker`, an abstract reference to a task that
/// wishes to be woken up at some point. The `contents` is some `T`, and is
/// typically a timestamp. Inserting a node into a list requires that `T` be
/// `PartialOrd`, and the list will be maintained in ascending sorted order by
/// each node's `contents`. If you don't require this, `Node<()>` degenerates
/// into an insertion-order list.
#[pin_project(PinnedDrop)]
pub struct Node<T> {
    prev: Cell<NonNull<Self>>,
    next: Cell<NonNull<Self>>,
    waker: WakerCell,
    contents: T,
    _marker: NotSendMarker,
}

impl<T> Node<T> {
    /// Creates a `Node` in a semi-initialized state.
    ///
    /// # Safety
    ///
    /// The result is not safe to use or drop yet. You must move it to its final
    /// resting place, pin it, and call `finish_init`.
    pub unsafe fn new(contents: T, waker: Waker) -> ManuallyDrop<Self> {
        ManuallyDrop::new(Node {
            prev: Cell::new(NonNull::dangling()),
            next: Cell::new(NonNull::dangling()),
            waker: WakerCell::new(waker),
            contents,
            _marker: NotSendMarker::default(),
        })
    }

    /// Finishes initialization of a node, discharging the obligations placed on
    /// you by `new`.
    ///
    /// # Safety
    ///
    /// To use this safely, you must call this on the pinned result of `new()`
    /// before doing *anything else* with it.
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
}

/// A `Node` will detach itself from any list on drop.
#[pinned_drop]
impl<T> PinnedDrop for Node<T> {
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

impl<T: core::fmt::Debug> core::fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Node")
            .field("prev", debug_link(self, &self.prev))
            .field("next", debug_link(self, &self.next))
            .field("waker", &"...")
            .field("contents", &self.contents)
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
/// # Drop
///
/// You must remove/wake all the nodes in a list before dropping the list.
/// Dropping a list without emptying it is treated as a programming error, and
/// will panic.
///
/// This isn't the only way we could do things, but it is the safest. If you're
/// curious about the details, see the source code for `Drop`.
#[pin_project(PinnedDrop)]
pub struct List<T> {
    #[pin]
    root: Node<T>,
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
        // Safety: Node::new is unsafe because it produces a node that cannot be
        // safely dropped. We punt its obligations down the road by re-wrapping
        // it in our _own_ unsafe ManuallyDrop structure.
        let node = unsafe {
            Node::new(
                T::default(),
                exploding_waker(),
            )
        };
        ManuallyDrop::new(List {
            root: ManuallyDrop::into_inner(node),
            _marker: NotSendMarker::default(),
        })
    }
}

impl<T> List<T> {
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
}

impl<T: PartialOrd> List<T> {
    /// Inserts `node` into this list, maintaining ascending sort order, and
    /// then waits for it to be kicked back out.
    ///
    /// Specifically, `node` will be placed just *before* the first item in the
    /// list whose `contents` are greater than or equal to `node.contents`, if
    /// such an item exists, or at the end if not.
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
    /// polled, then you, the user, have a decision to make. If the node
    /// is likely to have been detached with `wake_one`, then the event that
    /// caused the wake may be lost if this future is dropped now without being
    /// polled. To handle this race condition, use
    /// `insert_and_wait_with_cleanup` instead.
    ///
    /// If, however, you don't use `wake_one` on this list, don't worry about
    /// it.
    ///
    /// # Panics
    ///
    /// If `node` is not detached (if it's in another list) when this is called.
    /// This should be pretty difficult to achieve in practice.
    pub fn insert_and_wait<'list, 'node>(
        self: Pin<&'list Self>,
        node: Pin<&'node mut Node<T>>,
    ) -> impl Future<Output = ()> + Captures<(&'list Self, &'node mut Node<T>)> {
        self.insert_and_wait_with_cleanup(
            node,
            || (),
        )
    }

    /// Inserts `node` into this list, maintaining ascending sort order, and
    /// then waits for it to be kicked back out.
    ///
    /// Specifically, `node` will be placed just *before* the first item in the
    /// list whose `contents` are greater than or equal to `node.contents`, if
    /// such an item exists, or at the end if not.
    ///
    /// When the returned future completes, `node` has been detached again.
    ///
    /// The `cleanup` action is performed in only one circumstance:
    ///
    /// 1. `node` has been detached by some other code,
    /// 2. The returned `Future` has not yet been polled, and
    /// 3. It is being dropped.
    ///
    /// This gives you an opportunity to e.g. wake another node.
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
        node: Pin<&'node mut Node<T>>,
        cleanup: F,
    ) -> impl Future<Output = ()> + Captures<(&'list Self, &'node mut Node<T>)> {
        // We required `node` to be `mut` to prove exclusive ownership, but we
        // don't actually need to mutate it -- and we're going to alias it. So,
        // downgrade.
        let node = node.into_ref();

        WaitForDetach {
            node,
            list: self,
            state: Cell::new(WaitState::NotYetAttached),
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
    pub fn wake_less_than(self: Pin<&Self>, threshold: T) {
        // Work through the nodes from the head, using the root as a sentinel to
        // stop iteration.
        let mut candidate = self.root.next.get();
        while candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant
            let cref = unsafe { Pin::new_unchecked(candidate.as_ref()) };
            if cref.contents > threshold {
                break;
            }
            // Copy the next pointer before detaching.
            let next = cref.next.get();
            cref.detach();
            cref.waker.wake_by_ref();

            candidate = next;
        }
    }
}

impl List<()> {
    /// Convenience method for waking all the waiters on an unsorted list,
    /// because `wake_less_than(())` looks weird.
    pub fn wake_all(self: Pin<&Self>) {
        self.wake_less_than(())
    }

    /// Wakes the oldest waiter on an unsorted list.
    ///
    /// Returns a flag indicating whether anything was done (i.e. whether the
    /// list was found empty).
    pub fn wake_one(self: Pin<&Self>) -> bool {
        let candidate = self.root.prev.get();
        if candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant
            let cref = unsafe { Pin::new_unchecked(candidate.as_ref()) };
            cref.detach();
            cref.waker.wake_by_ref();
            true
        } else {
            false
        }
    }
}

/// Dropping a non-empty list currently indicates a programming error in the OS,
/// and so it will `panic!`.
///
/// This is because any node in the list should only be in the list for the
/// duration of an insert future, which borrows the list -- preventing it from
/// being dropped.
#[pinned_drop]
impl<T> PinnedDrop for List<T> {
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
        cheap_assert!(self.root.is_detached());
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for List<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("List")
            .field("last", debug_link(&self.root, &self.root.prev))
            .field("first", debug_link(&self.root, &self.root.next))
            .finish()
    }
}
/// Internal future type used for `insert_and_wait`. Gotta express this as a
/// named type because it needs a custom `Drop` impl.
struct WaitForDetach<'node, 'list, T, F: FnOnce()> {
    node: Pin<&'node Node<T>>,
    list: Pin<&'list List<T>>,
    state: Cell<WaitState>,
    cleanup: Option<F>,
}

#[derive(Copy, Clone, Debug)]
enum WaitState {
    NotYetAttached,
    Attached,
    DetachedAndPolled,
}

impl<T: PartialOrd, F: FnOnce()> Future for WaitForDetach<'_, '_, T, F> {
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

                    // Work through the nodes starting at the head, looking for
                    // the soon-to-be `next` of `node`. Use the root as a
                    // sentinel to stop iteration.
                    let mut candidate = self.list.root.next.get();
                    while candidate != NonNull::from(&self.list.root) {
                        // Safety: Link Valid Invariant means we can deref this
                        let cref = unsafe { candidate.as_ref() };

                        if cref.contents >= node.contents {
                            break;
                        }
                        candidate = cref.next.get();
                    }

                    // `candidate` is either a neighbor node, or the root; in
                    // the latter case, `node` is becoming the new head of the
                    // list.
                    node.next.set(candidate);
                    // Safety: Link Valid Invariant
                    let cref = unsafe { candidate.as_ref() };
                    node.prev.set(cref.prev.get());
                    // Safety: Link Valid Invariant
                    unsafe {
                        cref.prev.get().as_ref().next.set(nnn);
                    }
                    cref.prev.set(nnn);
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

impl<T, F: FnOnce()> Drop for WaitForDetach<'_, '_, T, F> {
    fn drop(&mut self) {
        match self.state.get() {
            WaitState::NotYetAttached => {
                // No work to do here.
            }
            WaitState::Attached => {
                if self.node.is_detached() {
                    // Uh oh, we have not had a chance to handle the detach.
                    if let Some(cleanup) = self.cleanup.take() {
                        cleanup();
                    }
                } else {
                    // If _we_ detach ourselves, we don't run the cleanup
                    // action.
                    self.node.detach();
                }

            }
            WaitState::DetachedAndPolled => {
                // No work to do here either.
            }
        }
    }
}

/// Used to construct wakers that will crash the program if used.
///
/// We use this for the placeholder Waker installed in List, because it should
/// never be awoken -- that would indicate list corruption.
static EXPLODING_VTABLE: RawWakerVTable = {
    // Reduce number of panic sites
    #[inline(never)]
    fn mono_explode() -> ! {
        panic!("list inconsistency")
    }

    fn explode<T>(_: *const ()) -> T {
        mono_explode()
    }

    RawWakerVTable::new(
        explode, // clone
        explode, // wake
        explode, // wake_by_ref
        |_| (),  // drop
    )
};

/// Makes a `Waker` that will panic if used in any way other than being dropped.
///
/// If this looks like a total hack, that's because it is. To reduce code
/// duplication, `List` contains a `Node`, and `Node` of course must hold a
/// `Waker`. Since we never intend to use the `Waker` stored in `List`, we use
/// an exploding waker.
fn exploding_waker() -> Waker {
    // Safety: the EXPLODING_VTABLE doesn't dereference the context pointer at
    // all, so we could pass literally anything here and be safe.
    unsafe {
        Waker::from_raw(RawWaker::new(core::ptr::null(), &EXPLODING_VTABLE))
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

/// Convenience macro for creating a pinned node on the stack.
///
/// `create_node!(ident, val, waker)` is equivalent to `let ident = ...;` -- it
/// creates a local variable called `ident`, holding an initialized node. The
/// node's contents are set to `val`, and its waker is `waker`.
///
/// (Note: `waker` should almost always be
/// [`exec::noop_waker()`][crate::exec::noop_waker].)
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
}

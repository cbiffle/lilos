//! Doubly-linked intrusive lists for scheduling and waking.
//!
//! # How to use for sleep/wake
//!
//! The basics are straightforward: given a `List` tracking waiters on a
//! particular event, create a `Node` and `insert` it. At some future point,
//! when one of the `wake_*` methods on `List` gets called, the `Node` will be
//! removed and its associated `Waker` invoked.
//!
//! But what does the waiting task do in the mean time? The answer is slightly
//! subtle.
//!
//! As with any blocking future, the task must be prepared to tolerate spurious
//! wakeups. Because many futures are bundled into a single task, but wakeups
//! happen at *task* level, the fact that your *task* has awoken does *not*
//! imply that your event has happened. Check.
//!
//! The easiest way to check is to inspect the `Node` and see if it's still in a
//! `List` (using `is_detached`). At the moment, this check is sufficient; the
//! other condition that could cause a `Node` to leave a `List` is if the `List`
//! were dropped, but we don't currently allow full lists to be dropped.
//!
//! This insert-and-wait-for-detach pattern is common enough that it's wrapped
//! up in the method `List::insert_and_wait`.

// Implementation safety notes:
//
// The safety comments in this module reference the following invariants:
//
// Link Valid Invariant: all the link pointers (that is, `Node::prev` and
// `Node::next`) transitively reachable from either `List` or `Node` are valid /
// not dangling. We maintain this by only setting them to the addresses of
// pinned structures, and ensuring that the `Drop` impl of those pinned
// structures will remove their addresses from any link.

use core::cell::Cell;

use core::future::Future;
use core::mem::ManuallyDrop;
use core::pin::Pin;
use core::ptr::NonNull;
use core::task::{Poll, RawWaker, RawWakerVTable, Waker};

use crate::NotSendMarker;

/// A member of a list.
///
/// A node is either *detached* (not in a list) or *attached* (in a list). After
/// creation it is initially detached; you can attach it to a list using
/// `List::insert`. To detach it, either call `Node::detach` or drop the node.
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
pub struct Node<T> {
    prev: Cell<NonNull<Self>>,
    next: Cell<NonNull<Self>>,
    waker: Waker,
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
            waker,
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
        // Safety: Link Valid Invariant allows deref of prev/next
        unsafe {
            self.prev.get().as_mut().next.set(self.next.get());
            self.next.get().as_mut().prev.set(self.prev.get());
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
impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        // We assume that all nodes are pinned.
        inner_drop(unsafe { Pin::new_unchecked(self) });

        fn inner_drop<T>(this: Pin<&mut Node<T>>) {
            this.as_ref().detach();
        }
    }
}

/// A list of `Node`s.
///
/// The list references but does not own the nodes.
///
/// Because lists contain self-referential pointers, creating one is somewhat
/// involved. Use the `create_list` macro when possible, or see `List::new` for
/// instructions.
pub struct List<T> {
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
    /// 1. Drop it immediately.
    /// 2. Unwrap it, pin it, and then call `List::finish_init`.
    pub unsafe fn new() -> ManuallyDrop<List<T>> {
        ManuallyDrop::new(List {
            root: ManuallyDrop::into_inner(Node::new(
                T::default(),
                exploding_waker(),
            )),
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
        Node::finish_init(list.root_mut());
    }

    fn root_mut(self: Pin<&mut Self>) -> Pin<&mut Node<T>> {
        unsafe { Pin::new_unchecked(&mut Pin::get_unchecked_mut(self).root) }
    }
}

impl<T: PartialOrd> List<T> {
    /// Inserts `node` into this list, maintaining ascending sort order.
    ///
    /// Specifically, `node` will be placed just *before* the first item in the
    /// list whose `contents` are greater than or equal to `node.contents`, if
    /// such an item exists, or at the end if not.
    ///
    /// # Panics
    ///
    /// If `node` is not detached.
    pub fn insert(self: Pin<&Self>, node: Pin<&mut Node<T>>) {
        let nnn = NonNull::from(&*node);
        // Node should not already belong to a list.
        assert!(node.prev.get() == nnn);
        debug_assert!(node.next.get() == nnn); // technically redundant

        // Work through the nodes starting at the head, looking for the future
        // `next` of `node`. Use the root as a sentinel to stop iteration.
        let mut candidate = self.root.next.get();
        while candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant means we can deref this
            let cref = unsafe { candidate.as_ref() };

            if cref.contents >= node.contents {
                break;
            }
            candidate = cref.next.get();
        }

        // `candidate` is either a neighbor node, or the root; in the latter
        // case, `node` is becoming the new head of the list.
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

    /// Variant of `insert` that can be used to wait for the `Node` to be kicked
    /// back out of the list.
    pub fn insert_and_wait<'a>(
        self: Pin<&Self>,
        mut node: Pin<&'a mut Node<T>>,
    ) -> impl Future<Output = ()> + 'a {
        self.insert(node.as_mut());
        futures::future::poll_fn(move |_| {
            if node.is_detached() {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        })
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
    pub fn wake_one(self: Pin<&Self>) {
        let candidate = self.root.prev.get();
        if candidate != NonNull::from(&self.root) {
            // Safety: Link Valid Invariant
            let cref = unsafe { Pin::new_unchecked(candidate.as_ref()) };
            cref.detach();
            cref.waker.wake_by_ref();
        }
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        // We assume we are pinned.
        inner_drop(unsafe { Pin::new_unchecked(self) });

        fn inner_drop<T>(this: Pin<&mut List<T>>) {
            // It's not immediately clear to me what the Drop behavior should
            // be. In particular, if the list is dropped while non-empty, should
            // its nodes be awoken? On the one hand, whatever condition they're
            // waiting for hasn't happened, so waking them seems misleading; on
            // the other hand, the condition *will never happen,* so if we don't
            // wake them now, they'll sleep, possibly forever.
            //
            // When in doubt: panic and set the behavior later.
            assert!(this.root.is_detached());
        }
    }
}

/// Used to construct wakers that will crash the program if used.
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

/// Creates a pinned list on the stack.
#[macro_export]
macro_rules! create_list {
    ($var:ident) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::List::new())
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::list::List::finish_init($var.as_mut());
        }
    };
}

/// Creates a pinned node on the stack.
#[macro_export]
macro_rules! create_node {
    ($var:ident, $dl:expr, $w: expr) => {
        // Safety: we discharge the obligations of `new` by pinning and
        // finishing the value, below, before it can be dropped.
        let $var = unsafe {
            core::mem::ManuallyDrop::into_inner($crate::list::Node::new(
                $dl, $w,
            ))
        };
        pin_utils::pin_mut!($var);
        // Safety: the value has not been operated on since `new` except for
        // being pinned, so this operation causes it to become valid and safe.
        unsafe {
            $crate::list::Node::finish_init($var.as_mut());
        }
    };
}

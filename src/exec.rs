//! A system for polling an array of tasks forever, plus `Notify` and other
//! scheduling tools.
//!
//! **Note:** for our purposes, a _task_ is an independent top-level future
//! managed by the scheduler polling loop. There are a fixed set of tasks,
//! provided to the scheduler at startup. This is distinct from the casual use
//! of "task" to mean a piece of code that runs concurrently with other code;
//! we'll use the term "concurrent process" for this. The fixed set of tasks
//! managed by the scheduler can execute an _arbitrary number_ of concurrent
//! processes.
//!
//! # Scheduler entry point
//!
//! The mechanism for "starting the OS" is [`run_tasks`].
//!
//! # Time
//!
//! The executor uses the timekeeping provided by the [`time`][crate::time]
//! module to enable tasks to be woken at particular times. [`sleep_until`]
//! produces a future that resolves at a particular time, while [`sleep_for`]
//! expresses the time relative to the current time.
//!
//! As their names imply, these functions can be used to delay the current task
//! -- but they can also be used to impose a timeout on any async operation, by
//! using [`select!`](https://docs.rs/futures/0.3/futures/macro.select.html).
//!
//! For the common case of needing to do an operation periodically, consider
//! [`every_until`] or [`PeriodicGate`], which try to minimize jitter and drift.
//!
//! # Interrupts, wait, and notify
//!
//! So, you've given the OS an array of tasks that need to each be polled
//! forever. The OS could simply poll every task in a big loop (a pattern known
//! in embedded development as a "superloop"), but this has some problems:
//!
//! 1. By constantly checking whether each task can make progress, we keep the
//!    CPU running full-tilt, burning power needlessly.
//!
//! 2. Because any given task may have to wait for *every other task* to be
//!    polled before it gets control, the minimum response latency to events is
//!    increased, possibly by a lot.
//!
//! We can do better.
//!
//! There are, in practice, two reasons why a task might yield.
//!
//! 1. Because it wants to leave room for other tasks to execute during a
//!    long-running operation. In this case, we actually *do* want to come right
//!    back and poll the task. (To do this, use [`yield_cpu`].)
//!
//! 2. Because it is waiting for an event -- a particular timer tick, an
//!    interrupt from a peripheral, a signal from another task, etc. In this
//!    case, we don't need to poll the task again *until that event occurs.*
//!
//! The OS tracks a *wake bit* per task. When this bit is set, it means that
//! the task should be polled. Each time through the outer poll loop, the OS
//! will determine which tasks have their wake bits set, *clear the wake bits*,
//! and then poll the tasks.
//!
//! (Tasks might be polled even when their bit isn't set -- this is a waste of
//! energy, but is also something that Rust `Future`s are expected to tolerate.
//! Giving the OS some slack on this dramatically simplifies the implementation.
//! However, the OS tries to poll the smallest feasible set of tasks each time
//! it polls.)
//!
//! The need to set and check wake bits is embodied by the [`Notify`] type,
//! which provides a kind of event broadcast. Tasks can subscribe to a `Notify`,
//! and when it is signaled, all subscribed tasks get their wake bits set.
//!
//! `Notify` is very low level -- the more pleasant abstractions of
//! [`queue`][crate::queue], [`mutex`][crate::mutex], and
//! [`sleep_until`]/[`sleep_for`] are built on top of it. However, `Notify` is
//! the only OS facility that's safe to use from interrupt service routines,
//! making it an ideal way to wake tasks when hardware events occur.
//!
//! Here is a basic example of using `Notify`; see the `queue` and `mutex`
//! modules for details on the higher-level options.
//!
//! ```ignore
//! /// Global notification signal for ethernet interrupts.
//! static ETH_NOTIFY: os::exec::Notify = os::exec::Notify::new();
//!
//! #[interrupt]
//! fn ETH() {
//!     // omitted: code to clear interrupt condition so it doesn't just recur
//!
//!     // Signal any tasks waiting for this interrupt.
//!     ETH_NOTIFY.notify();
//! }
//!
//! async fn ethernet_driver() {
//!     // ... stuff ...
//!
//!     // Wait for the interrupt we care about. Check the status register to
//!     // distinguish interrupt conditions and to handle spurious wakeups.
//!     ETH_NOTIFY.wait_until(|| dma.dmasr.read().nis());
//!
//!     // ... continue ...
//! }
//! ```
//!
//! # Building your own task notification mechanism
//!
//! If `Notify` doesn't meet your needs, you can use the [`wake_task_by_index`]
//! and [`wake_tasks_by_mask`] functions to explicitly wake one or more tasks.
//! Because tasks are required to tolerate spurious wakeups, both of these
//! functions are safe: spamming tasks with wakeup requests merely wastes
//! energy and time.
//!
//! Both of these functions expose the fact that the scheduler tracks wake bits
//! in a single `usize`. When waking a task with index 0 (mask `1 << 0`), we're
//! actually waking any task where `index % 32 == 0`. Very complex systems with
//! greater than 32 top-level tasks will thus experience more spurious wakeups.
//! The advantage of this "lossy" technique is that wake bit manipulation is
//! very, very cheap.
//!
//! # Idle behavior
//!
//! When no tasks have their wake bits set, the default behavior is to idle the
//! processor using the `WFI` instruction. You can override this behavior by
//! starting the scheduler with [`run_tasks_with_idle`] or
//! [`run_tasks_with_preemption_and_idle`], which let you substitute a custom
//! "idle hook" to execute when no tasks are ready.
//!
//! # Adding preemption
//!
//! By default, the scheduler does not preempt task code: task poll routines are
//! run cooperatively, and ISRs are allowed only in between polls. This
//! increases interrupt response latency, because if an event occurs while
//! polling tasks, all polling must complete before the ISR is run.
//!
//! Applications can override this by starting the scheduler with
//! [`run_tasks_with_preemption`] or [`run_tasks_with_preemption_and_idle`].
//! These entry points let you set a _preemption policy_, which allows ISRs
//! above some priority level to preempt task code. (Tasks still cannot preempt
//! one another.)

use core::future::Future;
use core::mem;
use core::pin::Pin;
use core::sync::atomic::{AtomicUsize, AtomicPtr, Ordering};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use core::time::Duration;

use crate::list::List;
use crate::time::Ticks;
use crate::FromNever;

/// How many bits in a `usize`, and thus in a pointer?
const USIZE_BITS: usize = mem::size_of::<usize>() * 8;

/// Accumulates bitmasks from wakers as they are invoked. The executor
/// atomically checks and clears this at each iteration.
static WAKE_BITS: AtomicUsize = AtomicUsize::new(0);

/// VTable for our wakers. Our wakers store a task notification bitmask in their
/// "pointer" member, and atomically OR it into `WAKE_BITS` when invoked.
static VTABLE: RawWakerVTable = RawWakerVTable::new(
    // clone
    |p| RawWaker::new(p, &VTABLE),
    // wake
    |p| wake_tasks_by_mask(p as usize),
    // wake_by_ref
    |p| wake_tasks_by_mask(p as usize),
    // drop
    |_| (),
);

/// Produces a `Waker` that will wake *at least* task `index` on invocation.
///
/// Technically, this will wake any task `n` where `n % 32 == index % 32`.
fn waker_for_task(index: usize) -> Waker {
    let mask = 1usize << (index % USIZE_BITS);
    // Safety: Waker::from_raw is unsafe because bad things happen if the
    // combination of this particular pointer and the functions in the vtable
    // don't meet the Waker contract or are incompatible. In our case, our
    // vtable functions are actually entirely safe, since we're passing an
    // integer as a pointer.
    unsafe {
        Waker::from_raw(RawWaker::new(mask as *const (), &VTABLE))
    }
}

/// Exploits our known Waker structure to extract the notification mask from a
/// Waker.
///
/// If this is applied to a Waker that isn't from this executor (specifically,
/// one not generated by `waker_for_task`), this will cause spurious and almost
/// certainly incorrect wakeups. Currently I don't feel like that risk is great
/// enough to mark ths unsafe -- it can't violate *memory* safety for certain.
///
/// In practice this function compiles down to a single inlined load
/// instruction.
fn extract_mask(waker: &Waker) -> usize {
    // Determine whether the pointer member comes first or second within the
    // representation of RawWaker. This is currently compile-time simplified
    // and goes away.
    //
    // Safety: we are using `transmute` to inspect the raw composition of a
    // Waker. That direction is safe -- it's a fancy version of casting a
    // pointer to an integer. Transmuting the _other_ direction would be very
    // unsafe.
    let ptr_first = unsafe {
        let (cell0, _) = mem::transmute::<_, (usize, usize)>(
            Waker::from_raw(RawWaker::new(
                1234 as *const (),
                &VTABLE,
            ))
        );
        cell0 == 1234usize
    };

    // Safety: at the moment, `Waker` consists exactly of a `*const ()` and a
    // `&'static RawWakerVTable` (or equivalent pointer), and this is unlikely
    // to change. We've already verified above that we can find the parameter
    // word, which is what we care about. Extracting it cannot violate memory
    // safety, since we're just reading initialized memory.
    unsafe {
        let parts = &*(waker as *const _ as *const (usize, usize));
        if ptr_first {
            parts.0
        } else {
            parts.1
        }
    }
}

/// Used to construct wakers do nothing, as a placeholder.
static NOOP_VTABLE: RawWakerVTable = RawWakerVTable::new(
    |x| RawWaker::new(x, &NOOP_VTABLE), // clone
    |_| (),                             // wake
    |_| (),                             // wake_by_ref
    |_| (),                             // drop
);

/// Returns a [`Waker`] that doesn't do anything and costs nothing to `clone`.
/// This is useful as a placeholder before a *real* `Waker` becomes available.
pub fn noop_waker() -> Waker {
    // Safety: Waker::from_raw is unsafe because the Waker can do weird and
    // destructive stuff if either the pointer, or the vtable functions, don't
    // meet its contract. Our no-op functions _trivially_ meet its contract.
    unsafe {
        Waker::from_raw(RawWaker::new(core::ptr::null(), &NOOP_VTABLE))
    }
}

/// Polls `future` in a context where the `Waker` will signal the task with
/// index `index`.
fn poll_task<T>(
    index: usize,
    future: Pin<&mut dyn Future<Output = T>>,
) -> Poll<T> {
    future.poll(&mut Context::from_waker(&waker_for_task(index)))
}

/// Selects an interrupt control strategy for the scheduler.
#[derive(Copy, Clone, Debug)]
pub enum Interrupts {
    /// Use PRIMASK to completely disable interrupts while task code is running.
    Masked,
    /// Use BASEPRI to mask interrupts of the given priority and lower.
    Filtered(u8),
}

impl Interrupts {
    fn scope<R>(self, body: impl FnOnce() -> R) -> R {
        let r = match self {
            Interrupts::Masked => {
                let prev = cortex_m::register::primask::read();
                cortex_m::interrupt::disable();

                let r = body();

                if prev == cortex_m::register::primask::Primask::Active {
                    // Safety: interrupts were just on, so this won't compromise
                    // memory safety.
                    unsafe {
                        cortex_m::interrupt::enable();
                    }
                }

                r
            }
            Interrupts::Filtered(priority) => {
                let prev = cortex_m::register::basepri::read();
                cortex_m::register::basepri_max::write(priority);

                let r = body();

                // Safety: just restoring state
                unsafe {
                    cortex_m::register::basepri::write(prev);
                }

                r
            }
        };

        // Make sure newly-enabled interrupt handlers fire.
        cortex_m::asm::isb();

        r
    }
}

/// Runs the given futures forever, sleeping when possible. Each future acts as
/// a task, in the sense of `core::task`.
///
/// The futures are defined as returning `!`, which means they won't complete.
///
/// Not all tasks are polled every time through the loop. On the first
/// iteration, only the tasks with a corresponding bit set in `initial_mask` are
/// polled; on subsequent futures, only tasks awoken by the *previous* iteration
/// are called.
///
/// Any time polling completes with *no* tasks awoken, code will never run again
/// unless an interrupt handler wakes tasks using `Notify`. And so, when we
/// detect this condition, we use the `WFI` instruction to idle the processor
/// until an interrupt arrives. This has the advantages of using less power and
/// having more predictable response latency than spinning.
pub fn run_tasks(
    futures: &mut [Pin<&mut dyn Future<Output = !>>],
    initial_mask: usize,
) -> ! {
    // Safety: we're passing Interrupts::Masked, the always-safe option
    unsafe {
        run_tasks_with_preemption_and_idle(
            futures,
            initial_mask,
            Interrupts::Masked,
            cortex_m::asm::wfi,
        )
    }
}

/// Extended version of `run_tasks` that replaces the default idle behavior
/// (sleeping until the next interrupt) with code of your choosing.
///
/// If you would like the processor to sleep when idle, you will need to call
/// WFI yourself from within the implementation of `idle_hook`.
///
/// See [`run_tasks`] for more details.
pub fn run_tasks_with_idle(
    futures: &mut [Pin<&mut dyn Future<Output = !>>],
    initial_mask: usize,
    idle_hook: impl FnMut(),
) -> ! {
    // Safety: we're passing Interrupts::Masked, the always-safe option
    unsafe {
        run_tasks_with_preemption_and_idle(
            futures,
            initial_mask,
            Interrupts::Masked,
            idle_hook,
        )
    }
}

/// Extended version of `run_tasks` that configures the scheduler with a custom
/// interrupt policy.
///
/// Passing `Interrupts::Masked` here gets the same behavior as `run_tasks`.
///
/// Passing `Interrupts::Filtered(p)` causes the scheduler to only disable
/// interrupts with priority equal to or numerically greater than `p`. This can
/// be used to ensure that the OS systick ISR (priority 0) can preempt
/// long-running tasks.
///
/// # Safety
///
/// This can be used safely as long as ISRs and task code that share data
/// structures use appropriate critical sections.
///
/// In particular, the *only* OS operation ISRs can perform in this case is
/// `Notify::notify`.
pub unsafe fn run_tasks_with_preemption(
    futures: &mut [Pin<&mut dyn Future<Output = !>>],
    initial_mask: usize,
    interrupts: Interrupts,
) -> ! {
    run_tasks_with_preemption_and_idle(
        futures,
        initial_mask,
        interrupts,
        cortex_m::asm::wfi,
    )
}

/// Extended version of `run_tasks` that configures the scheduler with a custom
/// interrupt policy and idle hook.
///
/// Passing `Interrupts::Masked` here gets the same behavior as
/// `run_tasks_with_idle`.
///
/// Passing `Interrupts::Filtered(p)` causes the scheduler to only disable
/// interrupts with priority equal to or numerically greater than `p`. This can
/// be used to ensure that the OS systick ISR (priority 0) can preempt
/// long-running tasks.
///
/// # Safety
///
/// This can be used safely as long as ISRs and task code that share data
/// structures use appropriate critical sections.
///
/// In particular, the *only* OS operation ISRs can perform in this case is
/// `Notify::notify`.
pub unsafe fn run_tasks_with_preemption_and_idle(
    futures: &mut [Pin<&mut dyn Future<Output = !>>],
    initial_mask: usize,
    interrupts: Interrupts,
    mut idle_hook: impl FnMut(),
) -> ! {
    WAKE_BITS.store(initial_mask, Ordering::SeqCst);

    // TODO make this list static for more predictable memory usage
    create_list!(timer_list);

    set_timer_list(timer_list, || loop {
        interrupts.scope(|| {
            // Scan for any expired timers.
            with_timer_list(|tl| tl.wake_less_than(Ticks::now()));

            // Capture and reset wake bits, then process any 1s.
            // TODO: this loop visits every future testing for 1 bits; it would
            // almost certainly be faster to visit the futures corresponding to
            // 1 bits instead. I have avoided this for now because of the
            // increased complexity.
            let mask = WAKE_BITS.swap(0, Ordering::SeqCst);
            for (i, f) in futures.iter_mut().enumerate() {
                if mask & (1 << (i % USIZE_BITS)) != 0 {
                    poll_task(i, f.as_mut()).from_never();
                }
            }

            // If none of the futures woke each other, we're relying on an
            // interrupt to set bits -- so we can sleep waiting for it.
            if WAKE_BITS.load(Ordering::SeqCst) == 0 {
                idle_hook();
            }

        });

        // Now interrupts are enabled for a brief period before diving back in.
        // Note that we allow interrupt-wake even when some wake bits are set;
        // this prevents ISR starvation by polling tasks.
    })
}

/// Constant that can be passed to `run_tasks` and `wake_tasks_by_mask` to mean
/// "all tasks."
pub const ALL_TASKS: usize = !0;

/// A lightweight task notification scheme that can safely be used from
/// interrupt handlers.
///
/// A `Notify` collects any number of task `Waker`s into a fixed-size structure
/// without heap allocation. It does this by coalescing the `Waker`s such that
/// they may become *imprecise*: firing the waker for task N may also spuriously
/// wake task M.
///
/// While this is often not the *ideal* strategy, it has the advantage that it
/// can be done safely from an ISR.
pub struct Notify {
    mask: AtomicUsize,
}

impl Notify {
    /// Creates a new `Notify` with no tasks waiting.
    pub const fn new() -> Self {
        Self {
            mask: AtomicUsize::new(0),
        }
    }

    /// Adds the `Waker` to the set of waiters.
    pub fn subscribe(&self, waker: &Waker) {
        self.mask.fetch_or(extract_mask(waker), Ordering::SeqCst);
    }

    /// Wakes tasks, at least all those whose waiters have been passed to
    /// `subscribe` since the last `notify`, possibly more.
    pub fn notify(&self) {
        wake_tasks_by_mask(self.mask.swap(0, Ordering::SeqCst))
    }

    /// Repeatedly calls `cond`, completing when it returns `true`. In between
    /// calls, subscribes to `notify`, so that the task will wake less often and
    /// leave CPU available for other things.
    ///
    /// This is appropriate if you know that any change to `cond`'s result will
    /// be preceded by some task calling `notify()`.
    pub fn wait_until<'a, 'b>(
        &'a self,
        mut cond: impl (FnMut() -> bool) + 'b,
    ) -> impl Future<Output = ()> + 'a
    where
        'b: 'a,
    {
        futures::future::poll_fn(move |cx| {
            if cond() {
                Poll::Ready(())
            } else {
                self.subscribe(cx.waker());
                Poll::Pending
            }
        })
    }

    pub fn wait_until2<'a, 'b>(
        &'a self,
        mut cond: impl (FnMut() -> bool) + 'b,
    ) -> impl Future<Output = ()> + 'a
    where
        'b: 'a,
    {
        futures::future::poll_fn(move |cx| {
            self.subscribe(cx.waker());
            if cond() {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        })
    }
}

/// Notifies the executor that any tasks whose wake bits are set in `mask`
/// should be polled on the next iteration.
///
/// This is a very low-level operation and is rarely what you want to use. See
/// `Notify`.
pub fn wake_tasks_by_mask(mask: usize) {
    WAKE_BITS.fetch_or(mask, Ordering::SeqCst);
}

/// Notifies the executor that the task with the given `index` should be polled
/// on the next iteration.
///
/// This operation isn't precise: it may wake other tasks, but it is guaranteed
/// to at least wake the desired task.
pub fn wake_task_by_index(index: usize) {
    wake_tasks_by_mask(1 << (index % USIZE_BITS));
}

/// Tracks the timer list currently in scope.
static TIMER_LIST: AtomicPtr<List<Ticks>> =
    AtomicPtr::new(core::ptr::null_mut());

/// Sets the timer list for the duration of `body`.
///
/// This doesn't nest, and will assert if you try.
fn set_timer_list<R>(
    list: Pin<&mut List<Ticks>>,
    body: impl FnOnce() -> R,
) -> R {
    // Prevent this from being used from interrupt context.
    assert!(cortex_m::register::apsr::read().bits() & 0xFF == 0);

    let old_list = TIMER_LIST.swap(
        // Safety: since we've gotten a &mut, we hold the only reference, so
        // it's safe for us to smuggle it through a pointer and reborrow it as
        // shared.
        unsafe { Pin::get_unchecked_mut(list) },
        Ordering::Acquire,
    );

    // Detect weird reentrant uses of this function. This would indicate an
    // internal error. Since this assert should only be checked on executor
    // startup, there is no need to optimize it away in release builds.
    assert!(old_list.is_null());

    let r = body();

    // Give up our scoped reference so the caller's &mut has no risk of
    // aliasing.
    TIMER_LIST.store(core::ptr::null_mut(), Ordering::Release);

    r
}

/// Nabs a reference to the current timer list and executes `body`.
///
/// This provides a safe way to access the timer thread local.
fn with_timer_list<R>(body: impl FnOnce(Pin<&List<Ticks>>) -> R) -> R {
    // Prevent this from being used from interrupt context.
    assert!(cortex_m::register::apsr::read().bits() & 0xFF == 0);

    let list_ref = {
        let tlptr = TIMER_LIST.load(Ordering::Acquire);
        assert!(!tlptr.is_null(), "with_timer_list outside of set_timer_list");

        // Safety: if it's not null, then it came from a `Pin<&mut>` that we
        // have been loaned. We do not treat it as a &mut anywhere, so we can
        // safely reborrow it as shared.
        unsafe {
            Pin::new_unchecked(&*tlptr)
        }
    };

    body(list_ref)
}

/// Sleeps until the system time is equal to or greater than `deadline`.
///
/// More precisely, `sleep_until(d)` returns a `Future` that will poll as
/// `Pending` until `Ticks::now() >= deadline`; then it will poll `Ready`.
///
/// If `deadline` is already in the past, this will instantly become `Ready`.
pub async fn sleep_until(deadline: Ticks) {
    // TODO: this early return means we can't simply return the insert_and_wait
    // future below, which is costing us some bytes of text.
    if Ticks::now() >= deadline {
        return;
    }

    crate::create_node!(node, deadline, noop_waker());

    // Insert our node into the pending timer list. If we get cancelled, the
    // node will detach itself as it's being dropped.
    with_timer_list(|tl| tl.insert_and_wait(node.as_mut())).await
}

/// Sleeps until the system time has increased by `d`.
///
/// More precisely, `sleep_for(d)` captures the system time, `t`, and returns a
/// `Future` that will poll as `Pending` until `Ticks::now() >= t + d`; then it
/// will poll `Ready`.
///
/// If `d` is 0, this will instantly become `Ready`.
pub fn sleep_for(d: Duration) -> impl Future<Output = ()> {
    sleep_until(Ticks::now() + d)
}

/// Returns a future that will be pending exactly once before resolving. This
/// has the effect of causing the calling future to yield by pending, before
/// resuming its work.
pub async fn yield_cpu() -> Yield {
    Yield { pending: true }
}

/// Type of future returned by `yield_cpu`.
pub struct Yield {
    pending: bool,
}

impl Future for Yield {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        // TODO: to make uncontested yields cheaper, it would be nice to check
        // the wake mask to see if anything else can run before pending. There
        // are two subtleties to doing this correctly:
        //
        // 1. Not just the upcoming wake mask, but the *current* wake mask,
        //    should be checked. The current one (which is a copy of the old
        //    upcoming value) is currently only held in a local in the executor;
        //    it would need to be published to a static.
        // 2. To avoid starving interrupts, this routine should briefly enable
        //    interrupts and allow them to write the wake mask.

        if core::mem::replace(&mut self.pending, false) {
            cx.waker().wake_by_ref();
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

/// Makes a future periodic, with a termination condition.
///
/// This will evaluate `action` periodically and poll the `Future` that results
/// until it completes before repeating.
///
/// Specifically, `action` will be called immediately, and then every `period`
/// thereafter. If the action future is still being polled when it comes time to
/// call `action` again, the call will be delayed, but will not be skipped.
/// Thus, you may observe rapid repeated calls to `action` to make up for lost
/// time.
///
/// This means that, if your requirement is to ensure that some amount of time
/// elapses *between* operations, this is *not* the right function -- you should
/// just `loop` and call `sleep_for` instead.
pub async fn every_until<F>(period: Duration, mut action: impl FnMut() -> F)
where
    F: Future<Output = bool>,
{
    let mut next = Ticks::now();
    loop {
        sleep_until(next).await;
        if action().await {
            break;
        }
        next += period;
    }
}

/// Utility for doing something periodically.
///
/// A `PeriodicGate` can be used to *gate* (pause) execution of a task until a
/// point in time arrives; that point in time is *periodic*, meaning it repeats
/// at regular intervals. For example, to call the function `f` every 30
/// milliseconds, you would write:
///
/// ```ignore
/// let gate = PeriodicGate::new(Duration::from_millis(30));
/// loop {
///     f();
///     gate.next_time().await;
/// }
/// ```
pub struct PeriodicGate {
    interval: Duration,
    next: Ticks,
}

impl PeriodicGate {
    /// Creates a periodic gate that can be used to release execution every
    /// `interval`, starting right now.
    pub fn new(interval: Duration) -> Self {
        PeriodicGate {
            interval,
            next: Ticks::now(),
        }
    }

    /// Returns a future that will resolve when it's time to execute again.
    pub async fn next_time(&mut self) {
        sleep_until(self.next).await;
        self.next += self.interval;
    }
}

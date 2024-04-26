//! OS test suite.
//!
//! The test suite is SoC-independent.

#![no_std]

mod list;
mod spsc;
mod mutex;
#[cfg(feature = "handoff")]
mod handoff;
#[cfg(feature = "semaphore")]
mod semaphore;
#[cfg(feature = "rwlock")]
mod rwlock;

use core::convert::Infallible;
use core::pin::pin;
use core::sync::atomic::{AtomicBool, Ordering};
use futures::FutureExt;

use cortex_m_semihosting::hprintln;
use lilos::exec;
use lilos::time;

pub fn run_test_suite(hz: u32) -> ! {
    // Check out peripherals from the runtime.
    let mut cp = cortex_m::Peripherals::take().unwrap();

    // Tasks
    let coordinator = pin!(task_coordinator());
    let flag_auto = pin!(task_set_a_flag_then_halt(&AUTO_FLAG));
    let flag_manual = pin!(task_set_a_flag_then_halt(&MUST_START_FLAG));
    let flag_manual2 = pin!(task_set_a_flag_then_halt(&MUST_NOT_START_FLAG));
    let waiting_for_notify = pin!(async {
        NOTIFY.until_next().await;
        NOTIFY_REACHED.store(true, Ordering::SeqCst);
        block_forever().await
    });

    let start_mask = 0b011;

    time::initialize_sys_tick(&mut cp.SYST, hz);
    exec::run_tasks(
        &mut [
            coordinator,
            flag_auto,
            flag_manual, // 2
            flag_manual2, // 3
            waiting_for_notify, // 4
        ],
        start_mask,
    )
}

static AUTO_FLAG: AtomicBool = AtomicBool::new(false);
static MUST_START_FLAG: AtomicBool = AtomicBool::new(false);
static MUST_NOT_START_FLAG: AtomicBool = AtomicBool::new(false);
static NOTIFY: exec::Notify = exec::Notify::new();
static NOTIFY_REACHED: AtomicBool = AtomicBool::new(false);

const A_BIT: core::time::Duration = core::time::Duration::from_millis(2);

macro_rules! async_tests {
    ($($(#[$attr:meta])* $name:path,)*) => {
        $(
            $(#[$attr])*
            {
                cortex_m_semihosting::hprint!(concat!(stringify!($name), "... "));
                $name().await;
                cortex_m_semihosting::hprintln!("OK");
            }
         )*
    };
}

async fn task_coordinator() -> Infallible {
    let tests = async {
        async_tests! {
            test_yield_cpu,
            test_other_tasks_started,
            test_clock_advancing,
            test_sleep_until_basic,
            test_sleep_until_multi,
            test_with_deadline_actively_polled,
            test_with_deadline_blocking,
            test_notify,

            list::test_node_basics,
            list::test_list_basics,
            list::test_insert_and_wait_not_eager,
            list::test_insert_and_wait_wake_one,
            list::test_wake_while_insert_order,
            list::test_insert_and_wait_cancel_behavior,
            list::test_iawwc_no_fire_if_never_polled,
            list::test_iawwc_no_fire_if_polled_after_detach,
            list::test_iawwc_fire,

            mutex::test_stack,
            mutex::test_static,
            mutex::test_lock_cancel_before_poll,
            mutex::test_lock_cancel_while_blocked,
            mutex::test_fairness,
            mutex::test_rewake_on_cancel,

            spsc::test_stack,
            spsc::test_static_storage,
            spsc::test_static_everything,
            spsc::test_nonempty_drop,

            #[cfg(feature = "handoff")]
            handoff::test_create_drop,
            #[cfg(feature = "handoff")]
            handoff::test_split_drop,
            #[cfg(feature = "handoff")]
            handoff::test_push_pop,
            #[cfg(feature = "handoff")]
            handoff::test_push_cancel,
            #[cfg(feature = "handoff")]
            handoff::test_push_cancel_after_block,
            #[cfg(feature = "handoff")]
            handoff::test_push_cancel_after_success,
            #[cfg(feature = "handoff")]
            handoff::test_pop_cancel,
            #[cfg(feature = "handoff")]
            handoff::test_pop_cancel_after_block,
            #[cfg(feature = "handoff")]
            handoff::test_pop_cancel_after_success,

            #[cfg(feature = "semaphore")]
            semaphore::test_create_drop,
            #[cfg(feature = "semaphore")]
            semaphore::test_acquire,
            #[cfg(feature = "semaphore")]
            semaphore::test_release,
            #[cfg(feature = "semaphore")]
            semaphore::test_exhaustion,
            #[cfg(feature = "semaphore")]
            semaphore::test_fairness,
            #[cfg(feature = "semaphore")]
            semaphore::test_cancellation,

            #[cfg(feature = "semaphore")]
            semaphore::test_scoped_create_drop,
            #[cfg(feature = "semaphore")]
            semaphore::test_scoped_acquire,
            #[cfg(feature = "semaphore")]
            semaphore::test_scoped_release,
            #[cfg(feature = "semaphore")]
            semaphore::test_scoped_exhaustion,

            #[cfg(feature = "rwlock")]
            rwlock::test_create_drop,
            #[cfg(feature = "rwlock")]
            rwlock::test_uncontended_try_lock_shared,
            #[cfg(feature = "rwlock")]
            rwlock::test_uncontended_try_lock_exclusive,
            #[cfg(feature = "rwlock")]
            rwlock::test_blocking,
            #[cfg(feature = "rwlock")]
            rwlock::test_fairness,
        }
    };

    // We're going to impose a timeout, just in case something fails to wake
    // properly. Yes, `sleep_for` needs to be working for the timeout to work --
    // this is best-effort in an attempt to improve user experience.

    // This timeout may seem awfully short -- the test suite tends to take
    // several seconds to run using openocd+gdb. However, this is in lilos time,
    // and lilos time halts during any semihosting operation. Think of it as the
    // "user" timing on Unix, while the time spent playing around in openocd is
    // "sys".
    const TEST_TIMEOUT: core::time::Duration = core::time::Duration::from_millis(1000);

    match time::with_timeout(TEST_TIMEOUT, tests).await {
        Some(()) => {
            hprintln!("tests complete.");
            cortex_m_semihosting::debug::exit(Ok(()));
        }
        None => {
            panic!("tests timed out.");
        }
    }

    block_forever().await
}

/// Make sure that yield CPU handles waking correctly -- otherwise the tests
/// will just halt here.
async fn test_yield_cpu() {
    exec::yield_cpu().await;
}

async fn test_other_tasks_started() {
    // Let all initially-started tasks run.
    exec::yield_cpu().await;
    // Check that the auto flag got set.
    assert!(AUTO_FLAG.load(Ordering::SeqCst), "flag_auto task not started?");
    // Check that the manual flag did _not._
    assert!(!MUST_START_FLAG.load(Ordering::SeqCst), "flag_manual started prematurely");
    // Start the manual flag task.
    start_task_by_index(2).await;
    // Manual flag should be set now.
    assert!(MUST_START_FLAG.load(Ordering::SeqCst), "flag_manual not started?");
    // Non-started manual flag should still be clear.
    assert!(!MUST_NOT_START_FLAG.load(Ordering::SeqCst), "flag_manual2 started unexpectedly");
}

async fn test_clock_advancing() {
    let t1 = time::TickTime::now();
    time::sleep_for(A_BIT).await;
    let t2 = time::TickTime::now();
    assert!(t2 > t1);
}

async fn test_sleep_until_basic() {
    let t1 = time::TickTime::now();
    let target = t1 + core::time::Duration::from_millis(10);
    time::sleep_until(target).await;
    let t2 = time::TickTime::now();
    assert!(t2 == target);
}

async fn test_sleep_until_multi() {
    futures::select_biased! {
        _ = time::sleep_for(A_BIT).fuse() => (),
        _ = time::sleep_for(A_BIT + A_BIT).fuse() => {
            panic!("longer sleep should not wake first")
        }
    }
}

/// Evaluates basic behavior of `with_deadline` when its task doesn't need
/// waking at expiration.
async fn test_with_deadline_actively_polled() {
    use lilos::{time::TickTime, exec::yield_cpu, time::with_deadline};

    let start = TickTime::now();
    let mut last_poll = start;
    let deadline = last_poll + time::Millis(10);
    with_deadline(deadline, async {
        loop {
            last_poll = TickTime::now();
            yield_cpu().await;
        }
    }).await;
    let end_time = TickTime::now();
    assert_eq!(end_time, deadline);
    assert!(last_poll < deadline);
}

/// Tests `with_deadline` in cases where the deadline is responsible for waking
/// the task to make progress.
async fn test_with_deadline_blocking() {
    use lilos::{time::TickTime, time::with_deadline};

    let start = TickTime::now();
    let mut last_poll = start;
    let deadline = last_poll + time::Millis(10);
    with_deadline(deadline, async {
        loop {
            last_poll = TickTime::now();
            time::sleep_for(time::Millis(100)).await;
        }
    }).await;
    let end_time = TickTime::now();
    assert_eq!(end_time, deadline);
    assert!(last_poll < deadline);
}

async fn test_notify() {
    start_task_by_index(4).await;
    assert!(!NOTIFY_REACHED.load(Ordering::SeqCst));
    NOTIFY.notify();
    exec::yield_cpu().await;
    exec::yield_cpu().await;
    assert!(NOTIFY_REACHED.load(Ordering::SeqCst));
}

///////////////////////////////////////////////////////////////////////////////
// Utility functions and task constructors

async fn start_task_by_index(index: usize) {
    exec::wake_task_by_index(index);
    exec::yield_cpu().await; // first pass completes all tasks already awake
    exec::yield_cpu().await // second pass lets new task run
}

async fn task_set_a_flag_then_halt(flag: &AtomicBool) -> Infallible {
    flag.store(true, Ordering::SeqCst);
    block_forever().await
}

async fn block_forever() -> Infallible {
    let notify = exec::Notify::new();
    loop {
        notify.until(|| false).await;
    }
}

#[macro_export]
macro_rules! poll_and_assert_ready {
    ($fut:expr) => { poll_and_assert_ready!($fut, concat!("future not ready: ", stringify!($fut))) };
    ($fut:expr, $msg:expr $(, $args:tt)*) => {
        if let core::task::Poll::Ready(v) = futures::poll!($fut.as_mut()) {
            v
        } else {
            panic!($msg $($args)*);
        }
    }
}

#[macro_export]
macro_rules! poll_and_assert_not_ready {
    ($fut:expr) => { poll_and_assert_not_ready!($fut, concat!("future unexpectedly ready: ", stringify!($fut))) };
    ($fut:expr, $msg:expr $(, $args:tt)*) => {
        if !futures::poll!($fut.as_mut()).is_pending() {
            panic!($msg $($args)*);
        }
    }
}

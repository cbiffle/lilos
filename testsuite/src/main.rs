//! OS test suite.
//!
//! The test suite is SoC-independent, though building it for a particular SoC
//! will require Cargo config changes, a linker script, and whatever
//! configuration's needed to program the physical chip. See the SoC-specific
//! subdirectories for examples.

#![no_std]
#![no_main]

// get the panic handler
use panic_semihosting as _;

mod list;
mod spsc;
mod mutex;
mod handoff;

use core::convert::Infallible;
use core::pin::pin;
use core::sync::atomic::{AtomicBool, Ordering};
use futures::FutureExt;

use cortex_m_semihosting::hprintln;

/// This constant assumes a 16MHz clock at reset. You probably don't need to
/// adjust it if your processor starts at a different speed; none of the tests
/// rely on this being _correct,_ they only require it to have been set.
const HZ: u32 = 16_000_000;

#[cortex_m_rt::entry]
fn main() -> ! {
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

    lilos::time::initialize_sys_tick(&mut cp.SYST, HZ);
    lilos::exec::run_tasks(
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
static NOTIFY: lilos::exec::Notify = lilos::exec::Notify::new();
static NOTIFY_REACHED: AtomicBool = AtomicBool::new(false);

const A_BIT: core::time::Duration = core::time::Duration::from_millis(2);

macro_rules! async_tests {
    ($($name:path,)*) => {
        $(
            cortex_m_semihosting::hprint!(concat!(stringify!($name), "... "));
            $name().await;
            cortex_m_semihosting::hprintln!("OK");
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
            test_notify,
            list::test_node_basics,
            list::test_list_basics,
            list::test_insert_and_wait,
            list::test_insert_and_wait_with_cleanup,
            mutex::test_stack,
            mutex::test_static,
            mutex::test_lock_cancel_before_poll,
            mutex::test_lock_cancel_while_blocked,
            mutex::test_fairness,
            mutex::test_rewake_on_cancel,
            spsc::test_stack,
            spsc::test_static_storage,
            spsc::test_static_everything,
            handoff::test_create_drop,
            handoff::test_split_drop,
            handoff::test_push_pop,
            handoff::test_push_cancel,
            handoff::test_push_cancel_after_block,
            handoff::test_push_cancel_after_success,
            handoff::test_pop_cancel,
            handoff::test_pop_cancel_after_block,
            handoff::test_pop_cancel_after_success,
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

    futures::select_biased! {
        _ = tests.fuse() => {
            hprintln!("tests complete.");
            cortex_m_semihosting::debug::exit(Ok(()));
        },
        _ = lilos::exec::sleep_for(TEST_TIMEOUT).fuse() => {
            panic!("tests timed out.");
        }
    }

    block_forever().await
}

/// Make sure that yield CPU handles waking correctly -- otherwise the tests
/// will just halt here.
async fn test_yield_cpu() {
    lilos::exec::yield_cpu().await;
}

async fn test_other_tasks_started() {
    // Let all initially-started tasks run.
    lilos::exec::yield_cpu().await;
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
    let t1 = lilos::time::TickTime::now();
    lilos::exec::sleep_for(A_BIT).await;
    let t2 = lilos::time::TickTime::now();
    assert!(t2 > t1);
}

async fn test_sleep_until_basic() {
    let t1 = lilos::time::TickTime::now();
    let target = t1 + core::time::Duration::from_millis(10);
    lilos::exec::sleep_until(target).await;
    let t2 = lilos::time::TickTime::now();
    assert!(t2 == target);
}

async fn test_sleep_until_multi() {
    futures::select_biased! {
        _ = lilos::exec::sleep_for(A_BIT).fuse() => (),
        _ = lilos::exec::sleep_for(A_BIT + A_BIT).fuse() => {
            panic!("longer sleep should not wake first")
        }
    }
}

async fn test_notify() {
    start_task_by_index(4).await;
    assert!(!NOTIFY_REACHED.load(Ordering::SeqCst));
    NOTIFY.notify();
    lilos::exec::yield_cpu().await;
    lilos::exec::yield_cpu().await;
    assert!(NOTIFY_REACHED.load(Ordering::SeqCst));
}

///////////////////////////////////////////////////////////////////////////////
// Utility functions and task constructors

async fn start_task_by_index(index: usize) {
    lilos::exec::wake_task_by_index(index);
    lilos::exec::yield_cpu().await; // first pass completes all tasks already awake
    lilos::exec::yield_cpu().await // second pass lets new task run
}

async fn task_set_a_flag_then_halt(flag: &AtomicBool) -> Infallible {
    flag.store(true, Ordering::SeqCst);
    block_forever().await
}

async fn block_forever() -> Infallible {
    let notify = lilos::exec::Notify::new();
    loop {
        notify.until(|| false).await;
    }
}

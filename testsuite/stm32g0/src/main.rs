//! OS test suite, STM32G0 wrapper.

#![no_std]
#![no_main]

// using a smaller panic handler on G0 to save space.
use panic_halt as _;

/// This constant assumes a 16MHz clock at reset. You probably don't need to
/// adjust it if your processor starts at a different speed; none of the tests
/// rely on this being _correct,_ they only require it to have been set.
const HZ: u32 = 16_000_000;

#[cortex_m_rt::entry]
fn main() -> ! {
    lilos_testsuite::run_test_suite(HZ)
}

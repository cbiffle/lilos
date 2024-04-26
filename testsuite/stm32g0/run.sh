#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")"

IMG=../../target/thumbv6m-none-eabi/release/lilos-testsuite-stm32g0

# G0 has tight enough flash that we need to build in release mode.
cargo build --release

openocd -f openocd.cfg \
    -c "init" \
    -c "reset halt" \
    -c "echo flashing..." \
    -c "flash write_image erase $IMG" \
    -c "echo verifying..." \
    -c "verify_image $IMG" \
    -c "echo running..." \
    -c "arm semihosting enable" \
    -c "reset run"

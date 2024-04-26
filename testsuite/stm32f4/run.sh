#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")"

IMG=../../target/thumbv7em-none-eabihf/debug/lilos-testsuite-stm32f4

# F4 has enough flash to build in debug mode
cargo build

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

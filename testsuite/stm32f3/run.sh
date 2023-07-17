#!/bin/bash

set -euo pipefail

cd "$(dirname "$0")"

IMG=target/thumbv7m-none-eabi/debug/lilos-testsuite-stm32f3

# F3 has enough flash to build in debug mode
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

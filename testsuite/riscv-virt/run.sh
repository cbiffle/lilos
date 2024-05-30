#!/usr/bin/env bash

set -euo pipefail

pushd "$(dirname "$0")"

./cargo.sh run --target riscv32imac-unknown-none-elf
./cargo.sh run --target riscv64gc-unknown-none-elf

echo "All tests passed."

popd >/dev/null

#!/usr/bin/env bash

set -euo pipefail

DIRS="os handoff semaphore rwlock testsuite/stm32f4 testsuite/stm32g0 testsuite/stm32f3 examples/*/*/"

for d in $DIRS; do
    echo "---- clipping in $d"
    pushd $d > /dev/null
    cargo clippy -- --deny warnings
    popd > /dev/null
done

#!/usr/bin/env bash

set -euo pipefail

DIRS="os extra/* testsuite/stm32f4 testsuite/stm32g0 testsuite/stm32f3 examples/*/*/"

for d in $DIRS; do
    echo "---- clipping in $d"
    pushd $d > /dev/null
    cargo ${TOOLCHAIN:=} clippy -- --deny warnings
    popd > /dev/null
done

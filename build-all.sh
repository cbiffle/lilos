#!/bin/bash

set -euo pipefail

DIRS="os testsuite/stm32f4 testsuite/stm32g0 examples/*/*"

for d in $DIRS; do
    echo "---- building in $d"
    pushd $d > /dev/null
    cargo build
    popd > /dev/null
done

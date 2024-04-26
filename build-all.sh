#!/usr/bin/env bash

set -euo pipefail

MODES=(
	""
	"--features mutex"
	"--features spsc"
	"--features systick"
	"--features mutex,spsc"
	"--features mutex,systick"
	"--features spsc,systick"
	"--features mutex,spsc,systick"
	)

for k in ${!MODES[@]}; do
    echo "---- building OS with: ${MODES[$k]}"
    pushd os > /dev/null
    cargo build --no-default-features ${MODES[$k]}
    popd > /dev/null
done

DIRS="handoff semaphore rwlock testsuite/stm32f4 testsuite/stm32g0 testsuite/stm32f3 testsuite/lm3s6965 examples/*/*/"

for d in $DIRS; do
    if [[ $d == *memory.x ]]; then
	continue
    fi
    echo "---- building in $d"
    pushd $d > /dev/null
    cargo build
    popd > /dev/null
done

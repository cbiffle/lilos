#!/usr/bin/env bash

set -euo pipefail

jq --version

DIRS="os handoff semaphore testsuite/stm32f4 testsuite/stm32g0 testsuite/stm32f3 examples/*/*/"

for d in $DIRS; do
    pushd $d > /dev/null
    VERSION=$(cargo metadata --format-version 1 \
        | jq -r '.resolve.root as $root | .packages[] | select(.id == $root) | .rust_version')
    TARGET=$(cargo metadata --format-version 1 \
        | jq -r '.resolve.root as $root | .packages[] | select(.id == $root) | .metadata.docs.rs["default-target"]')
    echo "---- building in $d using ${VERSION} for ${TARGET}"
    rustup update ${VERSION}
    rustup target add --toolchain ${VERSION} ${TARGET}
    rustup run ${VERSION} cargo check
    popd > /dev/null
done

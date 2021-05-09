#!/bin/bash

set -euo pipefail

DIRS="os testsuite examples/*/*"

for d in $DIRS; do
    echo "---- building in $d"
    pushd $d > /dev/null
    cargo build
    popd > /dev/null
done

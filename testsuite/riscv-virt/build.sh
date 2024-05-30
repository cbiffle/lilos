#!/usr/bin/env bash

set -euo pipefail

pushd "$(dirname "$0")"

./cargo.sh build

popd

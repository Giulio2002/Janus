#!/usr/bin/env bash
# Build the example Go programs for linux/arm64 into artifacts/.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mkdir -p "$root/artifacts"
cd "$root/examples/basic"
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-arm64" ./cmd
echo "built $root/artifacts/examples-arm64"

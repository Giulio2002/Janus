#!/usr/bin/env bash
# Build the example Go programs for linux/arm64 into artifacts/.
set -euo pipefail
# Example binaries (and so every address a proof depends on) are built with exactly this Go
# release, whatever Go is installed; the go command downloads it on first use.
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
mkdir -p "$root/artifacts"
cd "$root/examples/basic"
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-arm64" ./cmd
echo "built $root/artifacts/examples-arm64"

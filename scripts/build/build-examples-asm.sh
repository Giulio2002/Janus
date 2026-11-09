#!/usr/bin/env bash
# Build the Go assembly examples (examples/asm: ABI0 assembly functions, the Go code calling
# them and the ABI wrappers; docs/ABI0.md) for linux/arm64 and linux/amd64 (GOAMD64=v1) into
# artifacts/examples-asm-arm64 and artifacts/examples-asm-amd64.
set -euo pipefail
# Every address a proof depends on comes from these binaries, so Go is pinned (the go command
# downloads the release on first use).
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
mkdir -p "$root/artifacts"
cd "$root/examples/asm"
export CGO_ENABLED=0
GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-asm-arm64" ./cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-asm-amd64" ./cmd
echo "built $root/artifacts/examples-asm-arm64 $root/artifacts/examples-asm-amd64"

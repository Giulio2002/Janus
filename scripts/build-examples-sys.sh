#!/usr/bin/env bash
# Build the kernel examples (examples/sys: Go functions that make system calls, read the clocks
# or trap; WP-C, Janus/Contracts/Syscall*.lean) for linux/arm64 and linux/amd64 (GOAMD64=v1)
# into artifacts/examples-sys-arm64 and artifacts/examples-sys-amd64. They are a binary of their
# own so that the syscall, time and runtime code they pull in leaves the addresses of
# examples/basic unchanged. Every address a proof depends on comes from these binaries, so the
# Go release is pinned (GOTOOLCHAIN, downloaded on first use).
set -euo pipefail
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
export PATH="$PATH:/usr/local/go/bin"
mkdir -p "$root/artifacts"
cd "$root/examples/sys"
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-sys-arm64" ./cmd
CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-sys-amd64" ./cmd
echo "built $root/artifacts/examples-sys-arm64 $root/artifacts/examples-sys-amd64"

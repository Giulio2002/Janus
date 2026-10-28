#!/usr/bin/env bash
# Build the print/println examples (examples/print; R8, Janus/Contracts/Print*.lean) for
# linux/arm64 and linux/amd64 (GOAMD64=v1) into artifacts/examples-print-arm64 and
# artifacts/examples-print-amd64. A binary of their own, so that the print path they pull in leaves
# the addresses of the other examples unchanged. Every address a proof depends on comes from these
# binaries, so the Go release is pinned (GOTOOLCHAIN, downloaded on first use).
set -euo pipefail
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
export PATH="$PATH:/usr/local/go/bin"
mkdir -p "$root/artifacts"
cd "$root/examples/print"
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-print-arm64" ./cmd
CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-print-amd64" ./cmd
echo "built $root/artifacts/examples-print-arm64 $root/artifacts/examples-print-amd64"

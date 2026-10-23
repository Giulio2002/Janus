#!/usr/bin/env bash
# Build the uint256 verification target for linux/arm64 with the pinned toolchain.
# Output: targets/uint256/bin/uint256-arm64 (statically linked Go ELF).
set -euo pipefail
cd "$(dirname "$0")"
GO=${GO:-/usr/local/go/bin/go}
mkdir -p bin
# -trimpath: no host paths in the binary, so the build is reproducible across machines.
# -buildvcs=false: do not stamp the enclosing git state (keeps the SHA-256 stable).
# CGO_ENABLED=0: pure Go, static, no libc.
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 "$GO" build -trimpath -buildvcs=false -o bin/uint256-arm64 .
"$GO" version -m bin/uint256-arm64 | head -n 12
sha256sum bin/uint256-arm64

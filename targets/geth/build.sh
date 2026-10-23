#!/usr/bin/env bash
# Build the go-ethereum core/vm verification target for linux/arm64 with the pinned toolchain.
# Output: targets/geth/bin/geth-vm-arm64 (statically linked Go ELF).
set -euo pipefail
cd "$(dirname "$0")"
GO=${GO:-/usr/local/go/bin/go}
mkdir -p bin
# -trimpath: no host paths in the binary, so the build is reproducible across machines.
# -buildvcs=false: do not stamp the enclosing git state (keeps the SHA-256 stable).
# CGO_ENABLED=0: pure Go, static, no libc. GOARM64=v8.0: baseline ISA (the Go default, explicit).
CGO_ENABLED=0 GOOS=linux GOARCH=arm64 GOARM64=v8.0 "$GO" build -trimpath -buildvcs=false -o bin/geth-vm-arm64 .
"$GO" version -m bin/geth-vm-arm64 | grep -E 'go1|path|mod|dep.*(go-ethereum|uint256)|GOARCH|GOOS|GOARM64|CGO'
sha256sum bin/geth-vm-arm64

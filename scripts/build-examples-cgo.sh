#!/usr/bin/env bash
# Build the cgo examples (examples/cgo: Go functions calling C through cgo) for linux/arm64 and
# linux/amd64 into artifacts/examples-cgo-arm64 and artifacts/examples-cgo-amd64.
#
# Every address a proof depends on comes from these binaries, so the compilers are pinned:
# Go (GOTOOLCHAIN, downloaded on first use) and the C compilers cgo invokes for the C files and
# the external link. The script refuses to build with any other C compiler version unless
# JANUS_CC_ANY=1 (then the proofs may need adjusting: they name addresses only through the
# extraction, but a different compiler emits different code).
#
#   amd64: gcc                     (Ubuntu 15.2.0-16ubuntu1) 15.2.0, native
#   arm64: aarch64-linux-gnu-gcc   (Ubuntu 15.2.0-16ubuntu1) 15.2.0  (apt: gcc-aarch64-linux-gnu)
#   amd64, CC=clang: clang         Ubuntu clang version 21.1.8 (6ubuntu1)  (examples/cgo/cmdclang,
#                                  the clang-vectorised C of examples/cgo/vec ->
#                                  artifacts/examples-cgo-clang-amd64)
#
# CGO_CFLAGS is pinned to cgo's default (-g -O2). The binaries are non-PIE ET_EXEC executables
# (go build -buildmode=exe with external linking passes -no-pie), as janus extract requires.
set -euo pipefail
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
cc_amd64="${CC_AMD64:-gcc}"
cc_arm64="${CC_ARM64:-aarch64-linux-gnu-gcc}"
cc_clang="${CC_CLANG:-clang}"
want="(Ubuntu 15.2.0-16ubuntu1) 15.2.0"
for cc in "$cc_amd64" "$cc_arm64"; do
  v="$("$cc" --version | head -1)"
  if [[ "$v" != *"$want"* && "${JANUS_CC_ANY:-0}" != 1 ]]; then
    echo "build-examples-cgo: $cc is '$v', the examples are pinned to '$want' (set JANUS_CC_ANY=1 to override)" >&2
    exit 1
  fi
done
v="$("$cc_clang" --version | head -1)"
if [[ "$v" != *"clang version 21.1.8 (6ubuntu1)"* && "${JANUS_CC_ANY:-0}" != 1 ]]; then
  echo "build-examples-cgo: $cc_clang is '$v', the clang example is pinned to 'Ubuntu clang version 21.1.8 (6ubuntu1)' (set JANUS_CC_ANY=1 to override)" >&2
  exit 1
fi
mkdir -p "$root/artifacts"
cd "$root/examples/cgo"
export CGO_ENABLED=1 CGO_CFLAGS="-g -O2"
GOOS=linux GOARCH=arm64 CC="$cc_arm64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cgo-arm64" ./cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 CC="$cc_amd64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cgo-amd64" ./cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 CC="$cc_clang" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cgo-clang-amd64" ./cmdclang
echo "built $root/artifacts/examples-cgo-arm64 $root/artifacts/examples-cgo-amd64 $root/artifacts/examples-cgo-clang-amd64"

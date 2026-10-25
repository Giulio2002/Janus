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
#
# CGO_CFLAGS is pinned to cgo's default (-g -O2). The binaries are non-PIE ET_EXEC executables
# (go build -buildmode=exe with external linking passes -no-pie), as janus extract requires.
set -euo pipefail
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
cc_amd64="${CC_AMD64:-gcc}"
cc_arm64="${CC_ARM64:-aarch64-linux-gnu-gcc}"
want="(Ubuntu 15.2.0-16ubuntu1) 15.2.0"
for cc in "$cc_amd64" "$cc_arm64"; do
  v="$("$cc" --version | head -1)"
  if [[ "$v" != *"$want"* && "${JANUS_CC_ANY:-0}" != 1 ]]; then
    echo "build-examples-cgo: $cc is '$v', the examples are pinned to '$want' (set JANUS_CC_ANY=1 to override)" >&2
    exit 1
  fi
done
mkdir -p "$root/artifacts"
cd "$root/examples/cgo"
export CGO_ENABLED=1 CGO_CFLAGS="-g -O2"
GOOS=linux GOARCH=arm64 CC="$cc_arm64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cgo-arm64" ./cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 CC="$cc_amd64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cgo-amd64" ./cmd
# The C environment examples (examples/cgo/cenv, docs/FFI.md sections 2-4) are their own binary.
# On amd64 the linker relaxes every GOT load of a symbol the executable defines (`mov
# sym@GOTPCREL(%rip)` becomes `lea`/`mov $imm`), so a second amd64 build links with
# -Wl,--no-relax to keep the -fPIC GOT loads (used by the GOT example only: --no-relax also
# changes the Go runtime's own TLS code, which the stub pins do not cover).
GOOS=linux GOARCH=arm64 CC="$cc_arm64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cenv-arm64" ./cmd/cenv
GOOS=linux GOARCH=amd64 GOAMD64=v1 CC="$cc_amd64" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cenv-amd64" ./cmd/cenv
GOOS=linux GOARCH=amd64 GOAMD64=v1 CC="$cc_amd64" CGO_LDFLAGS="-g -O2 -Wl,--no-relax" go build -buildmode=exe -trimpath -buildvcs=false -o "$root/artifacts/examples-cenv-norelax-amd64" ./cmd/cenv
echo "built $root/artifacts/examples-cgo-{arm64,amd64} $root/artifacts/examples-cenv-{arm64,amd64,norelax-amd64}"

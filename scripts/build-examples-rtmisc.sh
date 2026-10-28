#!/usr/bin/env bash
# Build the remaining-runtime examples (examples/rtmisc; docs/RUNTIME-CONTRACTS.md, "Remaining
# runtime") for linux/arm64 and linux/amd64 (GOAMD64=v1):
#   artifacts/examples-rtmisc-{arm64,amd64}     ./cmd: rtmisc, plus the instrumented packages
#       cover (-cover -covermode=count), soft (-d=softfloat) and checkptr (-d=checkptr), each
#       flag applied to its package only;
#   artifacts/examples-rtmisc-sc-{arm64,amd64}  ./sc/cmd with GOEXPERIMENT=sizespecializedmalloc;
#   artifacts/examples-rtmisc-live-{arm64,amd64}  ./live/cmd: the live allocation examples
#       (Janus/Contracts/Live.lean).
#   artifacts/examples-rtmisc-softf-{arm64,amd64}  ./softcmd: the soft-float (-d=softfloat) and
#       runtime.KeepAlive examples of Janus.Contracts.SoftFloat, in a binary of their own.
# Separate binaries, so that no other example's addresses change.
set -euo pipefail
# Every address a proof depends on comes from these binaries, so Go is pinned (the go command
# downloads the release on first use).
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$PATH:/usr/local/go/bin"
mkdir -p "$root/artifacts"
cd "$root/examples/rtmisc"
export CGO_ENABLED=0
flags=(-trimpath -buildvcs=false -cover -covermode=count -coverpkg=example.com/rtmisc/cover
       -gcflags=example.com/rtmisc/soft=-d=softfloat -gcflags=example.com/rtmisc/checkptr=-d=checkptr)
GOOS=linux GOARCH=arm64 go build "${flags[@]}" -o "$root/artifacts/examples-rtmisc-arm64" ./cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 go build "${flags[@]}" -o "$root/artifacts/examples-rtmisc-amd64" ./cmd
GOEXPERIMENT=sizespecializedmalloc GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false \
  -o "$root/artifacts/examples-rtmisc-sc-arm64" ./sc/cmd
GOEXPERIMENT=sizespecializedmalloc GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false \
  -o "$root/artifacts/examples-rtmisc-sc-amd64" ./sc/cmd
GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-rtmisc-live-arm64" ./live/cmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-rtmisc-live-amd64" ./live/cmd
GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -gcflags=example.com/rtmisc/softf=-d=softfloat \
  -o "$root/artifacts/examples-rtmisc-softf-arm64" ./softcmd
GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -gcflags=example.com/rtmisc/softf=-d=softfloat \
  -o "$root/artifacts/examples-rtmisc-softf-amd64" ./softcmd
echo "built $root/artifacts/examples-rtmisc-{arm64,amd64} $root/artifacts/examples-rtmisc-sc-{arm64,amd64} $root/artifacts/examples-rtmisc-live-{arm64,amd64} $root/artifacts/examples-rtmisc-softf-{arm64,amd64}"

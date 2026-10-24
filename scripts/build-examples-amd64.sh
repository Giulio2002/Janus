#!/usr/bin/env bash
# Build the example Go programs for linux/amd64 into artifacts/examples-amd64 and extract
# every examples/basic function into artifacts/amd64/<Name>/ with janus extract.
# -buildvcs=false keeps the binary (and so the addresses the proofs mention) independent of
# the git state of the checkout.
set -euo pipefail
# Example binaries (and so every address a proof depends on) are built with exactly this Go
# release, whatever Go is installed; the go command downloads it on first use.
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
export PATH="$PATH:/usr/local/go/bin"
mkdir -p "$root/artifacts" "$root/bin"
(cd "$root/examples/basic" &&
  CGO_ENABLED=0 GOOS=linux GOARCH=amd64 GOAMD64=v1 go build -trimpath -buildvcs=false -o "$root/artifacts/examples-amd64" ./cmd)
echo "built $root/artifacts/examples-amd64"
(cd "$root" && go build -o "$root/bin/janus" ./cmd/janus)
funcs=$(cat "$root"/examples/basic/*.go | grep -oE '^func [A-Z][A-Za-z0-9]*' | awk '{print $2}')
for f in $funcs; do
  "$root/bin/janus" extract "$root/artifacts/examples-amd64" "example.com/basic.$f" "$root/artifacts/amd64/$f"
done

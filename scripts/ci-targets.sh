#!/usr/bin/env bash
# CI: build the verification targets and check that the builds reproduce the recorded SHA-256
# (targets/geth/geth-vm-arm64.sha256; the uint256 hash recorded in docs/TARGETS.md).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export GO="${GO:-$(command -v go || echo /usr/local/go/bin/go)}"
fail=0

"$root/targets/uint256/build.sh" > /dev/null
want="$(grep -oE '`bin/uint256-arm64` SHA-256 `[0-9a-f]{64}`' "$root/docs/TARGETS.md" | grep -oE '[0-9a-f]{64}' | head -1 || true)"
got="$(sha256sum "$root/targets/uint256/bin/uint256-arm64" | cut -d' ' -f1)"
if [ -z "$want" ]; then
  echo "uint256: built $got (no recorded hash found in docs/TARGETS.md)"
elif [ "$want" = "$got" ]; then
  echo "uint256: reproducible, SHA-256 $got"
else
  echo "uint256: SHA-256 $got, docs/TARGETS.md records $want" >&2; fail=1
fi

"$root/targets/geth/build.sh" > /dev/null
if (cd "$root/targets/geth" && sha256sum -c --quiet geth-vm-arm64.sha256); then
  echo "geth: reproducible, SHA-256 $(cut -d' ' -f1 "$root/targets/geth/geth-vm-arm64.sha256")"
else
  echo "geth: build does not match targets/geth/geth-vm-arm64.sha256" >&2; fail=1
fi
exit "$fail"

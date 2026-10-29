#!/usr/bin/env bash
# The "WrongAdd" demonstration: change `+` to `-` in the Go source of Add, rebuild, re-extract,
# and check that the *same* proof (examples/proofs/Add.lean) is rejected. Then verify
# examples/proofs/WrongAdd.lean, which proves that the subtracting binary violates the Add spec.
#
# The edit happens in a temporary copy of examples/basic, so the repository is never modified.
# Outputs: artifacts/wrongadd-arm64 (the broken binary) and artifacts/WrongAdd/ (its extraction
# and the counterexample's verified.json). Exit status 0 iff the Add proof is rejected and the
# counterexample is verified.
set -euo pipefail
# Example binaries (and so every address a proof depends on) are built with exactly this Go
# release, whatever Go is installed; the go command downloads it on first use.
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
janus="$root/bin/janus"
[ -x "$janus" ] || CGO_ENABLED=0 go build -o "$janus" ./cmd/janus
extra=()
[ -n "${JANUS_ROOT:-}" ] && extra=(--janus-root "$JANUS_ROOT")

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp -r examples/basic "$tmp/basic"
src="$tmp/basic/basic.go"
grep -q 'func Add(x, y uint64) uint64 { return x + y }' "$src" || {
  echo "break-demo: cannot find the Add function to edit in examples/basic/basic.go" >&2; exit 1; }
sed -i 's/func Add(x, y uint64) uint64 { return x + y }/func Add(x, y uint64) uint64 { return x - y }/' "$src"
echo "== edited Add in a copy of examples/basic:"
grep -n 'func Add(' "$src"

(cd "$tmp/basic" && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath \
  -o "$root/artifacts/wrongadd-arm64" ./cmd)
"$janus" extract artifacts/wrongadd-arm64 example.com/basic.Add artifacts/WrongAdd

echo "== verifying the unchanged Add proof against the subtracting binary (must be rejected):"
if "$janus" verify artifacts/WrongAdd --proof examples/proofs/Add.lean "${extra[@]}" \
    > "$tmp/add.log" 2>&1; then
  cat "$tmp/add.log"
  echo "break-demo: FAILED: the Add proof was accepted for x - y" >&2
  exit 1
fi
grep -E '^(Invalid|  Stage|  Lean errors|.*error)' "$tmp/add.log" | head -8
echo "   -> rejected, as it must be."

echo "== verifying the counterexample examples/proofs/WrongAdd.lean on the subtracting binary:"
"$janus" verify artifacts/WrongAdd --proof examples/proofs/WrongAdd.lean "${extra[@]}" \
  | grep -E '^(Verified|  Axioms|  Kernel)'
echo "break-demo: ok"

#!/usr/bin/env bash
# Round 5, item 6 (docs/AUDIT-ROUND5.md): targeted oracle cases for six instruction families
# (arm64 ADD/SUB extended register, Advanced SIMD shift by immediate, across lanes; amd64
# BT/BTS/BTR/BTC, SHLD/SHRD, BSF/BSR/TZCNT/LZCNT/POPCNT), model vs hardware (qemu-aarch64,
# the host CPU), plus the hand-derived kernel checks in HandDerived.lean.
# Writes only under audit/round5/model/{bin,cases,out-a64,out-x64}. Exits 1 on any MISMATCH,
# on a failing hand-derived check, or if a family that must agree stopped agreeing.
# Usage: audit/round5/model/run-model.sh   (about a minute on 48 cores)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
here="$root/audit/round5/model"
export PATH="$PATH:/usr/local/go/bin"
B="$here/bin"; mkdir -p "$B/a64" "$B/x64"
QEMU="${QEMU-/usr/bin/qemu-aarch64}"
(cd "$root/oracle" && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -o "$B/a64/runner" ./cmd/runner &&
  go build -o "$B/a64/oracle" ./cmd/oracle)
(cd "$root/oracle-amd64" && CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -buildmode=pie -o "$B/x64/runner" ./cmd/runner &&
  CGO_ENABLED=0 go build -o "$B/x64/oracle" ./cmd/oracle)
(cd "$root" && lake build janus-oracle janus-oracle-amd64 >/dev/null)
fail=0

echo "== hand-derived kernel checks (HandDerived.lean)"
if (cd "$root" && lake env lean "$here/HandDerived.lean"); then echo "  ok"; else echo "  >>> FAILED"; fail=1; fi

DCZID="$(GODEBUG=asyncpreemptoff=1 ${QEMU:+"$QEMU"} "$B/a64/runner" -dczid)"
python3 -I "$here/gen.py" "$here/cases" "$DCZID"

echo "== arm64: model vs ${QEMU:-native}"
GODEBUG=asyncpreemptoff=1 "$B/a64/oracle" run -qemu "$QEMU" -runner "$B/a64/runner" \
  -model "$root/.lake/build/bin/janus-oracle" -j "$(nproc)" -cases "$here/cases/a64.jsonl" -out "$here/out-a64" >/dev/null 2>&1
sed -n '5p' "$here/out-a64/summary.md"
grep -E '^\| (r5/|\*\*total)' "$here/out-a64/summary.md"

echo "== amd64: model vs the host CPU"
"$B/x64/oracle" run -runner "$B/x64/runner" -model "$root/.lake/build/bin/janus-oracle-amd64" \
  -j 16 -cases "$here/cases/x64.jsonl" -out "$here/out-x64" >/dev/null 2>&1
sed -n '5p' "$here/out-x64/summary.md"
grep -E '^\| (r5/|\*\*total)' "$here/out-x64/summary.md"

for d in out-a64 out-x64; do
  if grep -q '"verdict":"MISMATCH"' "$here/$d/verdicts.jsonl"; then
    echo ">>> MISMATCH in $d (see $here/$d/summary.md)"; fail=1
  fi
done
# The modelled forms must keep agreeing (a decoder regression that turned them into gaps
# would also pass the MISMATCH check): these classes have no model gaps today.
for cls in r5/a64.addsubext r5/x64.bt.reg r5/x64.bt.reg-imm r5/x64.bt.mem-imm; do
  if grep -q "\"class\":\"$cls\",[^}]*\"verdict\":\"model-gap\"" "$here"/out-*/verdicts.jsonl; then
    echo ">>> $cls has model gaps (expected none)"; fail=1
  fi
done
[ $fail -eq 0 ] && echo "All round-5 model rows as expected." || { echo "BROKEN"; exit 1; }

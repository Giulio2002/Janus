#!/usr/bin/env bash
# Round-6 regression rows (docs/audit/AUDIT-ROUND6.md). Exits 1 if a blocked attack prints Verified, a
# control stops verifying or prints something else, or the stub fixture is misclassified.
# Writes only under test/redteam/rounds/round6/work/ and test/redteam/rounds/round6/bin/.
# Usage: test/redteam/rounds/round6/run-round6.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
# shellcheck source=../../../../scripts/gate/lib/memguard.sh
. "$root/scripts/gate/lib/memguard.sh"
memguard_self "$@"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="$root/test/redteam/rounds/round6/bin/janus"; mkdir -p "$(dirname "$J")"
# test/redteam/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || memguard_lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build/build-examples.sh >/dev/null
W=test/redteam/rounds/round6/work; rm -rf "$W"; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
"$J" extract artifacts/examples-arm64 example.com/basic.Div $W/Div >/dev/null || exit 1
broken=()
A=test/redteam/rounds/round6/attacks

# row NAME EXPECT [PATTERN]: verdict of $out. EXPECT "blocked" (must not print Verified; if PATTERN
# is given the rejection must contain it) or "Verified" (must print Verified and contain PATTERN).
. "$root/test/redteam/lib/blocked.sh"
row() {
  local name=$1 expect=$2 pat=${3:-} verdict status=""
  verdict="$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-150)"
  [ -n "$verdict" ] || verdict="(no verdict) $(head -1 <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in Verified*) status=BROKEN ;; *) [ -n "$pat" ] && ! grep -qF -- "$pat" <<<"$out" && status=BROKEN ;; esac ;;
    Verified) case $verdict in Verified*) [ -n "$pat" ] && ! grep -qF -- "$pat" <<<"$out" && status=BROKEN ;; *) status=BROKEN ;; esac ;;
  esac
  # blocked rows: pinned reason, and no Lean elaboration failure (test/redteam/lib/blocked.sh)
  if [ "$expect" = blocked ]; then why="$(blocked_check rounds/round6/run-round6.sh "$name" "$out")"; [ -n "$why" ] && { status=BROKEN; verdict="$verdict [$why]"; }; fi
  printf '  %-36s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
v() { out="$("$J" verify --full-errors --janus-root "$root" --proof "$A/$1.lean" "${2:-$W/Add}" 2>&1)"; }
# UP3d: honest rows verify together with their Witness.nonvacuous
vw() { out="$("$J" verify --janus-root "$root" --proof "$A/$1.lean" "${2:-$W/Add}" --theorem Proof.correctness --theorem Proof.Witness.nonvacuous 2>&1)"; }

echo "== F1: names with lookalike letters or «…» components imitating trusted constants"
v F1a_homoglyph_extracted_program; row F1a_homoglyph_extracted_program blocked "shadows the Extracted namespace"
v F1b_guillemet_extracted;         row F1b_guillemet_extracted         blocked "shadows the Extracted namespace"
v F1c_homoglyph_ensures;           row F1c_homoglyph_ensures           blocked "lookalike letters"
out="$("$J" verify --janus-root "$root" --proof test/redteam/rounds/round5/attacks/E3d_field_named_def.lean $W/Add --theorem Proof.correctness --theorem Proof.Witness.nonvacuous 2>&1)"
row E3d_ascii_def_in_janus_namespace Verified 'Janus.Arm64.State.result : Janus.Arm64.State → BitVec 64 := fun s => s.regs 0'

echo "== F2: out-of-range numerals at wrapping types (statement and disclosed defs)"
v F2a_wrapped_numeral_hyp $W/Div; row F2a_wrapped_numeral_hyp blocked "out-of-range numeral"
v F2b_wrapped_numeral_def;        row F2b_wrapped_numeral_def blocked "out-of-range numeral"
vw F2c_numeral_in_range;          row F2c_numeral_in_range Verified '(18446744073709551615 : BitVec (64 : Nat)) ≠ (0 : BitVec (64 : Nat))'

echo "== F3: stub classification by package (test/redteam/rounds/round6/stubmod: module runtime.panicky)"
( cd test/redteam/rounds/round6/stubmod && GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}" CGO_ENABLED=0 GOOS=linux GOARCH=arm64 \
    go build -trimpath -buildvcs=false -o "$root/$W/stubmod" ./cmd ) || { echo "  stubmod build failed"; broken+=(F3-build); }
xo="$("$J" extract $W/stubmod main.Add $W/StubAdd 2>&1)"
if grep -qE 'code .* runtime\.panicky/lib\.Zero' <<<"$xo" && ! grep -qE 'stub .* runtime\.panicky' <<<"$xo"; then
  echo "  F3 extraction                        ok       runtime.panicky/lib.Zero is code, not a panic stub"
else echo "  F3 extraction: misclassified   <-- BROKEN"; echo "$xo" | sed 's/^/    /'; broken+=(F3-extract); fi
v F3a_stub_by_module_path $W/StubAdd; row F3a_stub_by_module_path blocked
vw F3b_stubmod_returns $W/StubAdd;    row F3b_stubmod_returns Verified 'ABIReturn s s'"'"' ∧ s'"'"'.regs 0 = x + y'
if command -v qemu-aarch64 >/dev/null; then
  q="$(qemu-aarch64 $W/stubmod 2>&1)"
  [ "$q" = 3 ] && echo "  F3 hardware (qemu-aarch64)           ok       Add(1, 2) returned 3" ||
    { echo "  F3 hardware: got '$q'   <-- BROKEN"; broken+=(F3-qemu); }
fi

echo "== unit rows (go test)"
(cd cmd/janus && . "$root/test/redteam/lib/gotest-row.sh" && gotest_row round6-stubkind memguard_run -n go-test -- go test -timeout 60m -run 'TestStubKind|TestRound6StatementNames' .) ||
  { echo "  >>> TestStubKind/TestRound6StatementNames failed"; broken+=(gotest); }

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-6 rows as expected."

#!/usr/bin/env bash
# Round-7 regression rows (docs/AUDIT-ROUND7.md). Exits 1 if a blocked attack prints Verified, a
# control stops verifying or prints something else, or a stub fixture is misclassified.
# Every attack verification passes --fresh (no result or replay cache: the cold path); the cache
# itself is attacked by audit/round7/run-cache.sh, which this script runs last.
# Writes only under audit/round7/work/ and audit/round7/bin/ (run-cache.sh: a temporary cache).
# Usage: audit/round7/run-round7.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="$root/audit/round7/bin/janus"; mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round7/work; rm -rf "$W"; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
broken=()
A=audit/round7/attacks

# row NAME EXPECT [PATTERN...]: verdict of $out. EXPECT "blocked" (must not print Verified; if a
# PATTERN is given the output must contain it) or "Verified" (must print Verified and contain
# every PATTERN).
row() {
  local name=$1 expect=$2 verdict status="" pat
  shift 2
  verdict="$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-150)"
  [ -n "$verdict" ] || verdict="(no verdict) $(head -1 <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in Verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  printf '  %-36s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$A/$1.lean" "${2:-$W/Add}" 2>&1)"; }
gob() { ( cd audit/round7/asmstub && GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}" CGO_ENABLED=0 GOOS=linux GOARCH=arm64 \
    go build -trimpath -buildvcs=false "$@" ) ; }

echo "== G1: runtime stubs by exact go1.26 name (audit/round7/asmstub: assembly in package lib)"
gob -o "$root/$W/asmstub" ./cmd || { echo "  asmstub build failed"; broken+=(G1-build); }
xa="$("$J" extract $W/asmstub main.Add $W/AsmAdd 2>&1)"; xi="$("$J" extract $W/asmstub main.Inc $W/AsmInc 2>&1)"
if grep -qE 'code .* runtime\.panicJanusR7$' <<<"$xa" && grep -qE 'code .* runtime\.morestackJanusR7$' <<<"$xi" &&
   grep -qE 'stub .* panic +runtime\.gopanic$' <<<"$xi" && ! grep -qE 'stub .*JanusR7' <<<"$xa$xi"; then
  echo "  G1 extraction                        ok       runtime.*JanusR7 are code; Inc reaches runtime.gopanic"
else echo "  G1 extraction: misclassified   <-- BROKEN"; echo "$xa"$'\n'"$xi" | sed 's/^/    /'; broken+=(G1-extract); fi
v G1a_asm_runtime_stub_panics $W/AsmAdd;      row G1a_asm_runtime_stub_panics blocked
v G1b_asm_runtime_stub_neverpanics $W/AsmInc; row G1b_asm_runtime_stub_neverpanics blocked
v G1c_asmstub_returns $W/AsmAdd;              row G1c_asmstub_returns Verified 'ABIReturn s s'"'"' ∧ s'"'"'.regs 0 = x + y'
if command -v qemu-aarch64 >/dev/null; then
  q="$(qemu-aarch64 $W/asmstub 2>&1)"
  if [ "$(head -1 <<<"$q")" = "3 42" ] && grep -q '^panic: boom' <<<"$q"; then
    echo "  G1 hardware (qemu-aarch64)           ok       Add(1, 2) = 3, Label() = 42, Inc panics"
  else echo "  G1 hardware: got '$(head -2 <<<"$q")'   <-- BROKEN"; broken+=(G1-qemu); fi
fi
gob -tags janusdup -o "$root/$W/asmdup" ./cmd || broken+=(G1d-build)
out="$("$J" extract $W/asmdup main.Add $W/DupAdd 2>&1)"; row G1d_linkname_duplicate_stub_name blocked "defines 2 functions with that name"
gob -ldflags=-s -o "$root/$W/asmstrip" ./cmd || broken+=(G1e-build)
out="$("$J" extract $W/asmstrip main.Add $W/StripAdd 2>&1)"; row G1e_stripped_binary_stub blocked "has no ELF symbol table"

echo "== G2: the entry symbol is the binary's label (//go:linkname push to example.com/basic.Add)"
"$J" extract $W/asmstub example.com/basic.Add $W/Label >/dev/null || broken+=(G2-extract)
v G2a_pushed_entry_label $W/Label; row G2a_pushed_entry_label Verified "Entry: example.com/basic.Add" "Module: example.com/asmstub"

echo "== H1: bound-variable names"
v H1a_binder_lookalike_vacuous;   row H1a_binder_lookalike_vacuous blocked "binds two variables whose names look alike"
v H1c_binder_cyrillic_guillemets; row H1c_binder_cyrillic_guillemets blocked "characters other than identifier letters"
v H1d_binder_zero_width;          row H1d_binder_zero_width blocked "characters other than identifier letters"
v H1b_binder_greek_honest;        row H1b_binder_greek_honest Verified "(α β : BitVec 64)"

echo "== K1: notes on standard operations that read unexpectedly"
v K1a_misleading_ops; row K1a_misleading_ops Verified "Notes (standard Lean meaning" "\`^\` wraps at" "division by zero is total at Nat" "Nat subtraction truncates at 0"
out="$("$J" verify --fresh --janus-root "$root" --proof examples/proofs/Add.lean $W/Add 2>&1)"; row K1b_honest_add_no_notes Verified
grep -q "Notes (" <<<"$out" && { echo "  K1b: the honest Add proof got notes   <-- BROKEN"; broken+=(K1b-notes); }
out="$("$J" explain $W/Add/verified.json 2>&1)"
row_e() { grep -q "Read with care" <<<"$out" && echo "  K1b explain: unexpected notes   <-- BROKEN" && broken+=(K1b-explain); }; row_e
"$J" verify --fresh --janus-root "$root" --proof $A/K1a_misleading_ops.lean $W/Add >/dev/null 2>&1
out="$("$J" explain $W/Add/verified.json 2>&1)"
if grep -q "Read with care" <<<"$out"; then echo "  K1a explain                          ok       notes shown"; else echo "  K1a explain: no notes   <-- BROKEN"; broken+=(K1a-explain); fi

echo "== J1: dependency definitions are disclosed with their bodies"
dep="$(audit/round7/dep/setup.sh "$root/$W/dep" "$root")" || { echo "  dependency fixture failed"; broken+=(dep-setup); }
out="$("$J" verify --fresh $W/Add --janus-root "$root" --proof "$dep/R7Proofs/Proofs.lean" --proof-root "$dep" --theorem R7Proofs.misnamed 2>&1)"
row J1a_misnamed_dependency_def Verified "Dependency definitions used by the statement" "MisLib.mul : BitVec (64 : Nat) → BitVec (64 : Nat) → BitVec (64 : Nat) := fun (a b : BitVec (64 : Nat)) => a + b"

echo "== unit rows (go test)"
(cd cmd/janus && go test -timeout 30m -run 'TestStubKind|TestClassifyStub|TestTermSafe' . >/dev/null 2>&1) ||
  { echo "  >>> TestStubKind/TestClassifyStub/TestTermSafe failed"; broken+=(gotest); }

echo "== result cache (audit/round7/run-cache.sh)"
audit/round7/run-cache.sh | sed 's/^/  /'
[ "${PIPESTATUS[0]}" = 0 ] || broken+=(cache-rows)

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-7 rows as expected."

#!/usr/bin/env bash
# Round-7 regression rows (docs/AUDIT-ROUND7.md). Exits 1 if a blocked attack prints Verified, a
# control stops verifying or prints something else, or a stub fixture is misclassified.
# Every attack verification passes --fresh (no result or replay cache: the cold path); the cache
# itself is attacked by audit/round7/run-cache.sh, which this script runs last.
# Writes only under audit/round7/work/ and audit/round7/bin/ (run-cache.sh: a temporary cache).
# Usage: audit/round7/run-round7.sh [-j N]   (the --fresh verifications, each a cold kernel replay of
#        the framework, run N at once: scripts/lib/parallel.sh; fixtures are built first, in order)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
par_init "$@"
J="$root/audit/round7/bin/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
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

# Fixtures first, in order (builds, extractions and the hardware checks); then the verification
# rows as independent parallel blocks, each on its own copy of the extraction it verifies (a
# successful verification writes verified.json into it). Output is printed in this order.
echo "== G1: runtime stubs by exact go1.26 name (audit/round7/asmstub: assembly in package lib)"
gob -o "$root/$W/asmstub" ./cmd || { echo "  asmstub build failed"; broken+=(G1-build); }
xa="$("$J" extract $W/asmstub main.Add $W/AsmAdd 2>&1)"; xi="$("$J" extract $W/asmstub main.Inc $W/AsmInc 2>&1)"
if grep -qE 'code .* runtime\.panicJanusR7$' <<<"$xa" && grep -qE 'code .* runtime\.morestackJanusR7$' <<<"$xi" &&
   grep -qE 'stub .* panic +runtime\.gopanic$' <<<"$xi" && ! grep -qE 'stub .*JanusR7' <<<"$xa$xi"; then
  echo "  G1 extraction                        ok       runtime.*JanusR7 are code; Inc reaches runtime.gopanic"
else echo "  G1 extraction: misclassified   <-- BROKEN"; echo "$xa"$'\n'"$xi" | sed 's/^/    /'; broken+=(G1-extract); fi
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
cp -r $W/AsmAdd $W/AsmAdd-c
par_run 'v G1a_asm_runtime_stub_panics $W/AsmAdd;      row G1a_asm_runtime_stub_panics blocked'
par_run 'v G1b_asm_runtime_stub_neverpanics $W/AsmInc; row G1b_asm_runtime_stub_neverpanics blocked'
g1c_pat="ABIReturn s s' ∧ s'.regs 0 = x + y"
par_run 'v G1c_asmstub_returns $W/AsmAdd-c;            row G1c_asmstub_returns Verified "$g1c_pat"'
par_wait

echo "== G3 (round 8): stubs pinned to their code, not to build info (audit/round8/govers: go1.25.5 labelled go1.26.0)"
# lib's assembly runtime·panicSimdImm returns 0; the go1.25 runtime has no function of that name
# and the binary claims go1.26.0 (-X runtime.buildVersion). Built by the round-8 red team.
G3=audit/round8
if ( cd $G3/govers && GOTOOLCHAIN=go1.25.5 CGO_ENABLED=0 GOOS=linux GOARCH=arm64 \
     go build -trimpath -buildvcs=false -ldflags=-X=runtime.buildVersion=go1.26.0 -o "$root/$W/govers" ./cmd ); then
  gv="$(go version "$W/govers" 2>&1)"
  case $gv in *": go1.26.0") ;; *) echo "  G3 fixture: build info says '$gv', not go1.26.0   <-- BROKEN"; broken+=(G3-label) ;; esac
  out="$("$J" extract $W/govers main.Add $W/GvAdd 2>&1)"
  row G3a_spoofed_goversion_extract blocked "is not the Go runtime's runtime.panicSimdImm" "round 8 G3"
  [ -e $W/GvAdd/Extracted.lean ] && { echo "  G3a: extraction wrote Extracted.lean   <-- BROKEN"; broken+=(G3a-written); }
  # the extraction round 7 accepted (stub runtime.panicSimdImm): verify re-extracts and rejects it
  rm -rf $W/GvAdd; mkdir -p $W/GvAdd; cp $G3/r7-extraction/GvAdd/* $W/GvAdd/
  par_run 'out="$("$J" verify --fresh --janus-root "$root" --proof "$G3/attacks/G3a_spoofed_goversion_stub.lean" $W/GvAdd 2>&1)"
  row G3a_spoofed_goversion_stub blocked "is not the Go runtime'"'"'s runtime.panicSimdImm"'
  if command -v qemu-aarch64 >/dev/null; then
    q="$(qemu-aarch64 $W/govers 2>&1)"
    if [ "$q" = 3 ]; then echo "  G3 hardware (qemu-aarch64)           ok       Add(1, 2) = 3 (returns; no panic)"
    else echo "  G3 hardware: got '$q'   <-- BROKEN"; broken+=(G3-qemu); fi
  fi
else echo "  G3 fixture build failed (needs GOTOOLCHAIN=go1.25.5)   <-- BROKEN"; broken+=(G3-build); fi

echo "== G2: the entry symbol is the binary's label (//go:linkname push to example.com/basic.Add)"
"$J" extract $W/asmstub example.com/basic.Add $W/Label >/dev/null || broken+=(G2-extract)
par_run 'v G2a_pushed_entry_label $W/Label; row G2a_pushed_entry_label Verified "Entry: example.com/basic.Add" "Module: example.com/asmstub"'
par_wait

echo "== H1: bound-variable names"
for c in H1a H1c H1d H1b J1 K1; do rm -rf $W/Add-$c; cp -r $W/Add $W/Add-$c; done
par_run 'v H1a_binder_lookalike_vacuous $W/Add-H1a;   row H1a_binder_lookalike_vacuous blocked "binds two variables whose names look alike"'
par_run 'v H1c_binder_cyrillic_guillemets $W/Add-H1c; row H1c_binder_cyrillic_guillemets blocked "characters other than identifier letters"'
par_run 'v H1d_binder_zero_width $W/Add-H1d;          row H1d_binder_zero_width blocked "characters other than identifier letters"'
par_run 'v H1b_binder_greek_honest $W/Add-H1b;        row H1b_binder_greek_honest Verified "(α β : BitVec 64)"'

# K1 (one block: its explain rows read the verified.json of the verification before them)
par_run 'echo "== K1: notes on standard operations that read unexpectedly"
K=$W/Add-K1
v K1a_misleading_ops $K; row K1a_misleading_ops Verified "Notes (standard Lean meaning" "\`^\` wraps at" "division by zero is total at Nat" "Nat subtraction truncates at 0"
out="$("$J" verify --fresh --janus-root "$root" --proof examples/proofs/Add.lean $K 2>&1)"; row K1b_honest_add_no_notes Verified
grep -q "Notes (" <<<"$out" && { echo "  K1b: the honest Add proof got notes   <-- BROKEN"; broken+=(K1b-notes); }
out="$("$J" explain $K/verified.json 2>&1)"
row_e() { grep -q "Read with care" <<<"$out" && echo "  K1b explain: unexpected notes   <-- BROKEN" && broken+=(K1b-explain); }; row_e
"$J" verify --fresh --janus-root "$root" --proof $A/K1a_misleading_ops.lean $K >/dev/null 2>&1
out="$("$J" explain $K/verified.json 2>&1)"
if grep -q "Read with care" <<<"$out"; then echo "  K1a explain                          ok       notes shown"; else echo "  K1a explain: no notes   <-- BROKEN"; broken+=(K1a-explain); fi'

dep="$(audit/round7/dep/setup.sh "$root/$W/dep" "$root")" || { echo "  dependency fixture failed"; broken+=(dep-setup); }
par_run 'echo "== J1: dependency definitions are disclosed with their bodies"
out="$("$J" verify --fresh $W/Add-J1 --janus-root "$root" --proof "$dep/R7Proofs/Proofs.lean" --proof-root "$dep" --theorem R7Proofs.misnamed 2>&1)"
row J1a_misnamed_dependency_def Verified "Dependency definitions used by the statement" "MisLib.mul : BitVec (64 : Nat) → BitVec (64 : Nat) → BitVec (64 : Nat) := fun (a b : BitVec (64 : Nat)) => a + b"'
par_wait

echo "== unit rows (go test)"
(cd cmd/janus && go test -timeout 30m -run 'TestStubKind|TestClassifyStub|TestStubPin|TestTermSafe' . >/dev/null 2>&1) ||
  { echo "  >>> TestStubKind/TestClassifyStub/TestStubPin*/TestTermSafe failed"; broken+=(gotest); }

echo "== result cache (audit/round7/run-cache.sh)"
audit/round7/run-cache.sh | sed 's/^/  /'
[ "${PIPESTATUS[0]}" = 0 ] || broken+=(cache-rows)

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-7 rows as expected."

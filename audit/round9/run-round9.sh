#!/usr/bin/env bash
# Round-9 regression rows (docs/AUDIT-ROUND9.md). Exits 1 if a blocked attack verifies, a
# control stops verifying, a kernel-checked model row changes verdict, or a real-binary probe
# contradicts what the fixed statements assume.
# Every janus verification uses --fresh and a private temporary cache. Writes only under
# audit/round9/work/, audit/round9/bin/ and a mktemp directory (removed at the end).
# Needs: go1.26.0 (GOTOOLCHAIN), qemu-aarch64, gdb (amd64 probe rows).
# Usage: audit/round9/run-round9.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="$root/audit/round9/bin/janus"; mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
[ -d artifacts/amd64/NewPair ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
W=audit/round9/work/rows; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round9.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
for f in Add NewPair; do
  mapfile -t tg < <(scripts/example-targets.sh "$f")
  "$J" extract artifacts/examples-arm64 "example.com/basic.$f" "$W/$f" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
done
LEAN="$(lake env which lean)"; LP="$root/.lake/build/lib/lean"
broken=()
A=audit/round9/attacks

# row NAME EXPECT [PATTERN...] on $out: EXPECT "blocked" (no Verified; patterns must appear) or
# "Verified" (Verified and every pattern).
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
  printf '  %-40s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
# check NAME OK-CONDITION-EXIT-STATUS MESSAGE
check() {
  if [ "$2" = 0 ]; then printf '  %-40s ok       %s\n' "$1" "$3"
  else printf '  %-40s FAILED   %s   <-- BROKEN\n' "$1" "$3"; broken+=("$1"); fi
}
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== C1: allocation contracts must be satisfiable (kernel-checked)"
o="$(lake env lean audit/round9/model/Unsat.lean 2>&1)"; check C1a_pre_fix_contract_unsat $? "the pre-round-9 newobject contract is false for every program/addr/rt ${o:+($o)}"
lake env lean audit/round9/model/UnsatFixed.lean >/dev/null 2>&1; rc=$?
[ $rc -ne 0 ]; check C1b_fixed_contract_unsat_attempt $? "the same argument against the fixed contract does not compile"
D="$T/ctl/NewPair"; mkdir -p "$D"; cp "$W/NewPair/Extracted.lean" "$D/"; cp examples/proofs/NewPair.lean "$D/Proof.lean"
cp audit/round9/controls/NewPair_witness.lean "$D/W.lean"
( cd "$D" && LEAN_PATH="$LP:." "$LEAN" --root=. -o Extracted.olean Extracted.lean &&
  LEAN_PATH="$LP:." "$LEAN" --root=. -o Proof.olean Proof.lean &&
  LEAN_PATH="$LP:." "$LEAN" --root=. W.lean ) > "$T/w.log" 2>&1
check C1c_newpair_witness_fires $? "an allocator, rt, H and a NewPair call for which Proof.correctness fires"
v examples/proofs/NewPair.lean "$W/NewPair"; row C1_ctl_NewPair Verified 'RtReady' 'rtView rt s.mem'

echo "== SAT: every runtime contract has a kernel-checked _satisfiable witness (lake build Janus checked them)"
o="$(python3 -I audit/round9/sat_check.py "$root")"; rc=$?
grep -E 'SAT (MISSING|OPEN)' <<<"$o" | sed 's/^/  /'
check SAT_contract_witnesses $rc "$(tail -n 1 <<<"$o")"
S9="$T/satcopy"; mkdir -p "$S9/audit/round9"; cp -r Janus Janus.lean "$S9/"; cp audit/round9/sat-pending.txt "$S9/audit/round9/"
sed -i 's/^theorem newobject_satisfiable/theorem newobject_satisfiable_gone/' "$S9/Janus/Contracts/AllocSat.lean"
python3 -I audit/round9/sat_check.py "$S9" >/dev/null 2>&1; rc=$?
[ $rc -ne 0 ]; check SAT_selftest_missing_witness_fails $? "removing newobject_satisfiable makes the SAT row fail"

echo "== real-binary probes (audit/round9/probe; go1.26.0)"
P="$T/probe"; mkdir -p "$P"
( cd audit/round9/probe && export GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 &&
  GOARCH=amd64 GOAMD64=v1 go build -trimpath -o "$P/probe9-amd64" . &&
  GOARCH=arm64 go build -trimpath -o "$P/probe9-arm64" . ) || { echo "probe build failed"; exit 1; }
o="$("$P/probe9-amd64" big 44 2>&1)"
grep -q 'out of memory' <<<"$o" && ! grep -q returned <<<"$o"
check C1d_real_runtime_throws_oom $? "MakeSlice(1<<44) (8·2^44 ≤ maxAlloc, admitted by the old contract) throws: $(grep -m1 'out of memory' <<<"$o" | cut -c1-70)"
o1="$("$P/probe9-amd64" hdr 50 | sort -u | tr '\n' ' ')"; o2="$(qemu-aarch64 "$P/probe9-arm64" hdr 50 | sort -u | tr '\n' ' ')"
[ "$o1" = "8 " ] && [ "$o2" = "8 " ]
check C2a_header_objects_8_mod_16 $? "new([66]*int) (528 bytes, pointerful): address mod 16 = amd64 {${o1% }} arm64 {${o2% }}"
cat > "$T/hdr.lean" <<'EOF'
import Janus
open Janus.Contracts
example : mallocHdr 528 false = true ∧ mallocHdr 528 true = false ∧ mallocHdr 512 false = false ∧
    mallocHdr 32760 false = true ∧ mallocHdr 32768 false = false := by decide
EOF
lake env lean "$T/hdr.lean" >/dev/null 2>&1; check C2b_mallocHdr_model $? "the contract only promises 8-alignment for those (mallocHdr)"
o="$(qemu-aarch64 "$P/probe9-arm64" mcache 20000)"
sh="$(sed -n 's/.*MCacheOK(shipped)=\([0-9]*\).*/\1/p' <<<"$o")"; fx="$(sed -n 's/.*MCacheOK(round 9)=\([0-9]*\).*/\1/p' <<<"$o")"
[ "${sh:-1}" = 0 ] && [ "${fx:-0}" -ge 18000 ]
check M1_mcacheok_real_calls $? "of 20000 real 64-byte requests on m0: old MCacheOK holds for ${sh:-?}, round-9 MCacheOK for ${fx:-?}"
if command -v gdb >/dev/null; then
  o="$(cd "$P" && timeout 1200 gdb -batch -x "$root/audit/round9/probe/setnext_amd64.py" --args ./probe9-amd64 loopgc 200000 2>&1 | grep PROBE)"
  on="$(sed -n 's/.*barrier_on=\([0-9]*\).*/\1/p' <<<"$o")"; old="$(sed -n 's/.*barrierok_satisfiable=\([0-9]*\).*/\1/p' <<<"$o")"
  new="$(sed -n 's/.*barrierok_round9=\([0-9]*\).*/\1/p' <<<"$o")"
  [ -n "$on" ] && [ "$old" -lt "$on" ] && [ "$new" = "$on" ]
  check S1_barrierok_real_calls $? "SetNext calls with the barrier on: $on; old [lo,hi) BarrierOK satisfiable for $old, round-9 BarrierOK for $new"
  o="$(cd "$P" && timeout 1200 gdb -batch -x "$root/audit/round9/probe/maps_amd64.py" --args ./probe9-amd64 maps 2000 2>&1 | grep PROBE)"
  sm="$(sed -n 's/.*small=\([0-9]*\).*/\1/p' <<<"$o")"; hk="$(sed -n 's/.*heap_interval_ok=\([0-9]*\).*/\1/p' <<<"$o")"
  [ -n "$sm" ] && [ "$sm" -gt 0 ] && [ "$hk" = "$sm" ]
  check MP_smallmodel_heap_interval $? "small-map lookups: $sm; one heap interval holds header and group and misses the stack window at $hk"
else printf '  %-40s skipped  (no gdb)\n' S1_barrierok_real_calls; fi
"$P/probe9-amd64" grow 3000000 > "$T/grow-amd64"; qemu-aarch64 "$P/probe9-arm64" grow 3000000 > "$T/grow-arm64"
o="$(cmp "$T/grow-amd64" "$T/grow-arm64" && audit/round9/model/grow_check.sh "$T/grow-arm64" 2>&1)"
grep -q 'GROW OK' <<<"$o"; check G1_growslice_capacity_exact $? "$o"

echo "== H2: bound-variable lookalikes the round-7 fold missed"
for a in H2a_binder_tonos_oxia H2b_binder_kelvin H2c_binder_prosgegrammeni; do
  v $A/$a.lean "$W/Add"; row "$a" blocked 'round 9 H2'
done
v audit/round7/attacks/H1a_binder_lookalike_vacuous.lean "$W/Add"; row H1a_still_blocked blocked 'look alike'
v audit/round7/attacks/H1b_binder_greek_honest.lean "$W/Add"; row H2_ctl_H1b_greek_honest Verified

echo "== I1g: contract names must be recorded contracts"
v $A/I1g_contract_name_lookalike.lean "$W/Add"; row I1g_contract_name_lookalike blocked 'runtime contract'

echo "== D1: docs/SOUNDNESS.md keeps the sections the stubpin merge dropped"
for s in '## Runtime contracts' '**Toolchain identity.**' '**The cache root must be private**' \
         '**Object names must resolve**' '**A contract must be satisfiable, and by the real runtime**'; do
  grep -qF -- "$s" docs/SOUNDNESS.md; check "D1 ${s:0:34}" $? "present"
done

echo "== MG: memory-guard settings change limits only, never a verdict"
for mg in prlimit systemd-user none bogus; do
  out="$(JANUS_MEMGUARD=$mg JANUS_MEM_MAX=300M "$J" verify --fresh --janus-root "$root" --proof audit/round7/attacks/H1a_binder_lookalike_vacuous.lean "$W/Add" 2>&1)"
  row "MG_attack_JANUS_MEMGUARD=$mg" blocked
done
out="$(JANUS_MEMGUARD=prlimit "$J" verify --fresh --janus-root "$root" --proof examples/proofs/Add.lean "$W/Add" 2>&1)"
row MG_ctl_Add_prlimit Verified

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-9 rows as expected."

#!/usr/bin/env bash
# UP3b verify-level regression runner (docs/SOUNDNESS.md "UP3"): real `janus verify` runs (NOT --audit-only), so the witness requirement is in force.
#   rows       every red-team row of the n11/up3 rounds (rows/, vrows/PIN*) must be REJECTED, with and without --allow-no-witness, for the expected reason
#   attackers  vrows/ATT_*, wit/WIT1-5 (witness-bearing): REJECTED with the reason named in their "Expected-reason:" header
#   controls   ctl/*.lean (witness-bearing, frozen shape) must VERIFY (correctness + Witness.nonvacuous); statement-only controls (C1 V15 F01 F08 W02 W03,
#              pre False: no witness can exist) must pass the statement audit (--audit-only prints `Audit-only:`)
#   known-accepted  vrows/KA1.lean: ACCEPTED on purpose (path reachability is not required)
# Usage: test/redteam/rounds/roundup3/run-verify-rows.sh   (env: JANUS_AUDIT_BIN, JANUS_AUDIT_PREBUILT=1)   Exits 1 if a row differs.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/roundup3
J="${JANUS_AUDIT_BIN:-$root/bin/janus}"
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || { CGO_ENABLED=0 go build -o "$J" ./cmd/janus && lake build Janus Janus.Tools.Audit >/dev/null || { echo "build failed"; exit 1; }; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W="$(mktemp -d "${TMPDIR:-/tmp}/janus-vrows.XXXXXX")" || exit 1
trap 'rm -rf "$W"' EXIT
mkdir -m 700 "$W/cache"; export JANUS_CACHE_DIR="${JANUS_CACHE_DIR:-$W/cache}"
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh Add)
"$J" extract artifacts/examples-arm64 "$(example_symbol Add)" "$W/Add" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || { echo "extract Add failed"; exit 1; }
. "$root/test/redteam/lib/blocked.sh"
RT=/srv/janus-rt-n11/audit/roundn11
bad=0
# verdict of one verify run on ARTIFACT/PROOF with THEOREMS: prints verified|rejected and leaves the output in $out
vrun() { # art proof flag thm...
  local art=$1 proof=$2 fl=$3; shift 3; local -a th=()
  for t in "$@"; do th+=(--theorem "$t"); done
  "$J" verify "$art" --proof "$proof" "${th[@]}" --janus-root "$root" $fl --no-result-cache > "$W/out.txt" 2>&1
  local nv  # one theorem: the run prints no `===` block, only `Verified:`
  if [ "$#" -eq 1 ]; then nv=$(grep -c '^Verified: ' "$W/out.txt"); else nv=$(grep -c '^=== .*: verified' "$W/out.txt"); fi
  if [ "$nv" -ge "$#" ]; then echo verified; else echo rejected; fi
}
reason_of() { # the audit's reason for the rejection in $out: the witness theorem's when it failed, else the main theorem's
  if printf '%s\n' "$out" | grep -q '^=== Proof.Witness.nonvacuous: FAILED'; then
    printf '%s\n' "$out" | awk '/^=== Proof.Witness.nonvacuous: FAILED/{w=1} w&&/^Invalid:/{print;exit}' | sed -E 's/^Invalid: (The audit rejected the proof: )?//' | cut -c1-170
  else printf '%s\n' "$out" | grep -m1 -E '^Invalid: (The audit rejected|Proof\.[A-Za-z.]* assumes)' | sed -E 's/^Invalid: (The audit rejected the proof: )?//' | cut -c1-170; fi
}
check_rejected() { # file label thm...
  local f=$1 n=$2; shift 2
  local want; want="$(grep -m1 -o 'Expected-reason: .*' "$f" | sed 's/Expected-reason: //; s/ *-\/$//')"; [ -n "$want" ] || want='.'
  for fl in "" "--allow-no-witness"; do
    local v; v=$(vrun "${ART:-$W/Add}" "$f" "$fl" "$@"); out="$(cat "$W/out.txt")"
    if [ "$v" = verified ]; then printf '%-34s %-20s VERIFIED   <-- BROKEN\n' "$n" "${fl:-no-flag}"; bad=1
    elif printf '%s' "$out" | grep -qE "$want"; then
      # the pinned reason (test/redteam/lib/blocked-pins.tsv; the Expected-reason header alone defaults to '.'), never a Lean elaboration failure
      why="$(blocked_check rounds/roundup3/run-verify-rows.sh "$n" "$out")"
      if [ -n "$why" ]; then printf '%-34s %-20s rejected for the WRONG reason   <-- BROKEN: %s\n' "$n" "${fl:-no-flag}" "$why"; bad=1
      else printf '%-34s %-20s rejected ok  [%s]\n' "$n" "${fl:-no-flag}" "$(reason_of)"; fi
    else printf '%-34s %-20s rejected for ANOTHER reason (wanted /%s/)   <-- BROKEN\n' "$n" "${fl:-no-flag}" "$want"; printf '%s\n' "$out" | grep -m3 '^Invalid' | cut -c1-300 | sed 's/^/    /'; bad=1; fi
  done
}
echo "== rows (no witness: rejected under every flag)"
for n in N10 N11 N13 N16 N17 N18 N46 N50 N51 N52 N60 N62 N64 N65; do
  f=$(ls $R/rows/${n}_*.lean); check_rejected "$f" "$n" Proof.correctness
done
# R01 is a statement about WriteTo (an abstract callee): against the Add artifact it never compiled ("too many variable names provided"),
# so the row was rejected by Lean and exercised nothing. It needs the WriteTo extraction.
mapfile -t tgW < <(scripts/example-targets.sh WriteTo)
"$J" extract artifacts/examples-arm64 "$(example_symbol WriteTo)" "$W/WriteTo" ${tgW[@]+"${tgW[@]}"} >/dev/null 2>&1 || { echo "extract WriteTo failed"; bad=1; }
ART="$W/WriteTo" check_rejected $RT/rows2/R01_R_pinned_false_in_pre.lean R01 Proof.correctness
for f in $R/vrows/PIN*.lean; do check_rejected "$f" "$(basename "$f" .lean)" Proof.correctness; done
echo "== attackers (witness-bearing: rejected for the named reason)"
for f in $R/vrows/ATT_*.lean $R/wit/WIT[1-6]_*.lean; do check_rejected "$f" "$(basename "$f" .lean)" Proof.correctness Proof.Witness.nonvacuous; done
echo "== strict pairing (UP3d): Witness.nonvacuous <-> correctness, Witness.<X> <-> main <X>, nothing else"
check_rejected $R/pair/PAIR1_missing_witness_extra.lean PAIR1 Proof.correctness Proof.extra Proof.Witness.nonvacuous
check_rejected $R/pair/PAIR2_witness_extra_tied_to_correctness.lean PAIR2 Proof.correctness Proof.extra Proof.Witness.nonvacuous Proof.Witness.extra
check_rejected $R/pair/PAIR3_nonvacuous_tied_to_extra.lean PAIR3 Proof.correctness Proof.extra Proof.Witness.nonvacuous Proof.Witness.extra
check_rejected $R/pair/PAIR4_witness_name_pairs_no_main.lean PAIR4 Proof.correctness Proof.extra Proof.Witness.nonvacuous Proof.Witness.extra Proof.Witness.other
v=$(vrun "$W/Add" $R/pair/PAIR_ok_control.lean "" Proof.correctness Proof.extra Proof.Witness.nonvacuous Proof.Witness.extra)
if [ "$v" = verified ]; then printf '%-34s verified ok\n' PAIR_ok_control; else printf '%-34s REJECTED   <-- BROKEN\n' PAIR_ok_control; bad=1; fi
echo "== Faults / fact-conjunct anchoring (UP3d, on LoadThird)"
mapfile -t tgL < <(scripts/example-targets.sh LoadThird)
"$J" extract artifacts/examples-arm64 "$(example_symbol LoadThird)" "$W/LoadThird" ${tgL[@]+"${tgL[@]}"} >/dev/null 2>&1 || { echo "extract LoadThird failed"; bad=1; }
FT="Proof.correctness Proof.faults Proof.Witness.nonvacuous Proof.Witness.faults"
v=$(vrun "$W/LoadThird" $R/pair/FLT_ok_control.lean "" $FT)
if [ "$v" = verified ]; then printf '%-34s verified ok\n' FLT_ok_control; else printf '%-34s REJECTED   <-- BROKEN\n' FLT_ok_control; bad=1; fi
for n in FLT1_false_premise FLT2_faults_untied_state FLT3_fact_other_state; do ART="$W/LoadThird" check_rejected $R/pair/$n.lean $n $FT; done
echo "== controls (witness-bearing: must VERIFY)"
for f in $R/ctl/*.lean; do
  n=$(basename "$f" .lean)
  v=$(vrun "$W/Add" "$f" "" Proof.correctness Proof.Witness.nonvacuous); out="$(cat "$W/out.txt")"
  if [ "$v" = verified ]; then printf '%-34s verified ok\n' "$n"; else printf '%-34s REJECTED   <-- BROKEN\n' "$n"; printf '%s\n' "$out" | grep -m3 '^Invalid' | cut -c1-300 | sed 's/^/    /'; bad=1; fi
done
echo "== statement-only controls (pre False, no witness can exist): the statement audit accepts"
declare -A ctlart
ctlart[C1_stub_control]=ErrWrap; ctlart[F01_live_stack4096]=AppendOne; ctlart[F08_newobj_live_ok]=NewPair
ctlart[W02_d_ok]=MbarTypedmemmove; ctlart[W03_d_var_lower]=MbarTypedmemmove; ctlart[V15_control_ok]=Add
for n in C1_stub_control F01_live_stack4096 F08_newobj_live_ok W02_d_ok W03_d_var_lower V15_control_ok; do
  f=$(ls $RT/icall/$n.lean $RT/icall2/$n.lean 2>/dev/null | head -1); a=${ctlart[$n]}
  if [ "$a" = Add ]; then art="$W/Add"; else
    art="$W/$a"; [ -d "$art" ] || { mapfile -t tg2 < <(scripts/example-targets.sh "$a"); "$J" extract artifacts/examples-arm64 "$(example_symbol "$a")" "$art" ${tg2[@]+"${tg2[@]}"} >/dev/null 2>&1 || echo "extract $a failed"; }
  fi
  o="$("$J" verify "$art" --proof "$f" --theorem Proof.correctness --janus-root "$root" --audit-only --no-result-cache 2>&1)"
  if printf '%s' "$o" | grep -q '^Audit-only:'; then printf '%-34s statement audit ok\n' "$n"; else printf '%-34s REJECTED   <-- BROKEN\n' "$n"; printf '%s\n' "$o" | grep -m2 '^Invalid' | cut -c1-300 | sed 's/^/    /'; bad=1; fi
done
echo "== run-free control (hypothesis-free, no run claim): verifies, reported as run-free"
for f in $R/vrows/RF*.lean; do
  v=$(vrun "$W/Add" "$f" "" Proof.correctness); out="$(cat "$W/out.txt")"
  if [ "$v" = verified ] && printf '%s' "$out" | grep -q 'run-free'; then printf '%-34s verified (run-free) ok\n' "$(basename "$f" .lean)"; else printf '%-34s NOT run-free-verified   <-- BROKEN\n' "$(basename "$f" .lean)"; bad=1; fi
done
echo "== known-accepted"
if [ -f $R/vrows/KA1.lean ]; then
  v=$(vrun "$W/Add" $R/vrows/KA1.lean "" Proof.correctness Proof.Witness.nonvacuous); out="$(cat "$W/out.txt")"
  if [ "$v" = verified ]; then echo "KA1                                known-accepted (verified, documented limitation)"; else echo "KA1  REJECTED  <-- the documented limitation changed"; printf '%s\n' "$out" | grep -m3 '^Invalid' | cut -c1-300; bad=1; fi
fi
[ $bad = 0 ] && echo "verify rows: all as expected" || echo "verify rows: BROKEN rows"
exit $bad

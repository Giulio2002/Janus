#!/usr/bin/env bash
# Audit-only sweep (UP3b): run the statement + witness audit (JANUS_STOP_AFTER_AUDIT=1, no verification) over every example proof
# of the arm64 (examples/proofs) and amd64 (examples/proofs-amd64) sweeps and list the theorems the audit rejects.
# Usage: audit/roundup3/audit-sweep.sh OUTDIR [arm64|amd64] [Name ...]    (default: every example, both ISAs)
# OUTDIR/results.tsv: ISA<TAB>Name<TAB>ok|REJECT|NOPROOF<TAB>first reason; OUTDIR/logs/ISA-Name.log; extractions in OUTDIR/art.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
out="${1:?outdir}"; shift; isa="${1:-both}"; [ $# -gt 0 ] && shift
mkdir -p "$out/logs" "$out/art" "$out/cache"; export JANUS_CACHE_DIR="$out/cache"
J="${JANUS_BIN:-$root/bin/janus}"
. scripts/example-contracts.sh
one() { # ISA NAME
  local i=$1 n=$2 proof art sym log="$out/logs/$1-$2.log"
  if [ $i = arm64 ]; then proof=examples/proofs/$n.lean; sym=$(example_symbol "$n"); art="$out/art/arm64-$n"
    [ -d "$art" ] || { mapfile -t tg < <(scripts/example-targets.sh "$n"); "$J" extract artifacts/examples-arm64 "$sym" "$art" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1; }
  else proof=examples/proofs-amd64/$n/Proof.lean; art=artifacts/amd64/$n; fi
  [ -f "$proof" ] && [ -d "$art" ] || { printf '%s\t%s\tNOPROOF\t\n' $i $n; return; }
  local -a th=(--theorem Proof.correctness)
  grep -q '^namespace Witness' "$proof" && th+=(--theorem Proof.Witness.nonvacuous)
  local t0=$(date +%s.%N)
  JANUS_STOP_AFTER_AUDIT=1 memcap -m 24G "$J" verify "$art" --proof "$proof" "${th[@]}" --janus-root "$root" --no-result-cache > "$log" 2>&1
  local rc=$? dt=$(echo "$(date +%s.%N) - $t0" | bc)
  local nth=${#th[@]}; nth=$((nth/2)); local ok; ok=$(grep -c 'AUDIT-STAGE-OK' "$log")
  # the dev hook always ends in "Invalid: AUDIT-STAGE-OK <thm>" (never a verification): success = one AUDIT-STAGE-OK line per theorem
  if [ "$ok" -ge "$nth" ]; then printf '%s\t%s\tok\t%.1fs\n' $i $n "$dt"
  else printf '%s\t%s\tREJECT\t%s\n' $i $n "$(grep -v 'AUDIT-STAGE-OK' "$log" | grep -m1 -E '^Invalid|^janus|rror' | cut -c1-400)"; fi
}
# JANUS_SWEEP_JOBS (default 3) audits run at once; JANUS_SWEEP_ALL=1 audits every example proof, else only those that mention a pinned
# runtime contract (the only ones the call-site rule can concern)
export -f one example_symbol runtime_symbol; export out root J isa
names=("$@")
mkdir -p "$out/tmp"; : > "$out/tmp/list"
cands() { # directory-style proof files -> names that mention a contract
  grep -lE "(Contract|Live|Memmove|Memequal|Access[12]|Assign|Delete|Iter|Memhash|Strhash|Rand|Equal|Ifaceeq|Efaceeq|Cmpstring|Typed|Memclr|Pool|Lock|Soft|KeepAlive|Sched|Gopanic|Goexit|Deferreturn|Morestack|Errorf|ConvT|AssertE2I|TypeAssert|Interface|Cgo|Checkptr|Wb|Defer|Gorecover|Chash|Fhash|Interhash|Nilinterhash|Typehash|Clear|MakeSmall|MakeMap|BulkBarrier)" "$@" 2>/dev/null
}
if [ "$isa" != amd64 ]; then
  if [ ${#names[@]} -gt 0 ]; then L=("${names[@]}"); elif [ "${JANUS_SWEEP_ALL:-}" = 1 ]; then L=($(ls examples/proofs/*.lean | xargs -n1 basename | sed 's/\.lean$//'));
  else L=($(cands examples/proofs/*.lean | xargs -n1 basename | sed 's/\.lean$//')); fi
  for n in "${L[@]}"; do echo "arm64 $n" >> "$out/tmp/list"; done
fi
if [ "$isa" != arm64 ]; then
  if [ ${#names[@]} -gt 0 ]; then L=("${names[@]}"); elif [ "${JANUS_SWEEP_ALL:-}" = 1 ]; then L=($(ls examples/proofs-amd64));
  else L=($(cands examples/proofs-amd64/*/Proof.lean | xargs -n1 dirname | xargs -n1 basename)); fi
  for n in "${L[@]}"; do echo "amd64 $n" >> "$out/tmp/list"; done
fi
xargs -P "${JANUS_SWEEP_JOBS:-3}" -L1 bash -c 'one "$@"' _ < "$out/tmp/list"

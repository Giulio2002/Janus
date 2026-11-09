#!/usr/bin/env bash
# Round-15 regression rows (docs/SOUNDNESS.md "Non-vacuity is required for contract-assuming main theorems"):
# `janus verify` rejects a MAIN theorem that assumes runtime contracts unless a kernel-checked non-vacuity
# witness for THAT theorem is verified in the same run; every report states the status; --allow-no-witness
# is inert (UP3); --audit-only is not a verification; a theorem without contract hypotheses is verified with its tied witness.
#   N1  main alone                              -> blocked (stage non-vacuity)
#   N2  main + Witness.nonvacuous (+ returns)   -> verified, "shown by"
#   N3  main + only Witness.returns             -> blocked (a concrete run does not state the contract hypotheses)
#   N4  main + a weaker witness (a conjunct of the precondition left out, plain and as an applied lambda) -> blocked
#   N5  main + a witness under another name (`alt`), or stated as an applied lambda (`lam`) -> verified, "shown by"
#   N6  a second main theorem with a hypothesis no witness exhibits -> blocked, the first stays verified
#   N7  --allow-no-witness (inert) -> blocked; N7b --audit-only -> 'Audit-only', no Verified line, no verified.json
#   N8  a theorem without contract hypotheses   -> verified, "Non-vacuity: NOT SHOWN" (no contract)
# Exits 1 if a row differs. Uses a private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/round15
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round15.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
for n in NewPair Add; do
  mapfile -t tg < <(scripts/example-targets.sh $n)
  "$J" extract artifacts/examples-arm64 "$(example_symbol $n)" "$W/$n" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
done
broken=()
P=Proof
F=$R/attacks/NvForms.lean
# run NAME PROOF ART [flags] -- THEOREM...  -> $all
run() {
  local proof=$1 art=$2; shift 2
  local -a fl=() th=()
  while [ $# -gt 0 ] && [ "$1" != -- ]; do fl+=("$1"); shift; done
  shift
  for t in "$@"; do th+=(--theorem "$P.$t"); done
  all="$("$J" verify --janus-root "$root" --proof "$proof" "$art" ${fl[@]+"${fl[@]}"} "${th[@]}" 2>&1)"
}
blk() { awk -v n="=== $P.$1:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all"; }
. "$root/test/redteam/lib/blocked.sh"
row() { # NAME expect(blocked|Verified) pattern...   (single-theorem runs: the whole output)
  local name=$1 expect=$2 out verdict status="" pat; shift 2
  out="$(blk "$name")"; [ -n "$out" ] || out="$all"
  verdict="$(grep -m1 -E '^(=== |Verified:|Invalid:|FAIL)' <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in *verified*|Verified:*) status=BROKEN ;; esac ;;
    Verified) case $verdict in *verified*|Verified:*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  # blocked rows: pinned reason, and no Lean elaboration failure (test/redteam/lib/blocked.sh)
  if [ "$expect" = blocked ]; then why="$(blocked_check rounds/round15/run-round15.sh "$([ "$name" = correctness ] && echo "${sect:-?}:$name" || echo "$name")" "$out")"; [ -n "$why" ] && { status=BROKEN; verdict="$verdict [$why]"; }; fi
  printf '  %-34s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
echo "== N1: a contract-assuming main theorem without a witness is rejected"; sect=N1
run $F "$W/NewPair" -- correctness
row correctness blocked 'Stage: non-vacuity' 'jointly satisfiable' 'anonymous `example`'
echo "== N2: with its witness"; sect=N2
run $F "$W/NewPair" -- correctness Witness.nonvacuous Witness.returns
row correctness Verified 'Non-vacuity: shown by Proof.Witness.nonvacuous'
row Witness.nonvacuous Verified 'Non-vacuity: this is a witness'
echo "== N3: Witness.returns alone does not show non-vacuity"; sect=N3
run $F "$W/NewPair" -- correctness Witness.returns
row correctness blocked 'Stage: non-vacuity' 'does not show non-vacuity'
echo "== N4: a weaker witness is no witness (the mains weak and lamWeak are the same statement as correctness; its witness leaves a conjunct out)"; sect=N4
run $F "$W/NewPair" -- weak Witness.weak
row weak blocked 'Stage: non-vacuity'
row Witness.weak blocked 'round 14, W2' 'is not among the conjuncts of the witness'
run $F "$W/NewPair" -- lamWeak Witness.lamWeak
row lamWeak blocked 'Stage: non-vacuity'
row Witness.lamWeak blocked 'round 14, W2' 'conjuncts are matched after beta-reduction'
echo "== N5: the witness of main X is Witness.X (any main name), also stated as an applied lambda; it never vouches for another main"; sect=N5
run $F "$W/NewPair" -- correctness alt Witness.nonvacuous Witness.alt
row alt Verified 'Non-vacuity: shown by Proof.Witness.alt'
row Witness.alt Verified 'Role: WITNESS'
run $F "$W/NewPair" -- correctness lam Witness.nonvacuous Witness.lam
row lam Verified 'Non-vacuity: shown by Proof.Witness.lam'
row Witness.lam Verified 'Role: WITNESS'
run $F "$W/NewPair" -- correctness Witness.alt
row correctness blocked 'Stage: non-vacuity'
echo "== N6: a witness supports the theorems it instantiates, not another main theorem"; sect=N6
run $F "$W/NewPair" -- correctness otherMain Witness.nonvacuous
row correctness Verified 'Non-vacuity: shown by'
row otherMain blocked 'Stage: non-vacuity'
echo "== N7: --allow-no-witness is inert (UP3): a contract-assuming theorem without a verified witness is still rejected"; sect=N7
run $F "$W/NewPair" --allow-no-witness -- correctness
row correctness blocked 'Stage: non-vacuity' 'does not bypass'
run $F "$W/NewPair" --allow-no-witness -- correctness Witness.nonvacuous
row correctness Verified 'Non-vacuity: shown by'
echo "== N7b: --audit-only is not a verification: 'Audit-only', no Verified line, no verified.json"; sect=N7b
run $F "$W/NewPair" --audit-only -- correctness
row correctness blocked 'Audit-only:' 'NOT A VERIFICATION'
[ ! -e "$W/NewPair/verified.json" ] && ! grep -q '^Verified:' <<<"$all" || broken+=(audit-only-wrote-report)
echo "== N8: a theorem without contract hypotheses is verified with its tied witness (UP3c: every main theorem needs one) and reports no contracts"; sect=N8
run examples/proofs/Add.lean "$W/Add" -- correctness Witness.nonvacuous
row correctness Verified 'Non-vacuity: shown by Proof.Witness.nonvacuous' 'Runtime contracts assumed: none'
if [ ${#broken[@]} -gt 0 ]; then echo "round 15: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round 15: all rows as expected"

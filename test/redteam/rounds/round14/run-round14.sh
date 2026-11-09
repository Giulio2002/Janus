#!/usr/bin/env bash
# Round-14 regression rows (docs/audit/AUDIT.md, docs/SOUNDNESS.md "Round 14"): the runtime of a MAIN theorem is
# quantified, never chosen, and witnesses have a checked shape.
#   V2  a theorem about `Extracted.program.link impl` for a CONCRETE `impl` (the consumer's toy allocator) with no
#       contract hypothesis used to verify and be reported as assuming the pinned `runtime.newobject` contract;
#       now every `link` of a non-witness theorem takes a variable of the statement, no segment list / program is
#       chosen or built by hand, and a theorem for the toy allocator cannot pass as a main theorem (bad1..bad8).
#   W2  `Witness.nonvacuous` / `Witness.returns` were gated by name and by "mentions Extracted.program"; now a
#       nonvacuous witness must exhibit every hypothesis and premise (call state, precondition) of the module's
#       `correctness` theorem, and a returns witness must be that theorem's guarantee at a start state (WeakA..H);
#       other `Witness.*` lemmas are not verifiable results.
# One file (test/redteam/rounds/round14/attacks/NewPairAttacks.lean), one verification of all its theorems (`--theorem` repeated).
# Exits 1 if an attack verifies or a control stops verifying. Uses --fresh and a private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/round14
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build/build-examples.sh >/dev/null
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round14.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/verify/example-contracts.sh
mapfile -t tg < <(scripts/verify/example-targets.sh NewPair)
"$J" extract artifacts/examples-arm64 "$(example_symbol NewPair)" "$W/NewPair" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
broken=()
P=Proof
thms=(correctness Witness.nonvacuous Witness.returns bad1 bad2 bad3 bad4 bad5 bad6 bad7 bad8 bad9 bad10 bad11
  WeakA.Witness.nonvacuous WeakB.Witness.nonvacuous WeakC.Witness.nonvacuous WeakD.Witness.nonvacuous
  WeakE.Witness.nonvacuous WeakF.Witness.returns WeakG.Witness.returns WeakI.Witness.returns WeakH.Witness.returns HideA.Witness.guarantee HideB.Witness.returns Witness.pre)
targs=(); for t in "${thms[@]}"; do targs+=(--theorem "$P.$t"); done
all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/NewPairAttacks.lean "$W/NewPair" "${targs[@]}" 2>&1)"
# the block of one theorem: from its "=== NAME:" line to the next one
blk() { awk -v n="=== $P.$1:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all"; }
. "$root/test/redteam/lib/blocked.sh"
row() { # NAME expect(blocked|Verified) pattern...
  local name=$1 expect=$2 out verdict status="" pat; shift 2
  out="$(blk "$name")"
  verdict="$(grep -m1 -E '^=== ' <<<"$out" | cut -c1-120)"
  [ -n "$verdict" ] || { verdict="(no block)"; status=BROKEN; }
  case $expect in
    blocked) case $verdict in *verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in *verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  # blocked rows: pinned reason, and no Lean elaboration failure (test/redteam/lib/blocked.sh)
  if [ "$expect" = blocked ]; then why="$(blocked_check rounds/round14/run-round14.sh "$name" "$out")"; [ -n "$why" ] && { status=BROKEN; verdict="$verdict [$why]"; }; fi
  printf '  %-34s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
echo "== V2: a main theorem quantifies the runtime implementation"
row bad1 blocked 'round 14' 'may link only a variable'
row bad2 blocked 'may link only a variable'
row bad3 blocked 'round 14'
row bad4 blocked 'rt-auditv2' 'other than as'
row bad5 blocked 'round 14'
row bad6 blocked 'round 14'
row bad7 blocked 'round 14'
row bad8 blocked 'about the program'
row bad9 blocked 'round 10 V1' 'RetAddr'
row bad10 blocked 'round 10 V1' 'exitAddr'
row bad11 blocked 'round 14'
echo "== W2: witnesses have a checked shape"
for w in WeakA WeakB WeakC WeakD WeakE; do row $w.Witness.nonvacuous blocked 'round 14, W2'; done
for w in WeakF WeakG WeakI WeakH; do row $w.Witness.returns blocked 'round 14, W2'; done
row HideA.Witness.guarantee blocked 'lemma of a Witness namespace'
row HideB.Witness.returns blocked 'round 14, W2' 'Returns'
row Witness.pre blocked 'round 14, W2' 'lemma of a Witness namespace'
echo "== controls"
row correctness Verified 'Role: main theorem' 'Runtime contracts assumed: Janus.Contracts.NewobjectContract@runtime.newobject'
row Witness.nonvacuous Verified 'Role: WITNESS' 'main theorem Proof.correctness'
row Witness.returns Verified 'Role: WITNESS' 'main theorem Proof.correctness'
echo "== class 7: a consumer module cannot declare a runtime contract (namespace Janus.Contracts, own def, Summary-bodied def, shadowed name)"
all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/FakeContracts.lean "$W/NewPair" \
  --theorem $P.fake1 --theorem $P.fake2 --theorem $P.fake3 2>&1)"
for f in fake1 fake2 fake3; do row $f blocked 'constrains a runtime variable'; done
echo "== (c): a witness must cover EVERY conjunct of a conjunction main theorem (IsEven ∧ IsOdd)"
mapfile -t tg < <(scripts/verify/example-targets.sh IsEven)
"$J" extract artifacts/examples-arm64 "$(example_symbol IsEven)" "$W/IsEven" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/IsEvenOneMember.lean "$W/IsEven" \
  --theorem $P.correctness --theorem $P.Witness.nonvacuous --theorem $P.Witness.returns --theorem $P.OneMember.Witness.nonvacuous 2>&1)"
row correctness Verified
row Witness.nonvacuous Verified 'Role: WITNESS'
row Witness.returns Verified 'Role: WITNESS'
row OneMember.Witness.nonvacuous blocked 'round 14, W2' 'conjunct 2 of 2'
echo "== rt-auditv2: a witness cannot skip an empty binder, a pc premise, a pinned implementation, an exists-bound closed contract"
# (PcPremise: its main theorem has post `False` and an unsatisfiable pc premise, so no witness can carry the returning run or even a
# call-site state tied to it; since UP3 the witness is refused for the missing call-site conjunct before the pc premise is reached)
for spec in "EmptyBinder 'binder of type'" "PcPremise 'call-site state'"; do
  eval set -- $spec; f=$1; pat=$2
  all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/$f.lean "$W/NewPair" --theorem $P.correctness --theorem $P.Witness.nonvacuous 2>&1)"
  echo " ($f: a main theorem that is vacuous by an empty binder / unsatisfiable pc premise; its genuine witness must not verify)"
  row correctness blocked 'Stage: non-vacuity'   # round 15: no witness verified for it either
  row Witness.nonvacuous blocked 'round 14, W2' "$pat"
done
all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/V2Attacks.lean "$W/NewPair" --theorem $P.pinpre1 --theorem $P.exc1 \
  --theorem $P.W1.Witness.returns --theorem $P.W2.Witness.returns 2>&1)"
row pinpre1 blocked 'rt-auditv2' 'other than as'
row exc1 blocked 'round 10 V1' 'not a variable of the statement'
row W1.Witness.returns blocked 'round 14, W2'
row W2.Witness.returns blocked 'round 14, W2'
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round 14: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round 14: all rows as expected"

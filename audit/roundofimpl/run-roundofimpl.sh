#!/usr/bin/env bash
# Round-15 regression rows (docs/AUDIT.md, docs/SOUNDNESS.md "Round 15"): internal calls. A runtime contract may be
# assumed about `Extracted.program.ofImpl impl` (the runtime's own code, no user code), and the one premise on `impl`
# the auditor allows is exactly `ImplApart Extracted.program impl` ("the runtime's code does not overlap the
# extracted function's code"). Controls verify; every attack (a concrete implementation, `impl` mentioned outside
# link/ofImpl, a constraining premise, another program, another predicate, a combined premise, `ofImpl` as the
# statement's program, the predicate in the conclusion) is rejected. arm64 (`OfImplAttacks.lean`) and amd64
# (`OfImplAttacksAmd64.lean`).
# Exits 1 if an attack verifies or a control stops verifying. Uses --fresh and a private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/roundofimpl
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
  { [ -f artifacts/examples-amd64 ] && [ -d artifacts/amd64/HexDigit ]; } || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundofimpl.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh NewPair)
"$J" extract artifacts/examples-arm64 "$(example_symbol NewPair)" "$W/NewPair" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
"$J" extract artifacts/examples-amd64 "$(example_symbol NewPair)" "$W/NewPair64" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
broken=()
P=Proof
blk() { awk -v n="=== $P.$1:" 'index($0,n)==1{p=1;print;next} /^=== /{p=0} p' <<<"$all"; }
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
  printf '  %-34s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
run() { # file dir thms...
  local f=$1 d=$2; shift 2
  local targs=(); for t in "$@"; do targs+=(--theorem "$P.$t"); done
  all="$("$J" verify --fresh --janus-root "$root" --proof $R/attacks/$f "$W/$d" "${targs[@]}" 2>&1)"
}
echo "== arm64: controls (a contract over ofImpl; with ImplApart; mixed link/ofImpl)"
run OfImplAttacks.lean NewPair ctl1 ctl2 ctl3 ctl4 ctl5 ctl6 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 Shadow.r12 r13 r14 r15 r16 r17 r18 r19 r20 r21
row ctl1 Verified 'Role: main theorem'
row ctl2 Verified 'Role: main theorem'
row ctl3 Verified 'Role: main theorem'
row ctl4 Verified 'Role: main theorem'
row ctl5 Verified 'Role: main theorem'
row ctl6 Verified 'Role: main theorem'
echo "== arm64: attacks"
row r1 blocked 'ofImpl impl'
row r2 blocked 'other than as'
row r3 blocked 'round 15'
row r4 blocked 'ofImpl impl'
row r5 blocked 'round 15'
row r6 blocked 'other than as'
row r7 blocked 'round 14'
row r8 blocked 'other than as'
row r9 blocked 'other than as'
row r10 blocked 'other than as'
row r11 blocked 'round 14'
for r in Shadow.r12 r13 r14 r15 r16 r17 r18 r19 r20 r21; do row $r blocked; done
echo "== amd64"
run OfImplAttacksAmd64.lean NewPair64 ctl1 ctl2 r1 r5 r6 r8 r9
row ctl1 Verified 'Role: main theorem'
row ctl2 Verified 'Role: main theorem'
row r1 blocked 'ofImpl impl'
row r5 blocked 'round 15'
row r6 blocked 'other than as'
row r8 blocked 'other than as'
row r9 blocked 'other than as'
echo "== Witness side: the placement premise is a hypothesis of the main theorem, so the witness must exhibit it"
run OfImplWitness.lean NewPair correctness Witness.nonvacuous Witness.returns NoApart.Witness.nonvacuous
row correctness Verified 'Role: main theorem'
row Witness.nonvacuous Verified 'Role: WITNESS' 'main theorem Proof.correctness'
row Witness.returns Verified 'Role: WITNESS' 'main theorem Proof.correctness'
row NoApart.Witness.nonvacuous blocked 'round 14, W2' 'ImplApart'
run OfImplWitnessAmd64.lean NewPair64 correctness Witness.nonvacuous Witness.returns NoApart.Witness.nonvacuous
row correctness Verified 'Role: main theorem'
row Witness.nonvacuous Verified 'Role: WITNESS' 'main theorem Proof.correctness'
row Witness.returns Verified 'Role: WITNESS' 'main theorem Proof.correctness'
row NoApart.Witness.nonvacuous blocked 'round 14, W2' 'ImplApart'
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round 15 (ofImpl): BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round 15 (ofImpl): all rows as expected"

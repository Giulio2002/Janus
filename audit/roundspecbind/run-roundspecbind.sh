#!/usr/bin/env bash
# Spec binding (docs/SOUNDNESS.md "Spec binding"). The spec (and live data) of a runtime-contract
# hypothesis must describe the runtime function the contract is stated at (`contractAddr "runtime.f"`), a live
# contract's spec and live data must belong together, and the contract must be about the implementation the
# statement runs. Rows from round 15b (OfImplMore.lean: q1-q4, p1, s15) and SpecBind.lean / SpecBind64.lean.
# Controls verify (their report names the spec: `RtContract@runtime.growslice[growsliceSpec]`); every attack is rejected
# with the reason checked. Exits 1 if a row differs. Private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/roundspecbind
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
  { [ -f artifacts/examples-amd64 ] && [ -d artifacts/amd64/HexDigit ]; } || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundspecbind.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh NewPair)
"$J" extract artifacts/examples-arm64 "$(example_symbol NewPair)" "$W/NewPair" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
mapfile -t tg < <(scripts/example-targets.sh AppendOne)
"$J" extract artifacts/examples-arm64 "$(example_symbol AppendOne)" "$W/AppendOne" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
mapfile -t tg < <(scripts/example-targets.sh AppendPoint)
"$J" extract artifacts/examples-amd64 "$(example_symbol AppendPoint)" "$W/AppendPoint64" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
mapfile -t tg < <(scripts/example-targets.sh FromBytes)
"$J" extract artifacts/examples-arm64 "$(example_symbol FromBytes)" "$W/FromBytes" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
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
  printf '  %-12s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
run() { # file art thm...
  local f=$1 art=$2; shift 2
  local targs=(); for t in "$@"; do targs+=(--theorem "$P.$t"); done
  all="$("$J" verify --allow-no-witness --janus-root "$root" --proof "$R/attacks/$f" "$W/$art" "${targs[@]}" 2>&1)"
  printf '%s\n' "$all" > "$W/$f.txt"
}
SPEC='which describes'
echo "== arm64: rows of round 15b (OfImplMore.lean)"
run OfImplMore.lean NewPair q1 q2 q3 q4 p1 s15
row q1 blocked 'with the spec `growsliceSpec`' "$SPEC runtime.growslice"
row q2 blocked 'with the spec `growsliceSpec`' "$SPEC runtime.growslice"
row q3 blocked 'with the spec `wbZeroSpec`' "$SPEC runtime.wbZero"
row q4 blocked 'with the spec `growsliceSpec`' "$SPEC runtime.growslice"
row p1 blocked 'about the runtime implementation `impl2`' 'but the statement runs `Extracted.program.link impl`'
row s15 blocked 'about the runtime implementation `impl2`' 'but the statement runs `Extracted.program.link impl`'
echo "== arm64: SpecBind.lean"
run SpecBind.lean AppendOne g1 g2 g3 g4 g5 g6 g7 n1 d1 i1
row g1 Verified 'RtContract@runtime.growslice[growsliceSpec]'
row g2 Verified 'RtLiveContract@runtime.growslice[growsliceSpec/growsliceLive]'
row g3 blocked 'with the spec `growsliceBufSpec`' "$SPEC runtime.growsliceBuf"
row g4 blocked 'with the spec `concatstringSpec 3`' "$SPEC runtime.concatstring3"
row g5 blocked 'live data `growsliceBufLive`, which belong to the spec `growsliceBufSpec`'
row g6 blocked 'with the spec `growsliceBufSpec`' "$SPEC runtime.growsliceBuf"
row g7 Verified 'RtLiveContract@runtime.growslice[growsliceSpec/growsliceLive]'   # a proof-local alias of the allowed constant is expanded: the statement is the one with growsliceLive
row n1 blocked 'the contract of `runtime.newobject`, at the address of `runtime.growslice`'
row d1 blocked 'which is not Extracted.program; object names are looked up in the extracted program only'
row i1 blocked 'about the runtime implementation `impl2`'
echo "== arm64: SbtsAddr.lean (the address of runtime.staticuint64s in slicebytetostringSpec, U-SBTS-POST)"
run SbtsAddr.lean FromBytes c1 a1 a2 a3 a4
NOTSPEC='which is not one of the framework'"'"'s named runtime-function specs'
row c1 Verified 'RtContract@runtime.slicebytetostring[slicebytetostringSpec]'
row a1 blocked "$NOTSPEC" 'slicebytetostringSpec 4096'
row a2 blocked "$NOTSPEC" 'slicebytetostringSpec st'
row a3 blocked "$NOTSPEC"
row a4 blocked "$NOTSPEC"
echo "== amd64: SpecBind64.lean"
run SpecBind64.lean AppendPoint64 h1 h2 h3 h4
row h1 Verified 'RtContract64@runtime.growslice[growsliceSpec]'
row h2 blocked 'with the spec `growsliceBufSpec`' "$SPEC runtime.growsliceBuf"
row h3 blocked 'the contract of `runtime.newobject`, at the address of `runtime.growslice`'
row h4 blocked 'about the runtime implementation `impl2`'
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round specbind: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round specbind: all rows as expected"

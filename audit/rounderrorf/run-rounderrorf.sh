#!/usr/bin/env bash
# fmt.Errorf runtime contract (U-ERRORF). The type and itab parameters of `ErrorfLive` (tErr, iErr, tInt, iWrap) must
# be the extraction's own `Extracted.dataAddr` constants of the real symbols (`janus extract --contract fmt.errorf`
# emits and checks them), and the contract must be stated at the address of `fmt.errorf`. The control verifies; every
# attack is rejected with the reason checked. Exits 1 if a row differs. Private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/rounderrorf
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
  [ -f artifacts/examples-amd64 ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-rounderrorf.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh ErrWrap)
"$J" extract artifacts/examples-arm64 "$(example_symbol ErrWrap)" "$W/ErrWrap" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
"$J" extract artifacts/examples-amd64 "$(example_symbol ErrWrap)" "$W/ErrWrap64" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
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
NOTDATA='where it takes `Extracted.dataAddr.'
for isa in "" 64; do
  echo "== ${isa:-arm64}${isa:+ (amd64)}: ErrorfData$isa.lean"
  run ErrorfData$isa.lean ErrWrap$isa c1 a1 a2 a3 a4 a5 a6 a7 a8
  row c1 Verified 'ErrorfLive'
  row a1 blocked "$NOTDATA«type:*errors.errorString»"
  row a2 blocked "$NOTDATA«go:itab.*errors.errorString,error»"
  row a3 blocked "$NOTDATA«type:int»"
  row a4 blocked "$NOTDATA«go:itab.*fmt.wrapError,error»"
  row a5 blocked "$NOTDATA«go:itab.*errors.errorString,error»"
  row a6 blocked "$NOTDATA«type:*errors.errorString»"
  row a7 blocked 'but the extracted program has no data object of that name'
  row a8 blocked 'runtime.newobject'
done
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round errorf: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round errorf: all rows as expected"

#!/usr/bin/env bash
# Framework-package rows (N4 mutual recursion, N6 writable globals, N7 pinned allocation, slice and
# write-barrier contracts). Exits 1 if a tampered runtime function is accepted as a contract, a
# statement naming a global the extraction does not record verifies, or a control stops working.
# Every janus verification uses --fresh and a private temporary cache. Writes only under
# audit/roundfw/work/ and a mktemp directory (removed at the end).
# Usage: audit/roundfw/run-roundfw.sh [-j N]
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
par_init "$@"
J="$root/audit/roundfw/work/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1; fi
export JANUS_AUDIT_BIN="$J"
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
[ -f artifacts/examples-amd64 ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
W=audit/roundfw/work/rows; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundfw.XXXXXX")" || exit 1   # 0700: the cache's parent
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
broken=()
A=audit/roundfw/attacks

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
  printf '  %-44s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== N7: allocation, slice and write-barrier contracts are pinned to the runtime's code"
# pin ARCH FUNCTION ENTRY [EXTRA --contract ...]: the untampered binary extracts with FUNCTION a
# pinned contract; a copy whose FUNCTION has one changed byte is rejected at extraction.
pin() {
  local arch=$1 fn=$2 entry=$3 bin="artifacts/examples-$1" d="$W/$1-$2"
  shift 3
  out="$("$J" extract "$bin" "$entry" "$d/ok" --contract "runtime.$fn" "$@" 2>&1)" || true
  if grep -q '^Extracted' <<<"$out" && grep -A3 "\"name\": \"runtime.$fn\"" "$d/ok/identity.json" | grep -q '"pinned": true'; then
    printf '  %-44s %-8s %s\n' "P_${arch}_${fn}_control" pinned "contract runtime.$fn recorded as pinned"
  else
    printf '  %-44s %-8s %s   <-- BROKEN\n' "P_${arch}_${fn}_control" pinned "$(head -2 <<<"$out" | tr '\n' ' ' | cut -c1-120)"
    broken+=("P_${arch}_${fn}_control")
  fi
  audit/roundfw/tamper.sh "$bin" "$T/$arch-$fn.bin" "runtime.$fn" || { broken+=("P_${arch}_${fn}_tamper"); return 0; }
  out="$("$J" extract "$T/$arch-$fn.bin" "$entry" "$d/tampered" --contract "runtime.$fn" "$@" 2>&1)" || true
  row "P_${arch}_${fn}_tampered" blocked "is not the code of the runtime's runtime.$fn" "--contract names runtime.$fn"
}
for arch in arm64 amd64; do
  pin $arch newobject example.com/basic.NewPair
  pin $arch makeslice example.com/basic.MakeSlice
  pin $arch growslice example.com/basic.AppendOne
  pin $arch mallocgc runtime.newobject
  pin $arch gcWriteBarrier2 example.com/basic.SetNext --contract runtime.wbBufFlush
done

echo "== N6: a statement names only globals the extraction records (janus-audit)"
mapfile -t tg < <(scripts/example-targets.sh MulAlgo)
"$J" extract artifacts/examples-arm64 example.com/basic.MulAlgo "$W/MulAlgo" "${tg[@]}" >/dev/null 2>&1 || exit 1
par_run 'v $A/G1_misspelt_global.lean $W/MulAlgo;  row G1_misspelt_global blocked "but the extracted program has no writable global"'
par_run 'v $A/G2_lookalike_global.lean $W/MulAlgo; row G2_lookalike_global blocked "no writable global"'
par_run 'v $A/G3_other_global_list.lean $W/MulAlgo; row G3_other_global_list blocked "which is not Extracted.program.globals"'
par_run 'echo "   controls"; v examples/proofs/MulAlgo.lean $W/MulAlgo Proof.correctness; row G_ctl_MulAlgo_GlobalsInit Verified "GlobalsInit"'
par_run 'v examples/proofs/MulAlgo.lean $W/MulAlgo Proof.Witness.nonvacuous; row G_ctl_MulAlgo_witness Verified'
par_wait

echo "== N4: mutual recursion (controls: both components verify with their witnesses)"
for f in IsEven CycA; do
  "$J" extract artifacts/examples-arm64 "example.com/basic.$f" "$W/$f" >/dev/null 2>&1 || exit 1
done
par_run 'v examples/proofs/IsEven.lean $W/IsEven Proof.correctness; row M_ctl_IsEven Verified "IsOdd"'
par_run 'v examples/proofs/CycA.lean $W/CycA Proof.correctness; row M_ctl_CycA_3cycle Verified "CycC"'
par_wait

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All framework-package rows as expected."

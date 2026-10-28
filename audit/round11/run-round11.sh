#!/usr/bin/env bash
# Round-11 regression rows (docs/AUDIT.md, docs/SOUNDNESS.md "Round 11"): the round-10 V1 rule
# (a runtime-contract hypothesis must quantify the runtime) now covers EVERY non-program,
# non-numeric contract argument, not only RtReady/IfaceModel/MapModel/List (Nat x Nat). Exits 1
# if a blocked attack verifies, a control stops verifying, or a kernel-checked model row changes
# verdict. Every janus verification uses --fresh and a private temporary cache. Writes only under
# audit/round11/work/, audit/round11/bin/ and a mktemp directory (removed at the end).
# Usage: audit/round11/run-round11.sh
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/round11
J="$root/$R/bin/janus"; mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=$R/work/rows; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round11.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
# extract NAME: the example NAME, with the symbol and contracts its own proof uses
extract() {
  mapfile -t tg < <(scripts/example-targets.sh "$1")
  "$J" extract artifacts/examples-arm64 "$(example_symbol "$1")" "$W/$1" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
}
for f in DeferTwice AlgMemhash16 RecoverSet Concat HashFKey; do extract "$f"; done
# K1: the checkptr example (examples/rtmisc), whose binary has its own build
[ -f artifacts/examples-rtmisc-arm64 ] || scripts/build-examples-rtmisc.sh >/dev/null
"$J" extract artifacts/examples-rtmisc-arm64 example.com/rtmisc/checkptr.Word "$W/CheckWord" --contract runtime.checkptrAlignment >/dev/null 2>&1 || exit 1
broken=()
A=$R/attacks

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
check() {
  if [ "$2" = 0 ]; then printf '  %-40s ok       %s\n' "$1" "$3"
  else printf '  %-40s FAILED   %s   <-- BROKEN\n' "$1" "$3"; broken+=("$1"); fi
}
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== L1: a closed runtime model in a contract hypothesis (any model type, not a whitelist)"
v $A/H1a_closed_HashModel.lean "$W/AlgMemhash16";  row H1a_hash_model_closed blocked 'round 11' 'Memhash'
v $A/H1b_hash_model_pinned_by_premise.lean "$W/AlgMemhash16"; row H1b_hash_model_pinned_by_eq blocked 'round 11' 'constrains a runtime variable'
v $A/P1a_closed_PanicRuntime.lean "$W/RecoverSet"; row P1a_panic_runtime_closed blocked 'round 11' 'GorecoverContract'
v $A/K1a_checkptr_model_pinned_by_premise.lean "$W/CheckWord"; row K1a_checkptr_model_pinned_by_premise blocked 'round 11' 'constrains a runtime variable'
v examples/proofs/AlgMemhash16.lean "$W/AlgMemhash16"; row L1_ctl_AlgMemhash16_HashModel_var Verified 'HashModel'
v examples/proofs/DeferTwice.lean "$W/DeferTwice"; row L1_ctl_DeferTwice_PanicRuntime_var Verified 'PanicRuntime'
v examples/proofs/RecoverSet.lean "$W/RecoverSet"; row L1_ctl_RecoverSet_PanicRuntime_var Verified 'PanicRuntime'
v examples/rtmisc/proofs/arm64/CheckWord.lean "$W/CheckWord"; row L1_ctl_CheckWord_CheckptrModel_var Verified 'CheckptrModel'

echo "== A1: the allow-list (RtSpec / Fmt arguments) is a NAMED list of framework constants"
for a in A1a_proof_defined_spec:Concat A1b_inline_spec_lambda:Concat A1b2_structure_update_of_listed_spec:Concat \
         A1c_imported_default_fmt:HashFKey A1d2_abbrev_of_bad_spec:Concat; do
  f=${a%%:*}; d=${a##*:}
  v $A/$f.lean "$W/$d"; row "$f" blocked 'round 11' 'named'
done
v $A/A1d_abbrev_alias.lean "$W/Concat"; row A1d_ctl_alias_unfolding_to_listed_spec Verified
v examples/proofs/Concat.lean "$W/Concat"; row A1_ctl_Concat_concatstringSpec Verified 'concatstringSpec'
v examples/proofs/HashFKey.lean "$W/HashFKey"; row A1_ctl_HashFKey_binary64 Verified 'binary64'

echo "== L1 model rows: the closed-model contracts really hold of no program (kernel-checked)"
for m in H1a_unsat_closed_H P1a_unsat_closed_P; do
  o="$(lake env lean $R/model/$m.lean 2>&1)"; rc=$?; check "L1_model_$m" $rc "$(grep -m1 error <<<"$o")"
done

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-11 rows as expected."

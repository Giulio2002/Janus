#!/usr/bin/env bash
# Round-13 regression rows (docs/AUDIT.md, docs/SOUNDNESS.md "Round 13"): the round-10/11 V1 rule
# (a runtime-contract hypothesis must quantify the runtime and nothing else may constrain the
# runtime variables) now classifies EVERY binder of the theorem, of any sort. A non-Prop binder
# (PLift, ULift, Subtype, Sigma, structure, a proof-local `def … : Type`) whose type mentions a
# runtime variable of a contract hypothesis is rejected. Exits 1 if a blocked attack verifies or a
# control stops verifying. Every verification uses --fresh and a private temporary cache. Writes
# only under audit/round13/work/, audit/round13/bin/ and a mktemp directory (removed at the end).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/round13
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round13.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/example-contracts.sh
mapfile -t tg < <(scripts/example-targets.sh NewPair)
"$J" extract artifacts/examples-arm64 "$(example_symbol NewPair)" "$W/NewPair" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
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
v() { out="$("$J" verify --fresh --janus-root "$root" --proof "$1" "$2" ${3:+--theorem "$3"} 2>&1)"; }

echo "== B1: a non-Prop binder (any sort) mentioning a runtime variable is rejected BY THIS RULE"
for f in P1a_plift_pin_H P1b_subtype_pin_H P1c_ulift_pin_rt P1d_sigma_pin_H P6b_local_def_in_type_universe; do
  v $A/$f.lean "$W/NewPair"; row "$f" blocked 'round 13' 'non-Prop binder'
done
echo "== C: controls"
v examples/proofs/NewPair.lean "$W/NewPair"; row C0_ctl_NewPair Verified 'NewobjectContract'
v $A/C1_ctl_harmless_type_binder.lean "$W/NewPair"; row C1_ctl_type_binders_without_runtime_vars Verified 'NewobjectContract'

# F: the extraction's own constants (`Extracted.funcs`, the panic contracts' function table) are an
# allowed contract argument ONLY as exactly that constant, and `janus check` re-derives it from the
# binary. Needs the panic extraction (cmd/janus/funcdata.go, wave 2); skipped before that exists.
if [ -f cmd/janus/funcdata.go ]; then
  echo "== F1: Extracted.funcs is allowed only as exactly the generated constant"
  mapfile -t tg < <(scripts/example-targets.sh DeferOrder)
  "$J" extract artifacts/examples-arm64 "$(example_symbol DeferOrder)" "$W/DeferOrder" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || exit 1
  for f in F1a_funcs_empty F1b_funcs_proof_defined F1c_funcs_tail F1d_funcs_take F1e_funcs_let_alias F1f_funcs_append_nil F1g_funcs_abbrev_alias; do
    v $A/$f.lean "$W/DeferOrder"; row "$f" blocked 'runtime'
  done
  v $R/controls/C2_ctl_DeferOrder_funcs.lean "$W/DeferOrder"; row C2_ctl_DeferOrder_honest_panic Verified 'GopanicContract'
  # a tampered Extracted.lean with a fake funcs table: janus check (and verify) must reject it
  cp -r "$W/DeferOrder" "$W/DeferOrder-tampered"
  if grep -q '^def funcs' "$W/DeferOrder-tampered/Extracted.lean"; then
    sed -i '/^def funcs/,/^$/ s/\(entry := \|Entry := \)[0-9]*/\10/' "$W/DeferOrder-tampered/Extracted.lean"
    sed -i '/^def funcs/ s/:= \[.*/:= []/' "$W/DeferOrder-tampered/Extracted.lean"
  fi
  cmp -s "$W/DeferOrder/Extracted.lean" "$W/DeferOrder-tampered/Extracted.lean" && echo "  (tamper did not change the file)" && broken+=(F2_tamper_noop)
  out="$("$J" check "$W/DeferOrder-tampered" 2>&1)"; rc=$?
  [ $rc != 0 ]; check_row=$?
  if [ $check_row = 0 ]; then printf '  %-40s ok       janus check rejects the fake funcs table\n' F2_tampered_funcs_check
  else printf '  %-40s FAILED   check accepted a fake funcs table   <-- BROKEN\n' F2_tampered_funcs_check; broken+=(F2_tampered_funcs_check); fi
  v $R/controls/C2_ctl_DeferOrder_funcs.lean "$W/DeferOrder-tampered"; row F2_tampered_funcs_verify blocked
fi

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo "round13: all rows as expected"

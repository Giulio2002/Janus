#!/usr/bin/env bash
# Regression rows for the named data-symbol constants (docs/CLI.md "Named data symbols"):
# `Extracted.dataAddr.«SYM»` / `Extracted.dataSize.«SYM»` are generated from the binary's symbol table, are
# part of the regenerated-and-compared Extracted.lean, and are identity-checked by the auditor like
# `program` and `entry`. A statement may mention them; a proof module cannot declare one, and a statement
# that mentions only them says nothing about the code.
#   control   examples/proofs/SymPows.lean (a table read through the named constants) verifies
#   shadow    a proof module declaring Extracted.dataAddr.«other» is blocked (reserved namespace)
#   Eqn*      only a THEOREM `C.eq_<k>`/`C.eq_def` about a constant C of the Extracted module (what simp/unfold realize)
#             is exempt from the shadow rule; a def, an axiom, a theorem with another left side or another/unknown
#             prefix, a lookalike-letter namespace and a non-equation are all blocked (EqnDef … EqnNotEq). Lean itself
#             rejects a declaration named `C.eq_<k>` of an existing constant C ("reserved name"), so those rows
#             are blocked at compile time; EqnOtherConst and EqnLookalike reach the auditor's shadow rule.
#   nocode    a statement about the constants alone is blocked (mentions no Extracted.program/entry)
# Exits 1 if an attack verifies or the control stops verifying. Private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/roundds
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundds.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
"$J" extract artifacts/examples-arm64 example.com/basic.SymPows "$W/SymPows" >/dev/null 2>&1 || exit 1
grep -q 'def dataAddr.«example.com/basic.symPows»' "$W/SymPows/Extracted.lean" || { echo "no data constant generated"; exit 1; }
broken=()
v() { "$J" verify --fresh --janus-root "$root" "$@" 2>&1; }
row() { # NAME expect(blocked|Verified) OUTPUT pattern...
  local name=$1 expect=$2 out=$3 verdict status="" pat; shift 3
  verdict="$(grep -m1 -E '^=== |^Error|^Rejected|^Invalid|^Verified' <<<"$out" | cut -c1-120)"
  [ -n "$verdict" ] || { verdict="(no verdict)"; status=BROKEN; }
  case $expect in
    blocked) case $verdict in *verified*|*Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in *verified*|*Verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  printf '  %-12s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
echo "== named data constants"
row control Verified "$(v --proof examples/proofs/SymPows.lean "$W/SymPows" --theorem Proof.correctness)"
row shadow blocked "$(v --proof $R/attacks/SymShadow.lean "$W/SymPows" --theorem Proof.correctness)" 'shadows the Extracted namespace'
row nocode blocked "$(v --proof $R/attacks/SymNoCode.lean "$W/SymPows" --theorem Proof.noCode)" 'says nothing about the extracted code'
for a in EqnDef EqnAxiom EqnOtherLhs EqnOtherConst EqnLookalike EqnNotEq; do
  row "$a" blocked "$(v --proof $R/attacks/$a.lean "$W/SymPows" --theorem Proof.correctness)"
done
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round ds: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round ds: all rows as expected"

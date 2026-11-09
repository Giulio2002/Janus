#!/usr/bin/env bash
# audit/icall/attacks.sh JANUS_BIN EXTRACTED_ADD_DIR EXAMPLE_BINARY [JANUS_ROOT]
# Runs the U-ICALL allowance rows (audit/icall/attacks/*.lean) with `janus verify` against an extraction of
# example.com/basic.Add: C0 (control) must verify, every A row marked "rejected" must be rejected by the audit,
# A8 must verify (P is an obligation only).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
J="${1:?janus binary}"; EX="${2:?extracted Add dir}"; BIN="${3:?example binary}"; JR="${4:-$root}"
. "$root/audit/lib/blocked.sh"
bad=0
for f in "$root"/audit/icall/attacks/*.lean; do
  n="$(basename "$f" .lean)"
  want="$(grep -o 'Expected: [A-Za-z ()]*' "$f" | head -1 | sed 's/Expected: //')"
  out="$("$J" verify "$EX" --proof "$f" --theorem Proof.correctness --janus-root "$JR" --binary "$BIN" --audit-only --no-result-cache 2>&1 | sed -E 's/^Audit-only: /Verified: /; s/^(=== .*): audit-only \(NOT verified\) ===\$/\1: verified ===/')"
  if printf '%s' "$out" | grep -q '^Verified:'; then got=Verified; else got=rejected; fi
  case "$want" in Verified*) w=Verified ;; *) w=rejected ;; esac
  if [ "$got" = "$w" ]; then echo "ROW ok   $n: $got"; else echo "ROW BAD  $n: wanted $w, got $got"; printf '%s\n' "$out" | tail -4; bad=1; fi
  [ "$w" = rejected ] && [ "$got" = rejected ] && printf '%s' "$out" | grep -m1 -i 'audit rejected\|Invalid' | cut -c1-240
  if [ "$w" = rejected ] && [ "$got" = rejected ]; then why="$(blocked_check icall/attacks.sh "$n" "$out")"; [ -n "$why" ] && { echo "ROW BAD  $n: $why"; bad=1; }; fi
done
exit $bad

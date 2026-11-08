#!/usr/bin/env bash
# Red-team round n9, U-ICALL: run the rows against a checkout that has the U-ICALL auditor allowances.
#   run-icall.sh JANUS_BIN JANUS_ROOT ADD_ARTIFACT ERRWRAP_ARTIFACT
# Rows B1-B12 are statements about `Add`, C1/B13-B17 about `ErrWrap` (which lists the stubs fmt.errorf, runtime.newobject).
# "Expected:" in each file is rejected or Verified. An ACCEPTED row that was expected to be rejected is a finding.
set -u
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
J="${1:?janus binary}"; JR="${2:?janus root}"; ADD="${3:?Add artifact}"; EW="${4:?ErrWrap artifact}"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT; mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
bad=0
for f in "$here"/*.lean; do
  n="$(basename "$f" .lean)"
  want="$(grep -o 'Expected: [A-Za-z]*' "$f" | head -1 | sed 's/Expected: //')"
  case "$n" in C1_*|B13_*|B14_*|B15_*|B16_*|B17_*) art="$EW" ;; *) art="$ADD" ;; esac
  out="$("$J" verify "$art" --proof "$f" --theorem Proof.correctness --janus-root "$JR" --audit-only --no-result-cache 2>&1 | sed -E 's/^Audit-only: /Verified: /; s/^(=== .*): audit-only \(NOT verified\) ===\$/\1: verified ===/')"
  if printf '%s' "$out" | grep -q '^Verified:'; then got=Verified; else got=rejected; fi
  if [ "$got" = "$want" ]; then s="ok"; else s="DIFFERS (wanted $want)"; bad=1; fi
  printf '%-28s %-9s %s\n' "$n" "$got" "$s"
  [ "$got" = rejected ] && printf '%s\n' "$out" | grep -m1 -iE 'audit rejected|Invalid|Lean errors' | cut -c1-200 | sed 's/^/    /'
done
exit $bad

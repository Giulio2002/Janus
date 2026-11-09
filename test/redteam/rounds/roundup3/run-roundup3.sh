#!/usr/bin/env bash
# Round UP3 (red team n11, vacuity attacks on the size arguments of a runtime contract; docs/SOUNDNESS.md "UP3").
# Rows (test/redteam/rounds/roundup3/rows/*.lean, each states "Expected: rejected|Verified" for the STATEMENT AUDIT) are statements about
# `Add` whose proof never uses the hypotheses, so only the auditor decides:
#   * with --audit-only (the proof and the statement audit; not a verification) a row is "rejected" or "Verified" (= the audit
#     accepted it: janus prints `Audit-only:`) exactly as its file says;
#   * with --allow-no-witness (inert) EVERY row is rejected, controls included: each row's theorem assumes a runtime contract
#     and none has a verified Witness.nonvacuous, so no flag verifies it.
# Exits 1 if a row differs.   Usage: test/redteam/rounds/roundup3/run-roundup3.sh   (or: JANUS_AUDIT_BIN=... JANUS_AUDIT_PREBUILT=1 from run-rounds.sh)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=test/redteam/rounds/roundup3
. "$root/test/redteam/lib/blocked.sh"
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build/build-examples.sh >/dev/null
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundup3.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
. scripts/verify/example-contracts.sh
mapfile -t tg < <(scripts/verify/example-targets.sh Add)
"$J" extract artifacts/examples-arm64 "$(example_symbol Add)" "$W/Add" ${tg[@]+"${tg[@]}"} >/dev/null 2>&1 || { echo "extract Add failed"; exit 1; }
bad=0
for f in "$R"/rows/*.lean; do
  n="$(basename "$f" .lean)"; want="$(grep -o 'Expected: [A-Za-z]*' "$f" | head -1 | sed 's/Expected: //')"
  out="$("$J" verify "$W/Add" --proof "$f" --theorem Proof.correctness --janus-root "$root" --audit-only --no-result-cache 2>&1)"
  if printf '%s' "$out" | grep -q '^Audit-only:'; then got=Verified
  elif printf '%s' "$out" | grep -q '^Verified:'; then got="FALSE-VERIFIED"
  else got=rejected; fi
  if [ "$got" = "$want" ]; then s=ok; else s="DIFFERS (wanted $want)"; bad=1; fi
  # rejected rows: the pinned reason of the audit (test/redteam/lib/blocked-pins.tsv), never an elaboration failure of the row file
  if [ "$got" = rejected ] && [ "$want" = rejected ]; then why="$(blocked_check rounds/roundup3/run-roundup3.sh "$n" "$out")"; [ -n "$why" ] && { s="$s BROKEN: $why"; bad=1; }; fi
  printf '%-34s audit-only %-9s %s\n' "$n" "$got" "$s"
  [ "$got" = rejected ] && printf '%s\n' "$out" | grep -m1 -iE 'audit rejected|Lean errors|Invalid|error' | cut -c1-240 | sed 's/^/    /'
  # --allow-no-witness: inert, nothing here has a witness: never Verified
  out="$("$J" verify "$W/Add" --proof "$f" --theorem Proof.correctness --janus-root "$root" --allow-no-witness --no-result-cache 2>&1)"
  if printf '%s' "$out" | grep -q '^Verified:'; then printf '%-34s allow-no-witness VERIFIED   <-- BROKEN\n' "$n"; bad=1
  else
    why="$(blocked_check rounds/roundup3/run-roundup3.sh "$n/allow-no-witness" "$out")"
    if [ -n "$why" ]; then printf '%-34s allow-no-witness rejected for the WRONG reason   <-- BROKEN: %s\n' "$n" "$why"; bad=1
    else printf '%-34s allow-no-witness rejected ok\n' "$n"; fi
  fi
done
# witness rows (WIT*): the main theorem passes the statement audit (no size is pinned), but the witness instantiates a contract at sizes
# where its call precondition is unsatisfiable (vacuously inhabited by `exfalso`): the witness must be rejected, so the main theorem
# gets no "shown" and is rejected too, under every flag.
for f in "$R"/wit/*.lean; do
  n="$(basename "$f" .lean)"
  for fl in "" "--allow-no-witness"; do
    out="$("$J" verify "$W/Add" --proof "$f" --theorem Proof.correctness --theorem Proof.Witness.nonvacuous --janus-root "$root" $fl --no-result-cache 2>&1)"
    if printf '%s' "$out" | grep -q '^=== Proof.correctness: verified' || printf '%s' "$out" | grep -q '^=== Proof.Witness.nonvacuous: verified'; then
      printf '%-34s %-20s ACCEPTED   <-- BROKEN\n' "$n" "${fl:-no-flag}"; bad=1
    elif printf '%s' "$out" | grep -qE 'instantiates the runtime contract|U-ICALL-INHABITED'; then printf '%-34s %-20s rejected ok (witness sizes)\n' "$n" "${fl:-no-flag}"
    else printf '%-34s %-20s rejected for ANOTHER reason   <-- BROKEN\n' "$n" "${fl:-no-flag}"; printf '%s\n' "$out" | head -8 | cut -c1-240 | sed 's/^/    /'; bad=1; fi
  done
done
[ $bad = 0 ] && echo "round up3: all rows as expected" || echo "round up3: BROKEN rows"
exit $bad

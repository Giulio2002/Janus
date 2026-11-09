#!/usr/bin/env bash
# Shared "blocked" row check for the audit round scripts.
#
# A row that expects `blocked` used to pass on ANY non-Verified verdict, including "Lean rejected the proof" (the attack
# file no longer compiles) or a rejection by an unrelated check, so a broken attack file silently kept passing. Now:
#   * every blocked row has PINS in audit/lib/blocked-pins.tsv: lines  SCRIPT<TAB>ROW<TAB>SUBSTRING  (several lines per
#     row: ALL substrings must occur, as fixed strings, in the row's output). The substring is a stable part of the exact
#     rejection reason of the check the attack targets (never a bare "Invalid"). A blocked row without a pin is BROKEN.
#   * "Lean rejected the proof" / "Lean rejected the extracted program" (an elaboration / compile failure of the proof file,
#     a consumer module or the extraction) is BROKEN for every blocked row unless one of its pins itself contains the text
#     "Lean rejected the" (the row then explicitly expects the compilation to stop, and its other pins name the Lean error).
#   * a pin may list alternatives separated by " ||| " (any one must occur): only for rows whose outcome is a race by design
#     (round 10 G2: a verification whose run trees are deleted under it fails closed, with whatever error it hits first).
#   * BLOCKED_SURVEY=FILE: append SCRIPT, ROW and the reason lines of every blocked row to FILE (used to write the pins).
# Usage (in a script's row()):   why=$(blocked_check SCRIPT NAME "$out");  [ -n "$why" ] && status=BROKEN
BLOCKED_PINS="${BLOCKED_PINS:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/blocked-pins.tsv}"
blocked_check() {
  local script=$1 name=$2 out=$3 p explicit=0 npins=0 why=""
  if [ -n "${BLOCKED_SURVEY:-}" ]; then
    { printf '%s\t%s\t' "$script" "$name"; grep -m1 -E '^(Invalid|Error|Verified):|^=== |^FAIL|^Rejected|^rejected|^accepted|^NOVERDICT|^AMBIGUOUS' <<<"$out" | head -1 | tr '\t\n' '  '
      printf ' || '; grep -v -E '^(janus: memory guard|janus-memguard:)' <<<"$out" | grep -E 'Stage:|error|Error|rejected|not |must|may ' | head -8 | cut -c1-240 | tr '\t\n' '  '; printf '\n'; } >> "$BLOCKED_SURVEY" 2>/dev/null
  fi
  while IFS=$'\t' read -r s r p; do
    [ "$s" = "$script" ] && [ "$r" = "$name" ] || continue
    npins=$((npins + 1))
    if [[ "$p" == *" ||| "* ]]; then
      local alt hit=0 rest=$p
      while [ -n "$rest" ]; do
        if [[ "$rest" == *" ||| "* ]]; then alt=${rest%% ||| *}; rest=${rest#* ||| }; else alt=$rest; rest=""; fi
        grep -qF -- "$alt" <<<"$out" && hit=1
      done
      [ "$hit" = 1 ] || why="$why none of the alternative pins occurs: '$p';"
    else
      grep -qF -- "$p" <<<"$out" || why="$why pin missing: '$p';"
    fi
    case $p in *"Lean rejected the"*) explicit=1 ;; esac
  done < "$BLOCKED_PINS"
  [ "$npins" -gt 0 ] || why="no pin for this blocked row in audit/lib/blocked-pins.tsv;"
  if [ "$explicit" = 0 ] && grep -qE "Lean rejected the (proof|extracted program)" <<<"$out"; then
    why="$why Lean rejected the proof/extraction (elaboration/compile failure), not the check this row targets;"
  fi
  printf '%s' "$why"
}

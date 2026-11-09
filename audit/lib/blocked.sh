#!/usr/bin/env bash
# Shared "blocked" row check for the audit round scripts.
#
# A row that expects `blocked` used to pass on ANY non-Verified verdict, including "Lean rejected the proof" (the attack
# file no longer compiles) or a rejection by an unrelated check, so a broken attack file silently kept passing. Now:
#   * every blocked row has PINS in audit/lib/blocked-pins.tsv: lines  SCRIPT<TAB>ROW<TAB>SUBSTRING  (several lines per
#     row: ALL substrings must occur, as fixed strings, in the row's output). The substring is a stable part of the exact
#     rejection reason of the check the attack targets (never a bare "Invalid"). A blocked row without a pin is BROKEN.
#   * "Lean rejected the proof" (an elaboration / compile failure of the proof file or consumer module) is BROKEN for every
#     blocked row unless one of its pins itself contains the text "Lean rejected the proof" (the row then explicitly
#     expects the proof to be stopped at compilation, and its other pins name the Lean error).
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
    grep -qF -- "$p" <<<"$out" || why="$why pin missing: '$p';"
    case $p in *"Lean rejected the proof"*) explicit=1 ;; esac
  done < "$BLOCKED_PINS"
  [ "$npins" -gt 0 ] || why="no pin for this blocked row in audit/lib/blocked-pins.tsv;"
  if [ "$explicit" = 0 ] && grep -qF -- "Lean rejected the proof" <<<"$out"; then
    why="$why the proof was rejected by Lean (elaboration/compile failure), not by the check this row targets;"
  fi
  printf '%s' "$why"
}

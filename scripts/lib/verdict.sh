#!/usr/bin/env bash
# Verdict selection for row scripts. A janus / `lake env lean` run may print banner lines on stderr
# before (JANUS_MEMGUARD_LOG, JANUS_MEMGUARD_VERBOSE) or after (no memory guard available) the
# verdict, so a verdict is selected by its pattern, never by its position.
#   verdict_line : stdin -> the first Verified:/Invalid:/Error: line; "NOVERDICT (...)" if there is none
#                  (rows treat NOVERDICT as BROKEN).
#   lean_first   : stdin -> the first line that is not a memory-guard banner.
verdict_line() { local l; l="$(grep -m1 -E '^(Verified|Invalid|Error)')" || true; printf '%s\n' "${l:-NOVERDICT (no Verified/Invalid/Error line)}"; }
lean_first() { grep -v -E '^(janus: memory guard|janus-memguard|memguard)' | head -1; }

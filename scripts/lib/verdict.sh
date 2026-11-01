#!/usr/bin/env bash
# Verdict selection for row scripts. A janus / `lake env lean` run may print banner lines on stderr
# before (JANUS_MEMGUARD_LOG, JANUS_MEMGUARD_VERBOSE) or after (no memory guard available) the
# verdict, so a verdict is selected by its pattern, never by its position.
#   verdict_line : stdin -> the first "Verified: " / "Invalid: " / "Error: " line (janus's exact vocabulary: printDiag and
#                  printVerified in cmd/janus, a colon and a space, at the start of the line); the WHOLE stream is read
#                  (no SIGPIPE to the producer).
#                  "NOVERDICT (...)"  if there is no such line;
#                  "AMBIGUOUS (...)"  if a Verified line coexists with an Invalid/Error line (a diagnostic that echoes
#                                     text, or a verdict hidden behind an earlier line): a row can then trust neither.
#                  Rows treat NOVERDICT and AMBIGUOUS as BROKEN for every expectation (audit/run-all.sh row()).
#   lean_first   : stdin -> the first line that is not a memory-guard banner.
verdict_line() {
  local out; out="$(awk '
    /^(Verified|Invalid|Error): / { if (first == "") first = $0; if ($0 ~ /^Verified: /) v = 1; else f = 1 }
    END { if (first == "") print "NOVERDICT (no Verified:/Invalid:/Error: line)";
          else if (v && f) print "AMBIGUOUS (Verified: and Invalid:/Error: lines both present; first: " substr(first, 1, 80) ")";
          else print first }')"
  printf '%s\n' "$out"
}
lean_first() { grep -v -E '^(janus: memory guard|janus-memguard:|memguard[:[])' | head -1; }

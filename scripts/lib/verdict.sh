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

# verdict_reason : stdin -> verdict_line, plus " [Stage: S]" (the first "Stage:" line of the stream) and, when Lean rejected a file, " [Lean: E ; G]"
# (E = the first Lean error message without its file:line:col prefix, G = the first goal line `⊢ …` after it, if any). The reason a
# row's `blocked` pin (audit/lib/blocked.sh, audit/lib/blocked-pins.tsv) is matched against when the row only carries a verdict line.
verdict_reason() {
  local all; all="$(cat)"
  local v; v="$(verdict_line <<<"$all")"
  local st; st="$(grep -m1 -E '^ *Stage: ' <<<"$all" | sed -E 's/^ *Stage: //')"
  local le; le="$(awk '
    /^ +[^ ]+:[0-9]+:[0-9]+: error: / && !e { e = $0; sub(/^ +[^ ]+:[0-9]+:[0-9]+: error: /, "", e); next }
    e && /⊢/ && !g { g = $0; sub(/^ +/, "", g); print e " ; " g; done = 1; exit }
    END { if (!done && e) print e }' <<<"$all")"
  # a failed Lake job (a consumer package's lakefile script or build step): "✖ [327/328] Running Janus.Backdoor" -> "Running Janus.Backdoor"
  local lk; lk="$(grep -m1 -E '^✖ \[[0-9]+/[0-9]+\] ' <<<"$all" | sed -E 's/^✖ \[[0-9]+\/[0-9]+\] //')"
  local lke; lke="$(grep -m1 -E '^error: ' <<<"$all" | sed -E 's/^error: //')"
  # the kernel replay's finding (leanchecker): "(kernel) declaration type mismatch, 'Proof.correctness' ..." / "while replaying declaration 'X'"
  local rp; rp="$({ grep -m1 -F '(kernel)' <<<"$all" || grep -m1 -F 'while replaying declaration' <<<"$all"; } | sed -E 's/^ +//' | cut -c1-200)"
  printf '%s%s%s%s%s\n' "$v" "${st:+ [Stage: $st]}" "${le:+ [Lean: $le]}" "${lk:+ [Lake: $lk${lke:+ ; $lke}]}" "${rp:+ [Replay: $rp]}"
}

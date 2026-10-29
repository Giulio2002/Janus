# shellcheck shell=bash
# tmark LABEL: with JANUS_TIMES_FILE set, append "<epoch>\t-\t<script>\tmark: LABEL" (see parallel.sh).
tmark() {
  [ -n "${JANUS_TIMES_FILE:-}" ] || return 0
  printf '%s\t-\t%s\tmark: %s\n' "$(date +%s.%N)" "$(basename "$0")" "$*" >> "$JANUS_TIMES_FILE"
  return 0
}

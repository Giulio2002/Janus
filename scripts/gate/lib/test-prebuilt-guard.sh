#!/usr/bin/env bash
# Guard: no audit round script (test/redteam/rounds/round*/run-*.sh) and no helper it sources runs `lake build` outside a
# JANUS_AUDIT_PREBUILT guard (same line, or inside an `if [ "${JANUS_AUDIT_PREBUILT..." ... fi` block / an
# `elif` branch of one). test/redteam/run-rounds.sh builds once and exports JANUS_AUDIT_PREBUILT=1; a lane that builds
# anyway rewrites .lake/build/lib/lean under the other lanes. Usage: test-prebuilt-guard.sh [ROOT]
root="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
fail=0
check() {
  awk -v F="$1" '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*echo / { next }
    /^[[:space:]]*elif .*JANUS_AUDIT_PREBUILT/ { elif = 1; next }
    /^[[:space:]]*if .*JANUS_AUDIT_PREBUILT/ { if (!depth) { guard = 1; depth = 1; next } }
    /^[[:space:]]*if / { if (guard) depth++; next }
    /^[[:space:]]*fi([[:space:];]|$)/ { if (guard) { depth--; if (depth == 0) guard = 0 }; next }
    /(^|[^[:alnum:]_-])(memguard_)?lake build/ {
      if (!guard && !elif && $0 !~ /JANUS_AUDIT_PREBUILT/) { printf "%s:%d: unguarded: %s\n", F, NR, $0; bad = 1 }
    }
    END { exit bad }
  ' "$1" || return 1
}
for f in "$root"/test/redteam/rounds/round*/run-*.sh "$root/scripts/lib/gate-decoder.sh"; do
  [ -f "$f" ] || continue
  check "$f" || fail=1
done
# the shared build of run-rounds.sh names every target a round builds
for t in janus-audit janus-oracle-amd64 janus-decode; do
  grep -q "memguard_lake build .*$t" "$root/test/redteam/run-rounds.sh" || { echo "test/redteam/run-rounds.sh's shared build lacks $t"; fail=1; }
done
# self-test of the checker: an unguarded build is caught
tmp="$(mktemp -d "${TMPDIR:-/tmp}/test-prebuilt-guard.XXXXXX")"; trap 'rm -rf "$tmp"' EXIT
printf '#!/bin/bash\nlake build Janus\n' > "$tmp/bad.sh"
printf '#!/bin/bash\n[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || lake build Janus\nif [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then\n  if x; then y; fi\n  lake build Janus\nfi\n' > "$tmp/good.sh"
check "$tmp/bad.sh" >/dev/null && { echo "self-test: an unguarded build was not caught"; fail=1; }
check "$tmp/good.sh" || { echo "self-test: guarded builds were flagged"; fail=1; }
[ "$fail" = 0 ] && echo "prebuilt-guard: ok" || exit 1

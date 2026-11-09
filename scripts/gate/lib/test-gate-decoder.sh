#!/usr/bin/env bash
# test/redteam/rounds/round10 must fail LOUDLY when the gate's saved decoder is missing, and use exactly the saved one otherwise.
#   scripts/lib/test-gate-decoder.sh      (milliseconds)
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t=$(mktemp -d "$here/artifacts/test-gate-decoder.XXXXXX" 2>/dev/null || { mkdir -p "$here/artifacts"; mktemp -d "$here/artifacts/test-gate-decoder.XXXXXX"; })
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
. "$here/scripts/lib/gate-decoder.sh"
mkdir -p "$t/r/.lake/build/bin"
export JANUS_GATE_PREBUILT=1
out="$(gate_decoder "$t/r" 2>&1)" && bad "no saved decoder: gate_decoder succeeded ($out)" || ok "no saved decoder: fails ($out)"
gate_save_decoder "$t/r" 2>/dev/null && bad "saving a decoder that was never built succeeded" || ok "saving an unbuilt decoder fails"
printf '#!/bin/sh\necho old\n' > "$t/r/.lake/build/bin/janus-decode"; chmod +x "$t/r/.lake/build/bin/janus-decode"
gate_save_decoder "$t/r" && ok "saved" || bad "save failed"
printf '#!/bin/sh\necho new\n' > "$t/r/.lake/build/bin/janus-decode"   # rebuilt after the save: the copy is no longer the current build
gate_decoder "$t/r" >/dev/null 2>&1 && bad "a decoder differing from the current build was accepted" || ok "rebuilt after the save: the saved copy is rejected"
# binding: another run's copy, a replaced copy, a copy with no stamp, a copy that differs from the current build
export JANUS_GATE_RUN_ID=run-A; printf '#!/bin/sh\necho old\n' > "$t/r/.lake/build/bin/janus-decode"; gate_save_decoder "$t/r" && ok "saved under run-A"
[ "$(gate_decoder "$t/r" 2>/dev/null)" = "$t/r/test/redteam/bin/janus-decode-gate" ] && ok "same run: accepted" || bad "same run rejected"
export JANUS_GATE_RUN_ID=run-B; gate_decoder "$t/r" >/dev/null 2>&1 && bad "a copy from another gate run (stale) accepted" || ok "stale copy from another run: rejected"
export JANUS_GATE_RUN_ID=run-A
rm -f "$t/r/.lake/build/bin/janus-decode"; gate_decoder "$t/r" >/dev/null 2>&1 && ok "build output dropped by janus: the stamp alone binds" || bad "dropped build output rejected"
printf '#!/bin/sh\necho evil\n' > "$t/r/.lake/build/bin/janus-decode"; chmod +x "$t/r/.lake/build/bin/janus-decode"
gate_decoder "$t/r" >/dev/null 2>&1 && bad "copy differing from the current build accepted" || ok "copy differs from the current build: rejected"
printf '#!/bin/sh\necho old\n' > "$t/r/.lake/build/bin/janus-decode"
printf '#!/bin/sh\necho evil\n' > "$t/r/test/redteam/bin/janus-decode-gate"; chmod +x "$t/r/test/redteam/bin/janus-decode-gate"
gate_decoder "$t/r" >/dev/null 2>&1 && bad "replaced copy accepted" || ok "replaced copy (stamp mismatch): rejected"
rm -f "$t/r/test/redteam/bin/janus-decode-gate.stamp"; gate_decoder "$t/r" >/dev/null 2>&1 && bad "unstamped copy accepted" || ok "unstamped copy: rejected"
# a failing save removes the earlier copy (never leaves the old one in place)
gate_save_decoder "$t/r" && rm -f "$t/r/.lake/build/bin/janus-decode" && { gate_save_decoder "$t/r" 2>/dev/null; [ ! -e "$t/r/test/redteam/bin/janus-decode-gate" ] && ok "failed save removed the earlier copy" || bad "failed save left the earlier copy"; }
unset JANUS_GATE_RUN_ID
rm -f "$t/r/test/redteam/bin/janus-decode-gate"
gate_decoder "$t/r" >/dev/null 2>&1 && bad "removed decoder accepted" || ok "removed decoder: fails again"
# the row script itself uses the helper
grep -q 'DEC="$(gate_decoder "$root")" || exit 1' "$here/test/redteam/rounds/round10/run-round10.sh" && grep -q '"\$DEC" "\$T"' "$here/test/redteam/rounds/round10/run-round10.sh" && ok "run-round10.sh takes its decoder from gate_decoder and fails when there is none" || bad "run-round10.sh does not use gate_decoder"
exit $fail

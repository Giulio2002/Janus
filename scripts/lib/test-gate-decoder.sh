#!/usr/bin/env bash
# audit/round10 must fail LOUDLY when the gate's saved decoder is missing, and use exactly the saved one otherwise.
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
printf '#!/bin/sh\necho new\n' > "$t/r/.lake/build/bin/janus-decode"   # rebuilt later: the gate's copy is the decoder of the gate
[ "$(gate_decoder "$t/r")" = "$t/r/audit/bin/janus-decode-gate" ] && [ "$("$t/r/audit/bin/janus-decode-gate")" = old ] && ok "the gate row uses exactly the saved decoder" || bad "wrong decoder"
rm -f "$t/r/audit/bin/janus-decode-gate"
gate_decoder "$t/r" >/dev/null 2>&1 && bad "removed decoder accepted" || ok "removed decoder: fails again"
# the row script itself uses the helper
grep -q 'DEC="$(gate_decoder "$root")" || exit 1' "$here/audit/round10/run-round10.sh" && grep -q '"\$DEC" "\$T"' "$here/audit/round10/run-round10.sh" && ok "run-round10.sh takes its decoder from gate_decoder and fails when there is none" || bad "run-round10.sh does not use gate_decoder"
exit $fail

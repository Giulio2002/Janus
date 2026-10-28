#!/usr/bin/env bash
# Self-test of scripts/lib/itemtimeout.sh (jv), with a stub `bin/janus` that sleeps. Run by go test
# (TestItemTimeoutLib). In a mktemp directory:
#   1. a verify within the limit passes and its output and status are untouched;
#   2. one that outlives JANUS_ITEM_TIMEOUT is killed, fails with status 124 and prints TIMEOUT, in
#      about the limit (not the stub's sleep), and its child process does not survive;
#   3. verify_theorems reports a timed-out theorem as failed (rc 124) while the other theorem of the
#      same example still passes;
#   4. JANUS_ITEM_TIMEOUT=0 disables the limit.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
t="$(mktemp -d "${TMPDIR:-/tmp}/test-itemtimeout.XXXXXX")"
trap 'rm -rf "$t"' EXIT
cd "$t"
mkdir -p bin artifacts/A
cat > bin/janus <<'EOS'
#!/usr/bin/env bash
# stub: janus verify DIR --proof P --theorem T ; theorem "slow" sleeps 60 s in a child
thm=$6
if [ "$thm" = slow ]; then sleep 60 & echo $! > "${STUB_PID:?}"; wait; fi
echo "Verified: $thm"
EOS
chmod +x bin/janus
printf '{\n  "binary": "../b"\n}\n' > artifacts/A/identity.json; echo b > artifacts/b
# shellcheck source=itemtimeout.sh
. "$here/itemtimeout.sh"
. "$here/theorems.sh"
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }
export STUB_PID="$t/pid"
out=$(JANUS_ITEM_TIMEOUT=20 jv artifacts/A --proof p --theorem fast) && [ "$out" = "Verified: fast" ] && ok "within the limit passes" || bad "within the limit: $out"
start=$(date +%s); rc=0
out=$(JANUS_ITEM_TIMEOUT=2 jv artifacts/A --proof p --theorem slow) || rc=$?
el=$(( $(date +%s) - start ))
{ [ $rc = 124 ] && grep -q '^TIMEOUT:' <<<"$out" && [ $el -lt 20 ]; } && ok "timeout: rc 124, TIMEOUT line, ${el}s" || bad "timeout rc=$rc el=$el out=$out"
sleep 1
if kill -0 "$(cat "$STUB_PID")" 2>/dev/null; then bad "stub child survived the timeout"; kill "$(cat "$STUB_PID")" 2>/dev/null || true; else ok "child process killed"; fi
st="$t/st"; mkdir -p "$st"
JANUS_ITEM_TIMEOUT=2 verify_theorems artifacts/A p "$st" fast slow 2>/dev/null || true
{ [ "$(cat "$st/0.rc")" = 0 ] && [ "$(cat "$st/1.rc")" = 124 ] && grep -q '^TIMEOUT:' "$st/1.log"; } && ok "verify_theorems: slow theorem timed out, fast one passed" || bad "verify_theorems rc: $(cat "$st"/*.rc | tr '\n' ' ')"
out=$(JANUS_ITEM_TIMEOUT=0 jv artifacts/A --proof p --theorem fast) && ok "limit disabled with 0" || bad "disabled"
[ $fail = 0 ] && echo "all checks passed"
exit $fail

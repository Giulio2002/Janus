#!/usr/bin/env bash
# Self-test of the go-test fixture lock behaviour (cmd/janus/janus_test.go TestMain, fixture_test.go ensureFixture):
#   1. `go test -list` never waits for (or builds) the fixture: with the fixture lock HELD by another process it still lists at once;
#   2. a real test run that finds the lock held says "waiting for the fixture lock" on stderr (no silent wait), and resumes ("got the
#      fixture lock after ...") when the holder lets go.
# Uses a private fixture dir (JANUS_TEST_FIXTURE_DIR) and a private test cache; the shared fixture is never touched.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export PATH=/usr/local/go/bin:$PATH
t="$(mktemp -d "${TMPDIR:-/tmp}/test-fixture-wait.XXXXXX")"
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
fx="$t/fx"; mkdir -p "$fx"
export JANUS_TEST_FIXTURE_DIR="$fx" JANUS_TEST_CACHE_DIR="$t/cache" JANUS_TEST_SEED_CACHE=off
( cd "$root/cmd/janus" && go test -c -o "$t/janus.test" . ) 2>&1 | tail -3
[ -x "$t/janus.test" ] || { echo "FAIL cannot compile the test binary"; rm -rf "$t"; exit 1; }
# hold the fixture lock from another process
exec 9>>"$fx/.fixture.lock"; flock -x 9
cd "$root/cmd/janus"
s=$SECONDS; out=$(timeout 120 "$t/janus.test" -test.list 'TestScanJanusModules' 2>&1); rc=$?
[ "$rc" = 0 ] && grep -q TestScanJanusModules <<<"$out" && [ $((SECONDS - s)) -lt 100 ] && ok "-test.list lists at once although the fixture lock is held ($((SECONDS - s)) s)" || bad "lister blocked or failed: rc $rc ($((SECONDS - s)) s) $out"
( timeout 25 "$t/janus.test" -test.run '^TestScanJanusModules$' > "$t/run.out" 2>&1 ) & rp=$!
sleep 12
grep -q "waiting for the fixture lock" "$t/run.out" && ok "a test run that finds the fixture lock held announces the wait" || bad "no 'waiting for the fixture lock' line: $(head -c 300 "$t/run.out")"
flock -u 9; exec 9>&-
wait $rp 2>/dev/null
grep -q "got the fixture lock after" "$t/run.out" && ok "... and says when it got the lock" || bad "no 'got the fixture lock' line: $(tail -c 300 "$t/run.out")"
rm -rf "$t"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail

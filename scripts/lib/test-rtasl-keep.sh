#!/usr/bin/env bash
# Self-test: audit/rt-asl/run.sh keeps its logs on a failure and removes them on success.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
T="$(mktemp -d "${TMPDIR:-/tmp}/rtasl-keep-test.XXXXXX")"; trap 'rm -rf "$T"' EXIT
mkdir -p "$T/tmp" "$T/keep"
fail=0
# a forced failure: an unknown group exits 2 after the work dir exists
out="$(TMPDIR="$T/tmp" RT_ASL_KEEP_DIR="$T/keep" JANUS_MEM_MAX=off "$root/audit/rt-asl/run.sh" nosuchgroup 2>&1)"; rc=$?
[ "$rc" -ne 0 ] || { echo "FAIL: forced failure returned 0"; fail=1; }
n=$(ls -d "$T"/tmp/rt-asl.* 2>/dev/null | wc -l)
[ "$n" = 1 ] && echo "ok: failed run left its log dir" || { echo "FAIL: log dir count $n"; fail=1; }
[ "$(ls "$T/keep" | wc -l)" = 1 ] && echo "ok: copied to RT_ASL_KEEP_DIR" || { echo "FAIL: no copy in keep dir"; fail=1; }
grep -q "kept in" <<<"$out" && echo "ok: path printed" || { echo "FAIL: no path printed: $out"; fail=1; }
# a successful run (no groups run: an empty group list is not possible, so run the cheapest real one with go skipped)
rm -rf "$T/tmp"/rt-asl.* "$T/keep"/*
out="$(TMPDIR="$T/tmp" RT_ASL_SKIP_GO=1 JANUS_MEM_MAX=off "$root/audit/rt-asl/run.sh" go 2>&1)"; rc=$?
if [ "$rc" = 0 ]; then
  [ "$(ls -d "$T"/tmp/rt-asl.* 2>/dev/null | wc -l)" = 0 ] && echo "ok: successful run removed its dir" || { echo "FAIL: dir left after success"; fail=1; }
else echo "FAIL: skip-go run rc=$rc: $out"; fail=1; fi
exit $fail

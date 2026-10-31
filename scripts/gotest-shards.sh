#!/usr/bin/env bash
# `go test ./cmd/...` split into shards that run at once, balanced by measured duration, with a
# proof that every test runs exactly once.
#
#   scripts/gotest-shards.sh [-n SHARDS] [-p PARALLEL] [--plan] [--outdir DIR]
#
#   -n SHARDS     number of shards (default: max(2, $JANUS_JOBS), at most 8)
#   -p PARALLEL   `go test -parallel` of each shard (default 1: the shards are the parallelism, so the
#                 total number of test slots is SHARDS x PARALLEL; $JANUS_GOTEST_PARALLEL)
#   --plan        print the assignment (shard, estimated seconds, tests) and the checks below, run nothing
#   --run ERE     development subset: only the tests whose name matches ERE (the partition check is then
#                 against that list; scripts/gate.sh --gotest-run). Not a gate run.
#   --outdir DIR  per-shard logs and the result (default artifacts/gate/gotest)
#
# The plan: `go test -list` gives the full list of tests (Test*, Example* and Fuzz* functions; benchmarks
# are not run by `go test` either) of every package under ./cmd/...; they are dealt to the shards
# longest first (greedy, onto the least loaded shard) using the measured durations in
# cmd/janus/order_test.go (testDurations; unknown tests, i.e. the ones under 1 s, count $JANUS_GOTEST_UNKNOWN s, default 1).
# Each shard runs `go test -count=1 -timeout 7000s -parallel P -v -run '^(T1|T2|...)$' PKG` for its
# tests. Checks, each of which fails the script:
#   before: the shards' test sets are disjoint and their union is the full list (no test unassigned,
#           none twice);
#   after:  every shard's output has a result line (PASS/FAIL/SKIP) for each of its tests, and none
#           for a test of another shard: the tests that ran are exactly the list, each once.
# A shard whose go test fails, times out or does not report all its tests fails the run. Subtests run
# with their parent. The whole run is `go test -timeout 7000s ./cmd/...` of the standard gate, cut in
# pieces (plus -count=1: a cached pass is never accepted).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
run="" nshards="" par="${JANUS_GOTEST_PARALLEL:-1}" plan="" outdir="$root/artifacts/gate/gotest"
while [ $# -gt 0 ]; do
  case "$1" in
    -n) nshards="$2"; shift 2 ;;
    -p) par="$2"; shift 2 ;;
    --plan) plan=1; shift ;;
    --run) run="$2"; shift 2 ;;
    --outdir) outdir="$2"; shift 2 ;;
    *) echo "usage: scripts/gotest-shards.sh [-n SHARDS] [-p PARALLEL] [--plan] [--outdir DIR]" >&2; exit 2 ;;
  esac
done
if [ -z "$nshards" ]; then
  nshards="${JANUS_JOBS:-2}"; [ "$nshards" -ge 2 ] || nshards=2; [ "$nshards" -le 8 ] || nshards=8
fi
unknown="${JANUS_GOTEST_UNKNOWN:-1}"
mkdir -p "$outdir"; rm -f "$outdir"/shard-*.log "$outdir"/shard-*.rc "$outdir"/plan.txt

# the list: "PKG<TAB>NAME"
: > "$outdir/all.txt"
for pkg in $(go list ./cmd/...); do
  go test -list '.*' "$pkg" 2>/dev/null | grep -E '^(Test|Example|Fuzz)' | sed "s|^|$pkg\t|" >> "$outdir/all.txt" || true
done
if [ -n "$run" ]; then grep -E -e "$run" <(cut -f2 "$outdir/all.txt") > /dev/null && awk -F'\t' -v re="$run" '$2 ~ re' "$outdir/all.txt" > "$outdir/all.tmp" && mv "$outdir/all.tmp" "$outdir/all.txt"; fi
[ -s "$outdir/all.txt" ] || { echo "gotest-shards: no tests listed"; exit 1; }
total=$(wc -l < "$outdir/all.txt")
if [ "$(cut -f2 "$outdir/all.txt" | sort | uniq -d | wc -l)" -ne 0 ]; then
  echo "gotest-shards: duplicate test names across packages are not supported"; exit 1
fi

# durations (order_test.go) -> "name<TAB>seconds"
grep -ohE '"[A-Za-z0-9_]+": [0-9.]+' cmd/janus/order_test.go | sed -E 's/^"([^"]+)": ([0-9.]+)$/\1\t\2/' > "$outdir/durations.txt" || true

# deal: longest first onto the least loaded shard
awk -F'\t' -v n="$nshards" -v unk="$unknown" -v out="$outdir" '
  FILENAME == ARGV[1] { d[$1] = $2; next }
  { name = $2; c = (name in d) ? d[name] : unk; cnt++; key[cnt] = $0; cost[cnt] = c }
  END {
    for (i = 1; i <= cnt; i++) idx[i] = i
    # selection by cost descending (stable by position)
    for (i = 1; i <= cnt; i++) for (j = i + 1; j <= cnt; j++) if (cost[idx[j]] > cost[idx[i]]) { t = idx[i]; idx[i] = idx[j]; idx[j] = t }
    for (s = 1; s <= n; s++) load[s] = 0
    for (k = 1; k <= cnt; k++) {
      i = idx[k]; best = 1
      for (s = 2; s <= n; s++) if (load[s] < load[best]) best = s
      load[best] += cost[i]; print best "\t" key[i] "\t" cost[i] > (out "/assign.txt")
    }
    for (s = 1; s <= n; s++) print s "\t" load[s] > (out "/loads.txt")
  }' "$outdir/durations.txt" "$outdir/all.txt"

# check: disjoint, complete
assigned=$(wc -l < "$outdir/assign.txt")
if [ "$assigned" -ne "$total" ] || [ "$(cut -f2,3 "$outdir/assign.txt" | cut -f1,2 | sort -u | wc -l)" -ne "$total" ] ||
   ! diff -q <(cut -f1,2 "$outdir/all.txt" | sort) <(cut -f2,3 "$outdir/assign.txt" | sort) >/dev/null; then
  echo "gotest-shards: the shards do not partition the test list ($assigned assigned, $total listed)"; exit 1
fi
{
  echo "gotest shards: $total tests in $nshards shards (-parallel $par each)"
  for ((s = 1; s <= nshards; s++)); do
    printf 'shard %d: est %ss, %d tests:' "$s" "$(awk -F'\t' -v s="$s" '$1 == s { print int($2 + 0.5) }' "$outdir/loads.txt")" "$(awk -F'\t' -v s="$s" '$1 == s' "$outdir/assign.txt" | wc -l)"
    awk -F'\t' -v s="$s" '$1 == s { printf " %s", $3 }' "$outdir/assign.txt"; echo
  done
  echo "partition check: ok ($total listed = $assigned assigned, each once)"
} | tee "$outdir/plan.txt"
[ -z "$plan" ] || exit 0

# A test cache of its own per shard, on disk next to the user cache (not in a RAM /tmp), seeded by the tests'
# TestMain from the user's cache and removed at the end, also when the run is interrupted (trap).
cachebase="${XDG_CACHE_HOME:-$HOME/.cache}"; mkdir -p "$cachebase"
runcache="$(mktemp -d "$cachebase/janus-test-run-XXXXXX")"
trap 'rm -rf "$runcache"' EXIT
trap 'exit 143' TERM INT
run_shard() { # S
  local s=$1 pkg re rc=0 f="$outdir/shard-$s"
  : > "$f.log"
  mkdir -p "$runcache/$s"; export JANUS_TEST_CACHE_DIR="$runcache/$s"
  for pkg in $(awk -F'\t' -v s="$s" '$1 == s { print $2 }' "$outdir/assign.txt" | sort -u); do
    re=$(awk -F'\t' -v s="$s" -v p="$pkg" '$1 == s && $2 == p { printf "%s%s", (n++ ? "|" : ""), $3 }' "$outdir/assign.txt")
    echo "== go test -count=1 -timeout 7000s -parallel $par -v -run '^($re)\$' $pkg" >> "$f.log"
    memguard_run -n "gotest-$s" -- go test -count=1 -timeout 7000s -parallel "$par" -v -run "^($re)\$" "$pkg" >> "$f.log" 2>&1 || rc=$?
  done
  echo "$rc" > "$f.rc"
}
t0=$(date +%s)
pids=()
for ((s = 1; s <= nshards; s++)); do run_shard "$s" & pids+=($!); done
# stream a line per finished shard
fail=0
for ((s = 1; s <= nshards; s++)); do
  wait "${pids[$((s - 1))]}" || true
  rc=$(cat "$outdir/shard-$s.rc" 2>/dev/null || echo missing)
  printf 'shard %d: go test exit %s (%ss since start)\n' "$s" "$rc" "$(( $(date +%s) - t0 ))"
  [ "$rc" = 0 ] || { fail=1; tail -n 40 "$outdir/shard-$s.log" | sed 's/^/  | /'; }
done
# after: the tests that ran are exactly the shard's tests
for ((s = 1; s <= nshards; s++)); do
  grep -E '^--- (PASS|FAIL|SKIP): ' "$outdir/shard-$s.log" | awk '{ sub(/:$/, "", $3); print $3 }' | sort > "$outdir/ran-$s.txt" || true
  awk -F'\t' -v s="$s" '$1 == s { print $3 }' "$outdir/assign.txt" | sort > "$outdir/want-$s.txt"
  if ! diff -q "$outdir/want-$s.txt" "$outdir/ran-$s.txt" >/dev/null; then
    echo "gotest-shards: shard $s ran a different set of tests than assigned:"; diff "$outdir/want-$s.txt" "$outdir/ran-$s.txt" | head -20; fail=1
  fi
done
ran=$(cat "$outdir"/ran-*.txt | sort | wc -l)
if [ "$ran" -ne "$total" ] || [ "$(cat "$outdir"/ran-*.txt | sort -u | wc -l)" -ne "$total" ]; then
  echo "gotest-shards: $ran test results for $total listed tests (each must run exactly once)"; fail=1
fi
grep -hE '^--- FAIL' "$outdir"/shard-*.log && fail=1
printf 'gotest shards: %d tests ran once each in %d shards, %ss wall\n' "$ran" "$nshards" "$(( $(date +%s) - t0 ))"
[ "$fail" = 0 ] && echo "gotest shards: all ok" || { echo "gotest shards: FAILED"; exit 1; }

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
mkdir -p "$outdir"; rm -f "$outdir"/shard-*.log "$outdir"/shard-*.rc "$outdir"/plan.txt "$outdir"/extra-*.log "$outdir"/extra-*.rc "$outdir"/skips*.txt

# the list: "PKG<TAB>NAME"
: > "$outdir/all.txt"
for pkg in $(go list ./cmd/...); do
  go test -timeout 60m -list '.*' "$pkg" 2>/dev/null | grep -E '^(Test|Example|Fuzz)' | sed "s|^|$pkg\t|" >> "$outdir/all.txt" || true
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
# Extras: tests that the shards must report as SKIPPED (they need an environment of their own: a 20 GiB memory cap, a Mathlib
# checkout) and that run here, beside the shards, in the nightly gates (JANUS_NIGHTLY=1; JANUS_GOTEST_EXTRAS=0/1 overrides). A
# nightly with an extra that does not PASS fails; without extras the SKIPPED-COVERAGE summary below says so loudly.
#   NAME | memory limit of the run | environment (KEY=VALUE ...) | cache + package dir (persistent, "" = per run)
# The persistent directories are keyed by the exact inputs (checkout path, toolchain, Mathlib revision): another key is a miss
# (a cold build), never a reuse; what is inside is content-checked by lake / janus themselves (a corrupt entry rebuilds or fails).
extras_on="${JANUS_GOTEST_EXTRAS:-}"; [ -n "$extras_on" ] || { [ "${JANUS_NIGHTLY:-}" = 1 ] && extras_on=1 || extras_on=0; }
extra_names=() extra_pids=() asl_deferred=()
mathlib_rev="${JANUS_TEST_MATHLIB_REV:-d13f23b723b8a846827a245b89c10fc7d3f11612}"
mathlib_key=$(printf '%s\n%s\n%s\n' "$root" "$(cat "$root/lean-toolchain" 2>/dev/null)" "$mathlib_rev" | sha256sum | cut -c1-16)
asl_key=$(printf '%s\n%s\n' "$root" "$(cat "$root/lean-toolchain" 2>/dev/null)" | sha256sum | cut -c1-16)
run_extra() { # LABEL "NAME NAME..." LIMIT ENVWORDS : one run (explicit -timeout 7000s) run of the named tests; every name must PASS
  local label=$1 names=$2 limit=$3 envw=$4 pkg f="$outdir/extra-$1" rc=0 re
  re=$(printf '%s' "$names" | tr ' ' '|')
  pkg=$(awk -F'\t' -v n="${names%% *}" '$2 == n { print $1 }' "$outdir/all.txt")
  : > "$f.log"
  echo "== extra $label: $envw go test -count=1 -timeout 7000s -v -run '^($re)\$' $pkg (memory limit $limit)" >> "$f.log"
  # shellcheck disable=SC2086
  memguard_run -l "$limit" -n "extra-$label" -- env $envw go test -count=1 -timeout 7000s -parallel 1 -v -run "^($re)\$" "$pkg" >> "$f.log" 2>&1 || rc=$?
  echo "$rc" > "$f.rc"
}
if [ "$extras_on" = 1 ]; then
  mkdir -p "$cachebase/janus-test-mathlib-$mathlib_key/cache" "$cachebase/janus-test-mathlib-$mathlib_key/pkg" "$cachebase/janus-test-asl-$asl_key" "$runcache/x-pressure"
  # label | tests | memory limit | environment. The ASL tests (JANUS_TEST_ASL=1) build JanusASL: about an hour cold; the persistent test cache
  # (keyed by checkout path and toolchain; its entries are keyed by framework and package hashes inside) and the checkout's own built
  # JanusASL as a seed (Lake reuses it by content, JANUS_TEST_ASL_SEED) make later runs short. JANUS_GOTEST_EXTRA_LIST (space
  # separated labels) limits the extras (development).
  # (no JANUS_TEST_ASL_SEED: a seed is accepted only with an attested manifest, asl_test.go verifyASLSeed; the persistent keyed
  # cache directory below is the warm start, built by janus's own buildASL under Lake's trace checks)
  extras=(
    "pressure|TestReplayUnderMemoryPressure|20G|JANUS_PRESSURE_TEST=1 JANUS_TEST_CACHE_DIR=$runcache/x-pressure"
    "mathlib|TestConsumerMathlib|24G|JANUS_TEST_MATHLIB=1 JANUS_TEST_CACHE_DIR=$cachebase/janus-test-mathlib-$mathlib_key/cache JANUS_TEST_MATHLIB_DIR=$cachebase/janus-test-mathlib-$mathlib_key/pkg JANUS_TEST_MATHLIB_REV=$mathlib_rev"
    "asl|TestASLExamples TestASLForgeryRejected TestASLUncovered TestASLConsumer|48G|JANUS_MEM_MAX=48G JANUS_TEST_ASL=1 JANUS_TEST_CACHE_DIR=$cachebase/janus-test-asl-$asl_key "
  )
  for e in "${extras[@]}"; do
    IFS='|' read -r lab names lim envw <<< "$e"
    if [ -n "${JANUS_GOTEST_EXTRA_LIST:-}" ] && [[ " $JANUS_GOTEST_EXTRA_LIST " != *" $lab "* ]]; then continue; fi
    ok=1; for n in $names; do cut -f2 "$outdir/all.txt" | grep -qx "$n" || ok=0; done
    [ "$ok" = 1 ] || continue
    if [ "$lab" = asl ]; then asl_deferred=("$lab" "$names" "$lim" "$envw"); continue; fi   # 48 GiB: runs ALONE, after everything else (below)
    run_extra "$lab" "$names" "$lim" "$envw" & extra_pids+=($!); extra_names+=("$lab:$names")
  done
fi
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
# The ASL extra needs a 48 GiB job and builds JanusASL: it never runs beside the shards or the other extras. It starts only once
# they have all finished (the shards were waited for above; the other extras are waited for here first) and takes the host's
# one-heavy-job lock (JANUS_HEAVY_LOCK, default /srv/janus-ops/heavy.lock when that directory exists) unless the caller says it
# already holds it (JANUS_HEAVY_LOCK_HELD=1, e.g. the whole lane was started under `flock`).
if [ "${#asl_deferred[@]}" = 4 ]; then
  for i in "${!extra_pids[@]}"; do wait "${extra_pids[$i]}" || true; done
  hl="${JANUS_HEAVY_LOCK:-}"; [ -n "$hl" ] || { [ ! -d /srv/janus-ops ] || hl=/srv/janus-ops/heavy.lock; }
  echo "extra asl: starting alone after the shards (heavy lock: ${hl:-none}${JANUS_HEAVY_LOCK_HELD:+, already held})"
  if [ -n "$hl" ] && [ "${JANUS_HEAVY_LOCK_HELD:-}" != 1 ]; then
    exec 8>>"$hl"; flock 8   # released when this script exits
  fi
  run_extra "${asl_deferred[@]}"
  extra_names+=("${asl_deferred[0]}:${asl_deferred[1]}"); extra_pids+=("$$")   # (nothing left to wait for: the run was in the foreground)
fi
# the extras: each named test must have run and PASSED (a skip or a failure of an extra fails the run)
extra_ok=()
for i in "${!extra_names[@]}"; do
  lab=${extra_names[$i]%%:*}; names=${extra_names[$i]#*:}; wait "${extra_pids[$i]}" || true
  erc=$(cat "$outdir/extra-$lab.rc" 2>/dev/null || echo missing)
  printf 'extra %s: go test exit %s (%ss since start)\n' "$lab" "$erc" "$(( $(date +%s) - t0 ))"
  allpass=1; for n in $names; do grep -qE "^--- PASS: $n " "$outdir/extra-$lab.log" || allpass=0; done
  if [ "$erc" = 0 ] && [ "$allpass" = 1 ]; then for n in $names; do extra_ok+=("$n"); done
  else echo "gotest-shards: extra $lab did not PASS (exit $erc):"; tail -n 40 "$outdir/extra-$lab.log" | sed 's/^/  | /'; fail=1; fi
done
# a SKIPPED test is not a verified one (about ten tests skip when objdump, the aarch64 objdump, lake or bwrap is missing): a run with any SKIP is
# never recorded as a lane PASS (scripts/lib/incr.sh incr_lane: INCR_NORECORD_FILE), whatever the exit status.
# SKIPPED-COVERAGE: every skip is printed with its reason, loudly, once; a skipped test whose extra run PASSED above is listed as
# covered and does not count.
cat "$outdir"/shard-*.log | awk '
  /^[ \t]+[A-Za-z0-9_]+\.go:[0-9]+: / { sub(/^[ \t]+/, ""); last = $0 }
  /^[ \t]*--- SKIP: / { n = $3; sub(/:$/, "", n); r = last; sub(/^[A-Za-z0-9_]+\.go:[0-9]+: /, "", r); print n "\t" r; last = "" }' > "$outdir/skips.txt"
nskip=0 ncov=0
: > "$outdir/skips-uncovered.txt"
while IFS=$'\t' read -r n r; do
  [ -n "$n" ] || continue
  cov=0; for e in "${extra_ok[@]:-}"; do [ "$e" != "$n" ] || cov=1; done
  if [ "$cov" = 1 ]; then ncov=$((ncov + 1)); printf '  covered   %s (%s) -> ran and PASSED in its own run (extra-*.log)\n' "$n" "${r:-no reason logged}" >> "$outdir/skips-report.txt"
  else nskip=$((nskip + 1)); printf '  NOT RUN   %s: %s\n' "$n" "${r:-no reason logged}" | tee -a "$outdir/skips-uncovered.txt" >> "$outdir/skips-report.txt"; fi
done < "$outdir/skips.txt"
if [ "$nskip" -gt 0 ] || [ "$ncov" -gt 0 ]; then
  echo "SKIPPED-COVERAGE: $nskip test(s) did NOT run in this lane ($ncov skipped in the shards but covered by an extra run):"
  cat "$outdir/skips-report.txt"
  [ "$extras_on" = 1 ] || echo "  (extras off: JANUS_NIGHTLY=1 or JANUS_GOTEST_EXTRAS=1 also runs TestReplayUnderMemoryPressure, TestConsumerMathlib and the four TestASL* tests)"
fi
if [ "$nskip" -gt 0 ]; then
  echo "gotest-shards: $nskip test(s) SKIPPED (a skip is not a pass; this run is not recorded)"
  [ -z "${INCR_NORECORD_FILE:-}" ] || echo "gotest: $nskip skipped test(s)" >> "$INCR_NORECORD_FILE"
  [ "${JANUS_REQUIRE_NO_SKIP:-}" != 1 ] || fail=1
fi
printf 'gotest shards: %d tests ran once each in %d shards, %ss wall\n' "$ran" "$nshards" "$(( $(date +%s) - t0 ))"
[ "$fail" = 0 ] && echo "gotest shards: all ok" || { echo "gotest shards: FAILED"; exit 1; }

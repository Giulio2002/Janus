#!/usr/bin/env bash
# Measure the elaboration time of proofs (the time `lean` spends checking the proof file
# against a pre-compiled `Extracted.olean`, i.e. tactic run time plus kernel checking).
#
# Usage: scripts/bench.sh [suite ...]
#   suites: examples-arm64  examples/proofs/<F>.lean            against artifacts/<F>
#           examples-amd64  examples/proofs-amd64/<F>/Proof.lean against artifacts/amd64/<F>
#           bench-arm64     bench/proofs-arm64/<F>.lean         against artifacts/bench-arm64/<F>
#           bench-amd64     bench/proofs-amd64/<F>.lean         against artifacts/bench-amd64/<F>
#   (bench proofs are named after the Go function they are about)
#   (default: all four). The bench suites build bench/go for both ISAs and extract every
#   function listed in bench/functions.txt first.
# Environment: JOBS (parallel proofs, default 1: sequential timings are the comparable ones),
#   OUT (result file, default artifacts/bench/results.tsv), FILTER (regex on proof names).
# Output: one line per proof, `suite<TAB>name<TAB>cpu-seconds<TAB>wall-seconds<TAB>ok|FAIL`,
# appended to $OUT and printed; failures keep their log in artifacts/bench/logs/<suite>-<name>.log.
# CPU time (user + system of the `lean` process) is what to compare: wall time depends on the
# load of the machine.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PATH="$PATH:/usr/local/go/bin"
# the same pinned Go release as the example builds (addresses and code depend on it)
export GOTOOLCHAIN="${JANUS_GO_TOOLCHAIN:-go1.26.0}"
suites=("$@")
[ ${#suites[@]} -eq 0 ] && suites=(examples-arm64 examples-amd64 bench-arm64 bench-amd64)
JOBS=${JOBS:-1}
OUT=${OUT:-$root/artifacts/bench/results.tsv}
FILTER=${FILTER:-.}
mkdir -p "$root/artifacts/bench/logs" "$root/bin"
lake build Janus >/dev/null
[ -x bin/janus ] || go build -o bin/janus ./cmd/janus
LP="$(lake env printenv LEAN_PATH)"

build_bench() {
  local arch=$1
  local bin="$root/artifacts/bench-$arch.bin"
  (cd "$root/bench/go" && CGO_ENABLED=0 GOOS=linux GOARCH=$arch GOAMD64=v1 \
    go build -trimpath -buildvcs=false -o "$bin" ./cmd)
  while read -r f; do
    [ -z "$f" ] && continue
    case "$f" in \#*) continue ;; esac
    bin/janus extract "$bin" "example.com/bench.$f" "$root/artifacts/bench-$arch/$f" >/dev/null
  done < "$root/bench/functions.txt"
}

# one proof: suite name proof-file artifact-dir
run_one() {
  local suite=$1 name=$2 proof=$3 art=$4
  local tmp; tmp=$(mktemp -d)
  local log="$root/artifacts/bench/logs/$suite-$name.log"
  if ! LEAN_PATH="$tmp:$LP" lean -o "$tmp/Extracted.olean" "$art/Extracted.lean" > "$log" 2>&1; then
    printf '%s\t%s\t-\t-\tFAIL(extracted)\n' "$suite" "$name"; rm -rf "$tmp"; return
  fi
  local st=ok
  /usr/bin/time -f "%U %S %e" -o "$tmp/time" env LEAN_PATH="$tmp:$LP" lean "$proof" > "$log" 2>&1 || st=FAIL
  grep -q ": error" "$log" && st=FAIL
  grep -q "declaration uses 'sorry'" "$log" && st=FAIL
  [ "$st" = ok ] && rm -f "$log"
  # CPU time (user + system) is the comparable number on a loaded machine; wall time too
  read -r u sy wall < <(tail -1 "$tmp/time")
  printf '%s\t%s\t%.2f\t%.2f\t%s\n' "$suite" "$name" "$(echo "$u + $sy" | bc)" "$wall" "$st"
  rm -rf "$tmp"
}
export -f run_one
export root LP

jobs_file=$(mktemp)
for s in "${suites[@]}"; do
  case $s in
    examples-arm64)
      for f in examples/proofs/*.lean; do
        n=$(basename "$f" .lean); [ "$n" = WrongAdd ] && continue
        [ -d "artifacts/$n" ] || { [ -x artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null;
          bin/janus extract artifacts/examples-arm64 "example.com/basic.$n" "artifacts/$n" >/dev/null; }
        echo "$s $n $f artifacts/$n" >> "$jobs_file"
      done ;;
    examples-amd64)
      for d in examples/proofs-amd64/*/; do
        n=$(basename "$d")
        [ -d "artifacts/amd64/$n" ] || scripts/build-examples-amd64.sh >/dev/null
        echo "$s $n ${d}Proof.lean artifacts/amd64/$n" >> "$jobs_file"
      done ;;
    bench-arm64|bench-amd64)
      arch=${s#bench-}
      build_bench "$arch"
      for f in bench/proofs-$arch/*.lean; do
        n=$(basename "$f" .lean)
        echo "$s $n $f artifacts/bench-$arch/$n" >> "$jobs_file"
      done ;;
    *) echo "unknown suite $s" >&2; exit 2 ;;
  esac
done
grep -E "$FILTER" "$jobs_file" | xargs -P "$JOBS" -L 1 bash -c 'run_one "$@"' _ | tee -a "$OUT"
rm -f "$jobs_file"

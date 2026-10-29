#!/usr/bin/env bash
# Evidence that the thread count does not change build outputs (why LEAN_NUM_THREADS is not in the ASL cache key;
# docs/SOUNDNESS.md "Build caches"): build the same modules with LEAN_NUM_THREADS=1 and with 4, in two scratch
# copies at the SAME path (one after the other, so no path difference), and compare the SHA-256 of every
# .olean/.ilean/.c/.c.o.export under .lake/build. Heavy-ish (the lean-sail package and ArmASL's first modules:
# a few minutes with 4 threads, longer with 1): run it under memcap, one heavy job.
#
#   scripts/lib/test-thread-identity.sh [TARGET...]    default targets: ArmASL.Defs ArmASL.FakeReal ArmASL.SpecializationV1
#                                                       ArmASL.JanusExtras (plus their Sail dependencies)
# Exit 0 when every output file is byte-identical across the two runs, 1 otherwise.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
targets=("$@"); [ ${#targets[@]} -gt 0 ] || targets=(ArmASL.Defs ArmASL.FakeReal ArmASL.SpecializationV1 ArmASL.JanusExtras)
work=$(mktemp -d /srv/janus-ops/work.XXXX); trap 'rm -rf "$work"' EXIT
co="$work/co"; tree="$co/JanusASL"   # the package requires the framework by path (..): a full checkout layout
mkdir -p "$co"
rsync -a --exclude=.git --exclude=.lake --exclude=artifacts --exclude=target --exclude=bin --exclude=JanusX86 --exclude=oracle-sail "$root/" "$co/" || exit 1
(cd "$tree" && tar -xzf vendor/ArmASL.tar.gz && touch ArmASL.lean) || exit 1
run() { # run THREADS OUTFILE: a clean .lake each time, the same path
  rm -rf "$tree/.lake"
  local s=$SECONDS
  (cd "$tree" && LEAN_NUM_THREADS=$1 lake build "${targets[@]}") > "$work/build-$1.log" 2>&1 || { echo "build with $1 thread(s) FAILED: $(tail -3 "$work/build-$1.log")"; return 1; }
  echo "built ${targets[*]} with LEAN_NUM_THREADS=$1 in $((SECONDS - s)) s"
  (cd "$tree/.lake" && find build packages/Sail/.lake/build -type f \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' -o -name '*.c.o.export' -o -name '*.o' \) -print0 | sort -z | xargs -0 sha256sum) > "$2"
}
run 1 "$work/h1" || exit 1
run 4 "$work/h4" || exit 1
n=$(wc -l < "$work/h1")
if [ "$n" -gt 0 ] && cmp -s "$work/h1" "$work/h4"; then
  echo "ok   $n output files (.olean/.ilean/.c/.o) are byte-identical with LEAN_NUM_THREADS=1 and 4"
  exit 0
fi
echo "FAIL the outputs differ between 1 and 4 threads ($n files):"; diff "$work/h1" "$work/h4" | head -20
exit 1

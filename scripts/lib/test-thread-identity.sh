#!/usr/bin/env bash
# Evidence that the thread count does not change build outputs (why LEAN_NUM_THREADS is not in the ASL cache key;
# docs/SOUNDNESS.md "Build caches"): build the same modules with LEAN_NUM_THREADS=1, 4 and 0 (0 = all cores, what Lean does when asked for no limit), in two scratch
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
run 0 "$work/h0" || exit 1
n=$(wc -l < "$work/h1")
if ! { [ "$n" -gt 0 ] && cmp -s "$work/h1" "$work/h4" && cmp -s "$work/h1" "$work/h0"; }; then
  echo "FAIL the outputs differ across thread counts ($n files):"; diff "$work/h1" "$work/h4" | head -10; diff "$work/h1" "$work/h0" | head -10
  exit 1
fi
echo "ok   $n output files (.olean/.ilean/.c/.o) of the model sample are byte-identical with LEAN_NUM_THREADS=1, 4 and 0"

# ---- phase 2: JanusASL proof modules. Their dependencies (the whole model and 200+ framework modules) are
# restored from the verified build cache, the same bytes in every run; only the sample modules' own outputs are
# deleted and rebuilt with each thread count. Skipped (loudly) when the cache has no entry for this checkout.
proofs=(${IDENT_PROOF_MODULES:-JanusASL.Proofs.Madd JanusASL.Proofs.Rel})
cache="${ASL_CACHE:-/srv/janus-asl-cache}"
prun() { # prun THREADS OUTFILE
  rm -rf "$tree/.lake"
  (cd "$co" && ASL_CACHE="$cache" scripts/asl.sh restore) > "$work/prestore-$1.log" 2>&1 || return 2
  [ -f "$tree/.lake/build/lib/lean/ArmASL.olean" ] || return 2
  python3 -I "$co/JanusASL/tools/asl_mod_cache.py" restore "$co" "$cache" >> "$work/prestore-$1.log" 2>&1
  local m f
  for m in "${proofs[@]}"; do
    [ -f "$tree/.lake/build/lib/lean/${m//.//}.olean" ] || return 2   # its dependencies must be restored too
    rm -f "$tree/.lake/build/lib/lean/${m//.//}".* "$tree/.lake/build/ir/${m//.//}".*
  done
  local s=$SECONDS
  (cd "$tree" && LEAN_NUM_THREADS=$1 lake build "${proofs[@]}") > "$work/pbuild-$1.log" 2>&1 || { echo "proof build with $1 thread(s) FAILED: $(tail -3 "$work/pbuild-$1.log")"; return 1; }
  grep -q "Built ${proofs[0]}" "$work/pbuild-$1.log" || { echo "FAIL: ${proofs[0]} was not rebuilt (a restored trace was reused)"; return 1; }
  echo "rebuilt ${proofs[*]} with LEAN_NUM_THREADS=$1 in $((SECONDS - s)) s"
  (cd "$tree/.lake" && for m in "${proofs[@]}"; do ls build/lib/lean/${m//.//}.olean build/lib/lean/${m//.//}.ilean build/ir/${m//.//}.c 2>/dev/null; done | sort | xargs sha256sum) > "$2"
}
rc2=0
prun 1 "$work/p1"; rc2=$?
if [ "$rc2" = 2 ]; then
  echo "SKIP phase 2: no usable cache entry for this checkout in $cache (run scripts/asl.sh build with that cache first)"
  exit 0
fi
[ "$rc2" = 0 ] || exit 1
prun 4 "$work/p4" || exit 1
prun 0 "$work/p0" || exit 1
pn=$(wc -l < "$work/p1")
if [ "$pn" -gt 0 ] && cmp -s "$work/p1" "$work/p4" && cmp -s "$work/p1" "$work/p0"; then
  echo "ok   $pn output files of ${proofs[*]} (proof modules, dependencies from the verified cache) are byte-identical with LEAN_NUM_THREADS=1, 4 and 0"
  exit 0
fi
echo "FAIL the proof modules' outputs differ across thread counts:"; diff "$work/p1" "$work/p4" | head -10; diff "$work/p1" "$work/p0" | head -10
exit 1

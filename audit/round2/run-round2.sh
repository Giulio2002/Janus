#!/usr/bin/env bash
# Reproduce the round-2 attacks (docs/AUDIT-ROUND2.md) and check the fixes: exits 1 if a fixed
# finding (CRITICAL-1, U1) regresses. Writes only under audit/round2/work/ (and temporary cache
# dirs / marker files under /tmp, removed again).
# Usage: audit/round2/run-round2.sh [-j N]   (-j: rows at once, default the core count capped by
#        memory, see scripts/lib/parallel.sh; -j 1 runs them one by one; output order is unchanged)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
par_init "$@"
J="$root/audit/round2/bin/janus"
mkdir -p "$(dirname "$J")"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round2/work; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1

v() { "$J" verify --janus-root "$root" "$@" 2>&1; }
line() { v "$@" | grep -E 'Verified:|Invalid' | head -1; }
broken=()

s1_header() {
echo "== S1 (CRITICAL-1, fixed): inline non-canonical instances in the statement =="
echo "The target example.com/basic.Add computes x + y. Each attack compiles against the real proof"
echo "and, before the fix, printed Verified with a statement reading as a different operation."
echo "Expected now: Invalid at Stage: statement identity (inline instance / does not round-trip)."
}
s1_row() {
  local a=$1 out r st
  out="$(v --proof audit/round2/attacks/$a.lean $W/Add)"
  r="$(grep -m1 -E '^(Verified|Invalid)' <<<"$out" | cut -c1-110)"
  st="$(grep -m1 'Stage:' <<<"$out" | sed 's/.*Stage: //')"
  printf '  %-20s %s [%s]\n' "$a" "$r" "$st"
  case "$r" in Verified*) echo "      >>> BROKEN: binary adds, statement says otherwise, yet Verified."; broken+=("$a") ;; esac
}
m1_block() {
echo
echo "== M1: Lean module-system proof (blocked on the single-file path) =="
r="$(line --proof audit/round2/attacks/M1_module_system.lean $W/Add)"; echo "  $r"
case "$r" in Verified*) broken+=(M1) ;; esac

echo
echo "== Positive controls (must elaborate with only propext/Quot.sound/Classical.choice) =="
echo "  AtomicAdd_witness.lean: see audit/round2/controls/ (run under lake env lean)."
}
# U1 and U1b share the host marker paths: one block, in order.
u1_block() {
echo
echo "== U1 / U1b (fixed): unshare fallback, forced with JANUS_SANDBOX=unshare =="
echo "Expected: U1 Invalid (its write to the read-only cache throws), U1b Verified (it catches its failed"
echo "writes); in both, nothing the sandboxed proof writes reaches the host"
echo "(trusted cache on the /tmp mount, /tmp, /dev/shm, /boot, /run/user/0, /run)."
markers=(/tmp/janus-u1b-marker /dev/shm/janus-u1b-marker /boot/janus-u1b-marker /run/user/0/janus-u1b-marker /run/janus-u1b-marker)
for a in U1_unshare_cache_write U1b_unshare_mounts; do
  c=$(mktemp -d /tmp/janus-u1-cache.XXXXXX); rm -f "${markers[@]}"
  out="$(JANUS_SANDBOX=unshare JANUS_CACHE_DIR="$c" "$J" verify --janus-root "$root" --proof audit/round2/attacks/$a.lean $W/Add 2>&1)"
  leaked=""; for m in "${markers[@]}" "$c/v1/replay/00/planted-by-sandboxed-proof"; do [ -e "$m" ] && leaked="$leaked $m"; done
  rm -f "${markers[@]}"; rm -rf "$c"
  printf '  %-24s %s\n' "$a" "$(grep -m1 -E '^(Verified|Invalid)' <<<"$out" | cut -c1-100)"
  if [ -n "$leaked" ]; then echo "      >>> BROKEN: written to the host:$leaked"; broken+=("$a"); fi
  if grep -q 'Stage: sandbox' <<<"$out"; then echo "      (the fallback refused on this host; install bubblewrap)"; fi
done
}
medium1_block() {
echo
echo "== MEDIUM-1 (amd64 DF): see audit/round2/amd64/README.txt; with artifacts/examples-amd64 built:"
if [ -f artifacts/examples-amd64 ]; then
  "$J" extract artifacts/examples-amd64 example.com/basic.CopyBlock $W/amd64-CopyBlock >/dev/null &&
  df_out=$(v --proof audit/round2/amd64/controls/DFMemmove.lean --theorem DFRepro.memmove_backward_rep_copies_forward $W/amd64-CopyBlock | head -1)
  echo "$df_out"
fi
echo "(MEDIUM-1 is fixed: amd64 models DF. This repro's concrete state t leaves df at its default"
echo " false, and with DF = 0 a forward copy is correct, so the theorem is now true and honest about"
echo " a state real executions never reach; Verified is expected. The fix itself is checked by"
echo " JanusTests.Amd64.df_backward_not_forward: with DF = 1 (after STD) the model copies backward.)"
echo "Model repros: audit/round2/model/README.txt (arm64, run from a copy of agent/arm64cov2), audit/round2/amd64/README.txt."
}

par_run s1_header
for a in S1_inline_instance S1c_mul S1d_ofnat S1e_decidable_if S1f_lt S1g_coe S1h_coe_inline S1i_beta; do
  par_run 's1_row "$a"'
done
par_run m1_block
par_run u1_block
par_run medium1_block
par_wait

if [ ${#broken[@]} -gt 0 ]; then
  echo "BROKEN: ${broken[*]}"
  exit 1
fi
echo "All round-2 verifier rows as expected (no BROKEN row)."

#!/usr/bin/env bash
# Gate-side LIVENESS check of the incremental keys (docs/TESTING.md "Incremental gate", "Liveness check"). The bug of ad264a2: the gate
# exported run-specific variables (a timestamped directory, a tree stamp, a load-derived job count) that were part of every key, so a
# record written by one gate run never matched the next and the incremental gate skipped nothing. The static scan
# (cmd/janus TestIncr2EveryGateExportIsClassified) finds the exports it can read; this finds a run-specific variable however it got into
# the environment (eval, computed names, a sourced file, a tool).
#
# It runs `janus incr explain` on one cheap item (arm64:Add: its proof file, the verifier, the toolchain; --no-fw: no build needed) in two
# consecutive invocations with identical content and different run-specific bookkeeping, and fails if the keys differ:
#   A  the environment as it is (inside a gate run: the real exports of THIS run)
#   B  the same, with the value of every variable the gate ADDED to its environment (GATE_ENV0_NAMES, written by scripts/gate.sh
#      before its first export, names the variables that were there at the start) changed to another value, except the variables
#      listed in scripts/lib/incr-keyed-exports.txt (constants of the gate that are keyed on purpose). PATH, HOME, PWD, OLDPWD, SHLVL,
#      _ and LC_*/LANG are not keyed by decision (docs/TESTING.md "Unkeyed environment").
#   C  (control) A with a keyed variable changed: the key MUST differ, so the check cannot pass because explain ignores the environment.
# Without GATE_ENV0_NAMES (a standalone run) B is the original bug: JANUS_GATE_TREE0, JANUS_LAKEGUARD_PIN/ROOT and the sizing
# variables with other values.
# Usage: JANUS_LIVENESS_BIN=<janus> scripts/lib/incr-liveness.sh   (without it: builds cmd/janus into a private directory)
# Takes about two seconds. Exit 0: alive; 1: a variable makes the keys differ (named); 2: the check could not run.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
export PATH=/usr/local/go/bin:$PATH
[ ! -d "$HOME/.elan/bin" ] || export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$root/artifacts"
t="$(mktemp -d "$root/artifacts/incr-liveness.XXXXXX")" || exit 2
trap 'rm -rf "$t"' EXIT
mkdir -m 700 "$t/cache"
bin="${JANUS_LIVENESS_BIN:-}"
if [ -z "$bin" ]; then
  go build -o "$t/janus" ./cmd/janus || { echo "incr-liveness: cannot build cmd/janus" >&2; exit 2; }
  bin="$t/janus"
fi
[ -x "$bin" ] || { echo "incr-liveness: $bin is not executable" >&2; exit 2; }
spec=(incr explain --id arm64:Add --kind arm64 --no-fw --proof examples/proofs/Add.lean --arg sym:Add)
# key ENV...: the key of the item under the current environment with the given NAME=value pairs changed (a private result-cache
# directory: nothing shared is read or created)
key() {
  local out
  out="$(env JANUS_CACHE_DIR="$t/cache" "$@" "$bin" "${spec[@]}" 2>&1)" || { echo "incr-liveness: explain failed: $out" >&2; return 1; }
  sed -n 's/^key: \([0-9a-f]\{64\}\)$/\1/p' <<<"$out" | grep . || { echo "incr-liveness: no key in: $out" >&2; return 1; }
}
keyA="$(key)" || exit 2

declare -A allowed=() env0=()
while IFS=$'\t' read -r n _; do [ -z "$n" ] || case "$n" in \#*) ;; *) allowed[$n]=1 ;; esac; done < "$root/scripts/lib/incr-keyed-exports.txt"
perturb=()
if [ -n "${GATE_ENV0_NAMES+x}" ]; then
  for n in $GATE_ENV0_NAMES; do env0[$n]=1; done
  while IFS= read -r n; do
    [ -z "${env0[$n]:-}" ] || continue
    [ -z "${allowed[$n]:-}" ] || continue
    case "$n" in PATH|HOME|PWD|OLDPWD|SHLVL|_|LANG|LC_*|JANUS_CACHE_DIR) continue ;; esac
    perturb+=("$n")
  done < <(compgen -e | sort)
  mode="gate environment: ${#perturb[@]} variables added by the gate"
else
  for n in JANUS_GATE_TREE0 JANUS_LAKEGUARD_PIN JANUS_LAKEGUARD_ROOT JANUS_GATE_AUTO_WHY JANUS_GATE_ROUNDS_LANES JANUS_ROUNDS_LANES \
    JANUS_GATE_AUTO_BUDGET JANUS_VERIFY_MEM_BUDGET_GIB JANUS_JOBS JANUS_LANES JANUS_GATE_PG JANUS_POOL_DIR JANUS_GATE_T0 JANUS_MEMGUARD_CGROUP; do
    perturb+=("$n")
  done
  mode="standalone: the run-specific variables of the gate set to two other values"
fi
args1=(); args2=()
for n in "${perturb[@]}"; do
  v="${!n-}"
  if [ "$n" = TMPDIR ]; then mkdir -p "$t/tmp1" "$t/tmp2"; args1+=("TMPDIR=$t/tmp1"); args2+=("TMPDIR=$t/tmp2"); continue; fi  # (a directory must exist)
  args1+=("$n=${v}~liveness-run-1"); args2+=("$n=${v}~liveness-run-2")
done
keyB1="$(key ${args1[@]+"${args1[@]}"})" || exit 2
keyB2="$(key ${args2[@]+"${args2[@]}"})" || exit 2
rc=0
if [ "$keyA" != "$keyB1" ] || [ "$keyA" != "$keyB2" ]; then
  echo "incr-liveness: FAIL: the key of the same item differs between two gate-like invocations ($mode):"
  echo "  A $keyA"; echo "  B $keyB1"; echo "  B $keyB2"
  for n in "${perturb[@]}"; do
    if [ "$n" = TMPDIR ]; then mkdir -p "$t/tmp3"; k="$(key TMPDIR="$t/tmp3")" || continue; else k="$(key "$n=${!n-}~liveness-probe")" || continue; fi
    [ "$k" = "$keyA" ] || echo "  keyed and run-specific: $n  (add it to incrEnvSkip with its reason, or if it can change what is checked, to scripts/lib/incr-keyed-exports.txt)"
  done
  rc=1
fi
keyC="$(key JANUS_ITEM_TIMEOUT="$((RANDOM + 100000))")" || exit 2
if [ "$keyC" = "$keyA" ]; then echo "incr-liveness: FAIL: control: changing a keyed variable (JANUS_ITEM_TIMEOUT) does not change the key: the check proves nothing"; rc=1; fi
[ "$rc" != 0 ] || echo "incr-liveness: ok: same key under two run-specific environments, key ${keyA:0:12} ($mode); control variable changes it"
exit $rc

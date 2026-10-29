#!/usr/bin/env bash
# Decoder coverage of the arm64 examples (`janus blockers`): every example, extracted as its proof extracts it,
# must decode fully. Shared by .github/workflows/ci.yml and scripts/gate.sh (lane `decoder`).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
[ -x bin/janus ] || CGO_ENABLED=0 go build -o bin/janus ./cmd/janus
. scripts/example-contracts.sh
mapfile -t names < <(sed -n '/^all=(/,/)/p' scripts/verify-examples.sh | tr -d '()' | sed 's/^all=//' | tr ' ' '\n' | grep -v '^$')
[ "${#names[@]}" -gt 0 ] || { echo "no examples found" >&2; exit 1; }
# Every example, extracted as its proof extracts it (the --contract arguments of
# scripts/example-targets.sh), must decode fully, including the LL/SC (LDAXR/STLXR)
# fallback loops Go emits next to the LSE path of sync/atomic callers: the
# store-exclusive is modelled (exclusive monitor + environment choice,
# docs/SOUNDNESS.md). The one exception is MapAccess1Small (runtime.mapaccess1_fast64
# verified on its own): its throw/lock paths reach SVC (Syscall6) and MRS CNTVCT_EL0
# (procyieldAsm), work package C in docs/COVERAGE.md, unreachable under its theorem.
bad=0
bl="${BLOCKERS_OUT:-$(mktemp -d)}"; mkdir -p "$bl"
for n in "${names[@]}"; do
  mapfile -t targs < <(scripts/example-targets.sh "$n")
  args=()
  for ((k = 0; k < ${#targs[@]}; k++)); do
    [ "${targs[k]}" = --contract ] && args+=(--contract "${targs[k+1]}")
  done
  bin/janus blockers artifacts/examples-arm64 "$(example_symbol "$n")" "${args[@]}" > "$bl/blockers-$n.txt" 2>&1 || true
  rej=$(grep -E '^ +0x[0-9a-f]+ +0x[0-9a-f]{8} ' "$bl/blockers-$n.txt" || true)
  if [ "$n" = MapAccess1Small ]; then
    rej=$(echo "$rej" | grep -Ev '^ +0x[0-9a-f]+ +0x(d4000001|d53be0[0-9a-f]{2}) ' || true)
  fi
  if [ -n "$rej" ] || ! grep -q "Summary: 1 symbol(s): " "$bl/blockers-$n.txt"; then
    echo "$n:"; cat "$bl/blockers-$n.txt"; bad=1
  fi
done
[ "$bad" = 0 ] || { echo "unexpected rejected words or extraction failures (above)" >&2; exit 1; }

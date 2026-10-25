#!/usr/bin/env bash
# Red-team round ASL (docs/AUDIT-ASL.md): JanusASL's meaning, the Sail backend patches, and
# concurrent `janus verify`. Writes only to a mktemp directory (and the Go/Lake build caches).
#
#   audit/rt-asl/run.sh            every row
#   RT_ASL_SKIP_GO=1 ...           skip the concurrency tests (about 6 min)
#   DEPS=/srv/janus-asl-deps       the pinned JanusASL toolchain (scripts/asl.sh deps); the Sail
#                                  backend rows are skipped without it
#
# Every row prints its result; a row whose result contradicts its expectation is marked
# BROKEN and the script exits 1.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
here="$root/audit/rt-asl"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
DEPS="${DEPS:-/srv/janus-asl-deps}"
W="$(mktemp -d "${TMPDIR:-/tmp}/rt-asl.XXXXXX")"
trap 'rm -rf "$W"' EXIT

broken=()
row() { # row NAME EXPECT RESULT  (EXPECT ok|blocked|latent: RESULT must start with it)
  local mark=""
  case "$3" in "$2"*) ;; *) mark="   <-- BROKEN"; broken+=("$1") ;; esac
  printf '%-34s %-8s %s%s\n' "$1" "$2" "$3" "$mark"
}

echo "== JanusASL (scripts/asl.sh prove)"
if scripts/asl.sh prove > "$W/prove.log" 2>&1; then
  row "asl-prove (60 theorems)" ok "ok ($(grep -o 'audited [0-9]* theorems' "$W/prove.log"))"
else
  row "asl-prove (60 theorems)" ok "FAILED: $(tail -3 "$W/prove.log" | tr '\n' ' ')"
fi

lean_in_pkg() { (cd "$root/JanusASL" && lake env lean "$@"); }

echo "== A1-A3: what Rel / LinuxEL0Config / the transfers mean (audit/rt-asl/RelMeaning.lean)"
lean_in_pkg "$here/RelMeaning.lean" > "$W/rel.log" 2>&1
n_ok=$(grep -c 'rt-asl ok' "$W/rel.log")
if grep -q 'error' "$W/rel.log" || [ "$n_ok" -ne 8 ]; then
  row "A1-A3 Lean checks" ok "FAILED ($n_ok/8): $(grep -m3 error "$W/rel.log" | tr '\n' ' ')"
else
  for t in Rel.unique Rel.no_two_regs Rel.no_two_flags Rel.ignores_mem rel_cfg_satisfiable Add_pure_asl; do
    row "A $t" ok "ok (kernel-checked, standard axioms)"
  done
fi

echo "== A6: strict audit (names, kinds, axioms, reviewed statements)"
lean_in_pkg "$here/AuditStrict.lean" > "$W/strict.log" 2>&1
grep -o 'STMT .*' "$W/strict.log" > "$W/statements"
if ! grep -q 'strict audit ok: 57 theorems' "$W/strict.log"; then
  row "A6 strict audit" ok "FAILED: $(grep -A5 'FAILED' "$W/strict.log" | tr '\n' ' ')"
elif ! diff -q "$here/asl-statements.golden" "$W/statements" >/dev/null; then
  row "A6 statements = reviewed copy" ok "CHANGED (diff $here/asl-statements.golden; re-review, then update it)"
  diff "$here/asl-statements.golden" "$W/statements" | head -6
else
  row "A6 strict audit" ok "ok (57 theorems present, theorems, standard axioms)"
  row "A6 statements = reviewed copy" ok "ok ($(wc -l < "$W/statements") statements unchanged)"
fi

echo "== A7: independent kernel replay of the JanusASL modules (leanchecker)"
# Every module of JanusASL.Proofs, batched by `scripts/asl.sh replay` (one leanchecker over all of
# JanusASL.Proofs holds several copies of the model's environment at once: ~16 GiB, docs/ASL.md "Memory").
if "$root/scripts/asl.sh" replay > "$W/replay.log" 2>&1 && grep -q '^replay: leanchecker passed on all' "$W/replay.log"; then
  row "A7 leanchecker JanusASL.Proofs" ok "ok (every proof module replayed by the kernel)"
else
  row "A7 leanchecker JanusASL.Proofs" ok "FAILED: $(tail -3 "$W/replay.log" | tr '\n' ' ')"
fi

echo "== A8: Go binaries carry no BTI property (so InGuardedPage = false is faithful)"
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null 2>&1
if [ -f artifacts/examples-arm64 ] && command -v readelf >/dev/null; then
  if readelf -lW artifacts/examples-arm64 | grep -q GNU_PROPERTY || readelf -nW artifacts/examples-arm64 | grep -qi 'AArch64 feature'; then
    row "A8 no GNU_PROPERTY BTI note" blocked "FOUND a GNU property note: pages may be guarded"
  else
    row "A8 no GNU_PROPERTY BTI note" blocked "blocked (artifacts/examples-arm64: no PT_GNU_PROPERTY, no AArch64 feature note)"
  fi
fi

echo "== A5/C2: the Sail Lean backend against Sail's C backend on concrete inputs"
if [ -x "$DEPS/opam/sail-0.20.3-janus/bin/sail" ]; then
  export OPAMROOT="$DEPS/opam"
  eval "$(opam env --switch=sail-0.20.3-janus --set-switch 2>/dev/null)"
  L="$(dirname "$(command -v sail)")/../share/sail/lib"
  mkdir -p "$W/c" "$W/lean/out"
  cp "$here/sail/patches.sail" "$here/sail/main_c.sail" "$W/c/"
  ( cd "$W/c" && sail -c patches.sail main_c.sail -o probe > sail.log 2>&1 &&
    gcc -O1 probe.c "$L/sail.c" "$L/rts.c" "$L/elf.c" "$L/sail_failure.c" "$L/sail_config.c" "$L/cJSON.c" \
      -I"$L" -lgmp -lz -o probe && ./probe > out ) || echo "C backend build failed (see $W/c)"
  ( cd "$W" && cp "$here/sail/patches.sail" lean/ && cd lean &&
    sail --lean patches.sail -o RtProbe --lean-output-dir "$W/lean/out" --lean-force-output > sail.log 2>&1 &&
    cd out/RtProbe &&
    python3 -I "$root/JanusASL/sail/fakereal_sqrt.py" RtProbe/FakeReal.lean &&
    sed -i "s#^git = .*#path = \"$root/JanusASL/.lake/packages/Sail\"#; /^rev = /d" lakefile.toml &&
    cp "$root/JanusASL/lean-toolchain" . && rm -f lake-manifest.json &&
    cp "$here/sail/Probe.lean" RtProbe/Probe.lean && memguard_lake build RtProbe > build.log 2>&1 &&
    lake env lean RtProbe/Probe.lean > "$W/lean/out.txt" 2>&1 ) || echo "Lean backend build failed (see $W/lean)"
  cmpk() { diff <(grep "^$1 " "$W/c/out") <(grep "^$1 " "$W/lean/out.txt") >/dev/null 2>&1; }
  if [ -s "$W/c/out" ] && [ -s "$W/lean/out.txt" ]; then
    for k in probe onebit va vd vg vh vc ve rtz rpow rsq; do
      if cmpk "$k"; then row "A5 $k" ok "ok (Lean = C on $(grep -c "^$k " "$W/c/out") inputs)"
      else row "A5 $k" ok "DIFFERS from the C backend"; fi
    done
    for k in vb vf vcat; do
      if cmpk "$k"; then row "C2 $k (let-bound block)" latent "fixed (Lean = C): update docs/AUDIT-ASL.md C2"
      else row "C2 $k (let-bound block)" latent "latent: Lean drops the block's assignments ($(diff <(grep "^$k " "$W/c/out") <(grep "^$k " "$W/lean/out.txt") | grep -c '^<') of 256 differ)"; fi
    done
  else
    row "A5 backend probes" ok "FAILED to build the probes"
  fi
  # C2 is not reached: no let/var in sail-arm or in JanusASL's own Sail binds a block.
  sa="$DEPS/sail-arm-7d05816/arm-v9.4-a/src"
  hits=$(cat "$sa"/*.sail "$root"/JanusASL/sail/*.sail 2>/dev/null | grep -cE '(let|var) [^=]*= *\{')
  if [ "$hits" = 0 ]; then row "C2 shape in the sliced sources" blocked "blocked (0 let/var-bound blocks in sail-arm + JanusASL/sail)"
  else row "C2 shape in the sliced sources" blocked "FOUND $hits let/var-bound blocks: C2 may be reached"; fi
else
  echo "   (skipped: no pinned toolchain at $DEPS; run scripts/asl.sh deps)"
fi

echo "== A5 fsqrt: FSQRT on the Lean model (sqrt_real replacement) against Sail's C backend"
# audit/rt-asl/sqrt: ~7,000 FSQRT cases (binary32/64, every rounding mode, FZ, DN; exact squares,
# denormals, near-midpoint roots, +-0, +-inf, negatives, NaN payloads), run by JanusASL's Lean model
# (`janus-asl-check --dump-asl`) and by oracle-sail's driver (sail-arm through Sail's C backend);
# V0-V31 and FPSR must be equal on every case.
mkdir -p "$W/fsqrt"
if python3 -I "$here/sqrt/gen_cases.py" > "$W/fsqrt/cases.jsonl" &&
   scripts/oracle-sail.sh build > "$W/fsqrt/osb.log" 2>&1 &&
   JANUS_SAIL_JOBS=8 "$root/oracle-sail/target/release/janus-oracle-sail" < "$W/fsqrt/cases.jsonl" > "$W/fsqrt/c.jsonl" &&
   (cd "$root/JanusASL" && memguard_lake build janus-asl-check > "$W/fsqrt/build.log" 2>&1 &&
    lake exe janus-asl-check --dump-asl "$W/fsqrt/cases.jsonl" > "$W/fsqrt/lean.jsonl" 2> "$W/fsqrt/lean.err"); then
  if python3 -I "$here/sqrt/compare.py" "$W/fsqrt/cases.jsonl" "$W/fsqrt/lean.jsonl" "$W/fsqrt/c.jsonl" > "$W/fsqrt/cmp.txt"; then
    row "A5 fsqrt (Lean = C)" ok "ok ($(head -1 "$W/fsqrt/cmp.txt"))"
  else
    row "A5 fsqrt (Lean = C)" ok "DIFFERS: $(head -3 "$W/fsqrt/cmp.txt" | tr '\n' ' ')"
  fi
else
  row "A5 fsqrt (Lean = C)" ok "FAILED to run (see $W/fsqrt)"
fi

echo "== C1: concurrent janus verify (cmd/janus/concurrency_test.go)"
if [ -z "${RT_ASL_SKIP_GO:-}" ]; then
  if (cd cmd/janus && memguard_run -n go-test -- go test -count=1 -timeout 40m -run 'TestConcurrentVerify|TestForeignFrameworkWriteDetected' .) > "$W/go.log" 2>&1; then
    row "C1 concurrent verifies + blockers" ok "ok (all succeed; foreign write still rejected)"
  else
    row "C1 concurrent verifies + blockers" ok "FAILED: $(grep -m5 -E 'failed|FAIL|unexpected' "$W/go.log" | tr '\n' ' ')"
  fi
else
  echo "   (skipped: RT_ASL_SKIP_GO set)"
fi

if [ ${#broken[@]} -gt 0 ]; then
  echo "BROKEN: ${broken[*]}"; exit 1
fi
echo "rt-asl: all rows as expected"

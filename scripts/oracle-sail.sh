#!/usr/bin/env bash
# Second, authoritative reference oracle: run the Janus oracle corpus on the Sail arm-v9.4-a
# model (Arm's ASL, via rems-project/sail-arm and the sail-aarch64-oracle crate) and report
# three-way agreement Janus vs Sail vs qemu. See docs/ORACLE-SAIL.md.
#
#   scripts/oracle-sail.sh build     build the Sail driver (first build ~30 min: one 166 MB C++ TU)
#   scripts/oracle-sail.sh smoke     build + hand-written sanity cases
#   scripts/oracle-sail.sh run       build + three-way run on the qemu oracle's corpus (default)
#   scripts/oracle-sail.sh regen     regenerate the Sail model from pinned sources (opam + Sail
#                                    0.20.1 + sail-arm) and diff it against the vendored model
#   scripts/oracle-sail.sh crosscheck  build a second driver on the regenerated model (separate
#                                    target dir) and diff its results with the vendored one on
#                                    the corpus (semantic provenance check; needs regen + run)
#
# Environment:
#   QEMU_OUT  qemu oracle output dir with cases.jsonl + hw.jsonl (default artifacts/oracle,
#             written by `scripts/oracle.sh full`; run that first)
#   OUT       output dir (default artifacts/oracle-sail)
#   JOBS      parallelism (default nproc)
#   DEPS      where pinned external sources/toolchains live (default /srv/janus-sail-deps)
#   SAIL_MODEL  vendored | regen  (which model.cpp to build against; default vendored)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mode="${1:-run}"
export PATH="$PATH:/usr/local/go/bin:$HOME/.cargo/bin"
QEMU_OUT="${QEMU_OUT:-$root/artifacts/oracle}"
OUT="${OUT:-$root/artifacts/oracle-sail}"
JOBS="${JOBS:-$(nproc)}"
DEPS="${DEPS:-/srv/janus-sail-deps}"
SAIL_MODEL="${SAIL_MODEL:-vendored}"
here="$root/oracle-sail"

# ---- pins (keep in sync with docs/ORACLE-SAIL.md and oracle-sail/Cargo.toml) ----
CRATE_URL=https://github.com/yufengzjj/sail-aarch64-oracle
CRATE_REV=2dffc81de96705d087b72a57047dd4589c6fb548
CRATE_MODEL_GZ_SHA256=64e3a9292cf2a722a9f2c59f2a379217a33556eb8c84f05501aa560315a0b78c
SAIL_ARM_URL=https://github.com/rems-project/sail-arm
SAIL_ARM_REV=f5bf6c3a2b5df8c7f6f9d3572825ff074e0c6b7c
SAIL_VERSION=0.20.1
OCAML_VERSION=5.2.1

crate="$DEPS/sail-aarch64-oracle"

fetch_crate() {
  if [ ! -d "$crate/.git" ]; then git clone -q "$CRATE_URL" "$crate"; fi
  git -C "$crate" fetch -q origin "$CRATE_REV" 2>/dev/null || true
  git -C "$crate" checkout -q "$CRATE_REV"
  echo "$CRATE_MODEL_GZ_SHA256  $crate/vendor/model.cpp.gz" | sha256sum -c --quiet
}

# The model C++ the driver is built against, instrumented (oracle-sail/instrument_model.py)
# and stored at a stable path: the crate's build.rs re-unpacks its vendored model into
# OUT_DIR on every build script run, which makes cargo rebuild the 166 MB TU each time.
model_dir() {
  local src="$1" dst="$2"
  if [ ! -f "$dst/model.cpp" ] || [ "$src/model.cpp" -nt "$dst/model.cpp" ]; then
    mkdir -p "$dst"
    python3 -I "$here/instrument_model.py" "$src/model.cpp" "$dst/model.cpp.tmp"
    mv "$dst/model.cpp.tmp" "$dst/model.cpp"
    cp "$src/model.h" "$src/model_missing.cpp" "$dst/"
  fi
}

do_build() {
  fetch_crate
  local plain
  case "$SAIL_MODEL" in
    vendored)
      plain="$DEPS/model-vendored-${CRATE_REV:0:7}"
      if [ ! -f "$plain/model.cpp" ]; then
        mkdir -p "$plain"
        gzip -dc "$crate/vendor/model.cpp.gz" > "$plain/model.cpp"
        cp "$crate/vendor/model.h" "$crate/vendor/model_missing.cpp" "$plain/"
      fi ;;
    regen) plain="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/cpp"
      [ -f "$plain/model.cpp" ] || { echo "run '$0 regen' first" >&2; exit 2; } ;;
    *) echo "SAIL_MODEL must be vendored or regen" >&2; exit 2 ;;
  esac
  local inst="$DEPS/model-instrumented-${CRATE_REV:0:7}"
  [ "$SAIL_MODEL" = regen ] && inst="$DEPS/model-instrumented-regen-${SAIL_ARM_REV:0:7}"
  model_dir "$plain" "$inst"
  (cd "$here" &&
    AARCH64_ORACLE_SAIL_MODEL_C="$inst/model.cpp" \
      cargo build --release --locked)
  # The qemu agent's oracle CLI, built from its unmodified sources plus (only while needed) an
  # overlay fixing a comparator panic on >8-byte memory diffs (now fixed upstream in compare.go, so
  # the overlay is empty unless an old checkout is used; see docs/ORACLE-SAIL.md).
  mkdir -p "$here/bin" "$here/go-overlay"
  python3 -I - "$root/oracle/cmd/oracle/compare.go" "$here/go-overlay" <<'PY'
import json, sys, os
src, d = sys.argv[1], sys.argv[2]
s = open(src).read()
bad = '\t\tk := d[:strings.IndexAny(d, ":[")]\n'
good = '\t\tk := d\n\t\tif j := strings.IndexAny(d, ":["); j >= 0 {\n\t\t\tk = d[:j]\n\t\t}\n'
rep = {}
if bad in s:
    open(os.path.join(d, "compare.go"), "w").write(s.replace(bad, good))
    rep[src] = os.path.join(d, "compare.go")
json.dump({"Replace": rep}, open(os.path.join(d, "overlay.json"), "w"))
PY
  (cd "$root/oracle" && go build -overlay "$here/go-overlay/overlay.json" -o "$here/bin/oracle" ./cmd/oracle)
  (cd "$root" && lake build janus-oracle >/dev/null) ||
    echo "warning: lake build janus-oracle failed; using the existing $root/.lake/build/bin/janus-oracle" >&2
}

sail_bin="$here/target/release/janus-oracle-sail"
oracle_bin="$here/bin/oracle"
janus_bin="$root/.lake/build/bin/janus-oracle"

do_smoke() {
  mkdir -p "$OUT"
  python3 -I "$here/smoke.py" > "$OUT/smoke.jsonl"
  "$sail_bin" -j 4 < "$OUT/smoke.jsonl" > "$OUT/smoke.sail.jsonl"
  python3 -I "$here/smoke.py" --check "$OUT/smoke.sail.jsonl"
}

do_run() {
  [ -f "$QEMU_OUT/cases.jsonl" ] && [ -f "$QEMU_OUT/hw.jsonl" ] ||
    { echo "no qemu corpus in $QEMU_OUT: run scripts/oracle.sh full first" >&2; exit 2; }
  mkdir -p "$OUT"/{janus-vs-sail,qemu-vs-sail,janus-vs-qemu}
  # Freeze the corpus and qemu's results (the qemu oracle may be re-run concurrently).
  cp "$QEMU_OUT/cases.jsonl" "$OUT/cases.jsonl"
  cp "$QEMU_OUT/hw.jsonl" "$OUT/qemu.jsonl"
  echo "== Sail: $(wc -l < "$OUT/cases.jsonl") cases"
  JANUS_SAIL_JOBS="$JOBS" "$sail_bin" < "$OUT/cases.jsonl" > "$OUT/sail.jsonl"
  "$sail_bin" --to-model < "$OUT/sail.jsonl" > "$OUT/sail-model.jsonl"

  # DCZID_EL0 is IMPLEMENTATION DEFINED (qemu -cpu max: 7, the Sail model: 8). The corpus
  # carries qemu's value; Janus is checked against each reference with that reference's own
  # value (State.dczid is a free parameter of every theorem), read here with one MRS.
  sail_dczid="$(python3 -I -c 'import json; print(json.dumps({"id": 0, "class": "probe", "word": "0xd53b00e0", "pc": "0x1000000800", "x": ["0x0"] * 31, "sp": "0x1000040800", "nzcv": 0, "seed": 0, "dczid": 0}))' |
    "$sail_bin" -j 1 | python3 -I -c 'import json, sys; print(int(json.loads(sys.stdin.readline())["x"][0], 16))')"
  echo "== Sail DCZID_EL0 = $sail_dczid (corpus/qemu: $(head -1 "$OUT/cases.jsonl" | python3 -I -c 'import json,sys; print(json.loads(sys.stdin.readline()).get("dczid"))'))"
  python3 -I -c '
import json, sys
v = int(sys.argv[1])
for line in sys.stdin:
    if line.strip():
        c = json.loads(line); c["dczid"] = v; sys.stdout.write(json.dumps(c, separators=(",", ":")) + "\n")
' "$sail_dczid" < "$OUT/cases.jsonl" > "$OUT/cases.sail-dczid.jsonl"

  echo "== Janus vs Sail (hardware := Sail, State.dczid := Sail's)"
  cp "$OUT/sail.jsonl" "$OUT/janus-vs-sail/hw.jsonl"
  "$oracle_bin" run -reuse-native -model "$janus_bin" -j "$JOBS" \
    -cases "$OUT/cases.sail-dczid.jsonl" -out "$OUT/janus-vs-sail" > /dev/null
  cp "$OUT/janus-vs-sail/model.jsonl" "$OUT/janus.jsonl"

  echo "== qemu vs Sail (hardware := qemu, model := Sail)"
  cp "$OUT/qemu.jsonl" "$OUT/qemu-vs-sail/hw.jsonl"
  printf '#!/bin/sh\nexec python3 -I %s %s\n' "$here/replay.py" "$OUT/sail-model.jsonl" > "$OUT/qemu-vs-sail/sail-as-model.sh"
  chmod +x "$OUT/qemu-vs-sail/sail-as-model.sh"
  "$oracle_bin" run -reuse-native -model "$OUT/qemu-vs-sail/sail-as-model.sh" -j 1 -shard 100000000 \
    -cases "$OUT/cases.jsonl" -out "$OUT/qemu-vs-sail" > /dev/null

  echo "== Janus vs qemu (same corpus, same Janus build, State.dczid := qemu's)"
  cp "$OUT/qemu.jsonl" "$OUT/janus-vs-qemu/hw.jsonl"
  "$oracle_bin" run -reuse-native -model "$janus_bin" -j "$JOBS" \
    -cases "$OUT/cases.jsonl" -out "$OUT/janus-vs-qemu" > /dev/null

  if grep -q '"verdict":"MISMATCH"' "$OUT/janus-vs-sail/verdicts.jsonl"; then
    echo "== minimize Janus-vs-Sail mismatches (Sail as the runner)"
    JANUS_SAIL_JOBS=1 "$oracle_bin" minimize -qemu "" -runner "$sail_bin" -model "$janus_bin" \
      -out "$OUT/janus-vs-sail" -max 200 > /dev/null
    echo "minimal reproductions: $OUT/janus-vs-sail/repro.md"
  fi
  echo "== Sail-only: SP-based accesses with a misaligned SP (qemu does not check SP alignment)"
  mkdir -p "$OUT/spalign"
  python3 -I "$here/spalign.py" "$OUT/cases.sail-dczid.jsonl" > "$OUT/spalign/cases.in.jsonl"
  JANUS_SAIL_JOBS=1 "$oracle_bin" run -qemu "" -runner "$sail_bin" -model "$janus_bin" -j "$JOBS" \
    -cases "$OUT/spalign/cases.in.jsonl" -out "$OUT/spalign" > /dev/null
  sed -n 5p "$OUT/spalign/summary.md"
  python3 -I "$here/threeway.py" "$OUT" > /dev/null
  sed -n '1,12p' "$OUT/threeway.md"
  echo "report: $OUT/threeway.md  soundness cases: $OUT/soundness.jsonl"
}

do_regen() {
  fetch_crate
  local sa="$DEPS/sail-arm" wt="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}"
  [ -d "$sa/.git" ] || git clone -q "$SAIL_ARM_URL" "$sa"
  [ -d "$wt" ] || git -C "$sa" worktree add -q "$wt" "$SAIL_ARM_REV"
  export OPAMROOT="$DEPS/opam" OPAMYES=1
  if ! opam switch list 2>/dev/null | grep -q "sail-$SAIL_VERSION"; then
    command -v opam >/dev/null || apt-get install -y opam z3 libgmp-dev pkg-config
    opam init --bare --disable-sandboxing -n
    opam switch create "sail-$SAIL_VERSION" "ocaml-base-compiler.$OCAML_VERSION"
    opam install -y "sail.$SAIL_VERSION"
  fi
  eval "$(opam env --switch="sail-$SAIL_VERSION")"
  sail --version | grep -q "$SAIL_VERSION"
  local keep=()
  for f in $(grep -oE '^function [a-z_0-9]+' "$crate/sail/harness.sail" | awk '{print $2}'); do
    keep+=(--c-preserve "$f")
  done
  cd "$wt/arm-v9.4-a"
  mkdir -p cpp
  # README Step 2 of the crate, with --c-preserve for every harness function.
  sail --cpp --cpp-namespace sail_aarch64 --c-no-main -O --Oconstant-fold --memo-z3 "${keep[@]}" \
    src/prelude.sail src/decode_start.sail src/builtins.sail src/v8_base.sail src/stubs.sail \
    src/interrupts.sail src/interface.sail src/devices.sail src/impdefs.sail src/mem.sail \
    src/sysregs_autogen.sail src/sysregs.sail src/reset.sail src/instrs32.sail src/instrs64.sail \
    src/instrs64_sve.sail src/instrs64_sme.sail src/decode_end.sail src/fetch.sail \
    src/map_clauses.sail src/event_clauses.sail "$crate/sail/harness.sail" -o cpp/model
  python3 -I "$crate/scripts/fix_cpp_model.py" cpp/model.h cpp/model.cpp
  local v="$DEPS/model-vendored-${CRATE_REV:0:7}"
  [ -f "$v/model.cpp" ] || { mkdir -p "$v"; gzip -dc "$crate/vendor/model.cpp.gz" > "$v/model.cpp"; }
  for f in model.cpp model.h model_missing.cpp; do
    if cmp -s "cpp/$f" "$v/$f" 2>/dev/null || cmp -s "cpp/$f" "$crate/vendor/$f"; then
      echo "regen: $f identical to the vendored copy"
    else
      echo "regen: $f DIFFERS from the vendored copy"
    fi
  done
}

do_crosscheck() {
  [ -f "$OUT/cases.jsonl" ] && [ -f "$OUT/sail.jsonl" ] || { echo "run '$0 run' first" >&2; exit 2; }
  local plain="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/cpp"
  [ -f "$plain/model.cpp" ] || { echo "run '$0 regen' first" >&2; exit 2; }
  local inst="$DEPS/model-instrumented-regen-${SAIL_ARM_REV:0:7}"
  model_dir "$plain" "$inst"
  (cd "$here" && CARGO_TARGET_DIR="$DEPS/target-regen" AARCH64_ORACLE_SAIL_MODEL_C="$inst/model.cpp" \
    cargo build --release --locked)
  JANUS_SAIL_JOBS="$JOBS" "$DEPS/target-regen/release/janus-oracle-sail" < "$OUT/cases.jsonl" > "$OUT/sail-regen.jsonl"
  if cmp -s "$OUT/sail.jsonl" "$OUT/sail-regen.jsonl"; then
    echo "crosscheck: regenerated model (sail-arm ${SAIL_ARM_REV:0:7}, Sail $SAIL_VERSION) and vendored model agree on all $(wc -l < "$OUT/cases.jsonl") cases"
  else
    echo "crosscheck: results DIFFER on $(diff "$OUT/sail.jsonl" "$OUT/sail-regen.jsonl" | grep -c '^<') cases (diff $OUT/sail.jsonl $OUT/sail-regen.jsonl)"
    exit 1
  fi
}

case "$mode" in
  build) do_build ;;
  crosscheck) do_crosscheck ;;
  smoke) do_build; do_smoke ;;
  run)   do_build; do_smoke; do_run ;;
  regen) do_regen ;;
  *) echo "usage: $0 build|smoke|run|regen|crosscheck" >&2; exit 2 ;;
esac

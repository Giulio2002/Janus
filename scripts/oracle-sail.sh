#!/usr/bin/env bash
# Second, authoritative reference oracle: run the Janus oracle corpus on the Sail arm-v9.4-a
# model (Arm's ASL, via rems-project/sail-arm and the sail-aarch64-oracle crate) and report
# three-way agreement Janus vs Sail vs qemu. See docs/ORACLE-SAIL.md.
#
#   scripts/oracle-sail.sh build     build the Sail driver (the 166 MB model is built as SAIL_SPLIT_PARTS parallel C++ TUs, see SAIL_SPLIT)
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
#   SAIL_SPLIT  1 (default): build the model as SAIL_SPLIT_PARTS (48) translation units in parallel
#             (oracle-sail/split_model.py + a patched copy of the pinned crate, oracle-sail/split_crate.py);
#             0: the original single translation unit (serial, ~24 min). Part of the driver cache key.
#   KEEP      what `run` leaves in OUT (scripts/lib/artifacts.sh): by default the reports, the
#             compressed corpus, results and verdicts, the MISMATCH verdicts; the per-comparison
#             copies of the corpus and the derived dumps are removed. KEEP=zst compresses
#             everything, KEEP=1 keeps every dump raw. QEMU_OUT may hold compressed (.zst) files.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
# shellcheck source=lib/artifacts.sh
. "$root/scripts/lib/artifacts.sh"
memguard_self "$@"
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
# Integrity (oracle-sail/dir_digest.py): the instrumented model, model.h and model_missing.cpp carry a record
# (.inst-complete) of their SHA-256, of the source model they were made from and of instrument_model.py; the parts
# directory a record (.complete) of the SHA-256 of every part, model.h and model_missing.cpp, of the instrumented
# model and of split_model.py. Both are re-hashed on EVERY use (about 200 MB, ~1 s), not only compared by mtime: a
# stale, edited, extended or truncated directory is regenerated from the source model, never built silently.
sha256_of() { python3 -I -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }

model_dir() {
  local src="$1" dst="$2" sd ins
  sd=$(python3 -I "$here/dir_digest.py" digest "$src/model.cpp" "$src/model.h" "$src/model_missing.cpp")
  ins=$(sha256_of "$here/instrument_model.py")
  if [ -f "$dst/model.cpp" ] && [ ! "$src/model.cpp" -nt "$dst/model.cpp" ] &&
     python3 -I "$here/dir_digest.py" check "$dst/.inst-complete" "$dst/model.cpp" "$dst/model.h" "$dst/model_missing.cpp" -- "src=$sd" "instrument=$ins"; then
    return 0
  fi
  [ ! -f "$dst/model.cpp" ] || echo "oracle-sail: instrumented model $dst is stale or does not match its record: regenerating" >&2
  mkdir -p "$dst"
  rm -f "$dst/.inst-complete"
  python3 -I "$here/instrument_model.py" "$src/model.cpp" "$dst/model.cpp.tmp"
  mv "$dst/model.cpp.tmp" "$dst/model.cpp"
  cp "$src/model.h" "$src/model_missing.cpp" "$dst/"
  python3 -I "$here/dir_digest.py" record "$dst/.inst-complete" "$dst/model.cpp" "$dst/model.h" "$dst/model_missing.cpp" -- "src=$sd" "instrument=$ins"
}

# ---- parallel model build (docs/ORACLE-SAIL.md "Split build") ----
# The model is one 170 MB C++ TU that g++ compiles serially (~24 min). With SAIL_SPLIT=1 it is cut at
# top-level item boundaries into SAIL_SPLIT_PARTS TUs (split_model.py, every layout assumption asserted) and the pinned
# crate's build.rs, patched to take the parts (build.rs.patch, both hashes pinned), compiles them in parallel.
SAIL_SPLIT="${SAIL_SPLIT:-1}"
SAIL_SPLIT_PARTS=48
BUILD_RS_SHA256=6e47e363dca372dcc5a9d93036d35cb9714722886b936a39d0929208f963787f
BUILD_RS_PATCHED_SHA256=916d07721fb7756b1822728fb76d35cbd1bab44d825a06470a61b8ae958c1a19

# split_parts INSTRUMENTED_DIR -> prints the dir holding model_part_*.cpp (+ model.h), made once per model/splitter
split_parts() {
  local inst="$1" tag dst idig sm
  sm=$(sha256_of "$here/split_model.py")
  tag=${sm:0:12}
  dst="$inst/parts-$SAIL_SPLIT_PARTS-$tag"
  idig=$(python3 -I "$here/dir_digest.py" digest "$inst/model.cpp" "$inst/model.h" "$inst/model_missing.cpp")
  if [ -f "$dst/.complete" ] && [ ! "$inst/model.cpp" -nt "$dst/.complete" ] &&
     python3 -I "$here/dir_digest.py" check "$dst/.complete" "$dst" -- "inst=$idig" "split_model=$sm" "parts=$SAIL_SPLIT_PARTS"; then
    echo "$dst"; return 0
  fi
  [ ! -e "$dst" ] || echo "oracle-sail: parts $dst are stale or do not match their record: regenerating" >&2
  rm -rf "$dst.tmp.$$"; mkdir -p "$dst.tmp.$$"
  python3 -I "$here/split_model.py" "$inst/model.cpp" "$dst.tmp.$$" "$SAIL_SPLIT_PARTS" >&2
  cp "$inst/model.h" "$inst/model_missing.cpp" "$dst.tmp.$$/"
  python3 -I "$here/dir_digest.py" record "$dst.tmp.$$/.complete" "$dst.tmp.$$" -- "inst=$idig" "split_model=$sm" "parts=$SAIL_SPLIT_PARTS"
  rm -rf "$dst"; mv "$dst.tmp.$$" "$dst"
  echo "$dst"
}
# split_crate_cfg -> prints the cargo --config file that swaps in the patched crate copy
split_crate_cfg() {
  python3 -I "$here/split_crate.py" "$crate" "$DEPS/crate-split-${CRATE_REV:0:7}-${BUILD_RS_PATCHED_SHA256:0:8}" \
    "$BUILD_RS_SHA256" "$BUILD_RS_PATCHED_SHA256" "$here/build.rs.patch"
}

# ---- build cache for the driver (docs/SOUNDNESS.md "Build caches") ----
# The driver is a pure function of the pinned crate and model, the instrumenter, oracle-sail's
# sources and lockfile, the Rust and C++ toolchains and their environment (oracle-sail/cache_key.py).
# Its cache entry (scripts/lib/bcache.py kind "sail") holds the one binary, a SHA-256 manifest and an
# HMAC of it under the per-user key; both are checked on every use, and an entry that fails either is
# ignored and replaced by a rebuild. SAIL_CACHE=<dir> picks the directory (default: $ASL_CACHE, else
# /srv/janus-asl-cache if it exists, else ~/.cache/janus/asl); SAIL_CACHE=off disables it;
# SAIL_CACHE_READONLY=1 never writes.
SAIL_CARGO_FLAGS="--release --locked"
SAIL_DRIVER_REL=target/release/janus-oracle-sail
case "${JANUS_ASL_CACHE:-}" in ''|0|off|no|false) ;; *) : "${ASL_CACHE:=$JANUS_ASL_CACHE}" ;; esac
if [ -z "${SAIL_CACHE+x}" ]; then
  if [ -n "${ASL_CACHE+x}" ]; then SAIL_CACHE="$ASL_CACHE"
  elif [ -d /srv/janus-asl-cache ]; then SAIL_CACHE=/srv/janus-asl-cache
  else SAIL_CACHE="${XDG_CACHE_HOME:-$HOME/.cache}/janus/asl"; fi
fi
[ "$SAIL_CACHE" = off ] && SAIL_CACHE=""
# JANUS_ASL_CACHE=0 (also off/no/false): the opt-out for a forced cold build (the full gate before a push to main)
case "${JANUS_ASL_CACHE:-}" in 0|off|no|false) SAIL_CACHE="" ;; esac

sail_cache_key() {  # sail_cache_key MODEL_CPP_OR_EMPTY
  local mf=()
  [ -n "$1" ] && mf=(--model-file "$1")
  python3 -I "$here/cache_key.py" "$root" "${mf[@]}" --pins "crate_rev=$CRATE_REV" "crate_model_gz_sha256=$CRATE_MODEL_GZ_SHA256" \
    "sail_model=$SAIL_MODEL" "sail_split=$SAIL_SPLIT:$SAIL_SPLIT_PARTS:$BUILD_RS_PATCHED_SHA256" "cargo_flags=$SAIL_CARGO_FLAGS" "sail_arm_rev=$SAIL_ARM_REV" "sail_version=$SAIL_VERSION"
}

do_build() {
  local ckey="" crc=0 cout inp
  if [ -n "$SAIL_CACHE" ]; then
    if [ "$SAIL_MODEL" = regen ]; then
      local rm_="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/cpp/model.cpp"
      [ -f "$rm_" ] && ckey=$(sail_cache_key "$rm_") || true
    else
      ckey=$(sail_cache_key "")
    fi
  fi
  if [ -n "$ckey" ]; then
    mkdir -p "$here/target/release"
    cout=$(python3 -I "$root/scripts/lib/bcache.py" fetch sail "$SAIL_CACHE" "$ckey" "$here") || crc=$?
    case $crc in
      0) echo "sail cache: driver $ckey: $cout ($SAIL_CACHE)" ;;
      2) echo "sail cache: no entry for driver $ckey ($SAIL_CACHE); building" ;;
      3) echo "sail cache: the entry for driver $ckey was REJECTED (above); building from source" ;;
      *) echo "sail cache: not usable here (above); building from source" ;;
    esac
  fi
  if [ "$crc" != 0 ] || [ -z "$ckey" ]; then
    do_build_driver
    if [ -n "$ckey" ] && [ "${SAIL_CACHE_READONLY:-0}" != 1 ] && [ -f "$here/$SAIL_DRIVER_REL" ]; then
      mkdir -p "$SAIL_CACHE"
      inp=$(mktemp "${TMPDIR:-/tmp}/sail-cache-inputs.XXXXXX")
      python3 -I "$here/cache_key.py" "$root" --show --pins "crate_rev=$CRATE_REV" "sail_model=$SAIL_MODEL" > "$inp" || true
      cout=$(printf '%s\0' "$SAIL_DRIVER_REL" | python3 -I "$root/scripts/lib/bcache.py" store sail "$SAIL_CACHE" "$ckey" "$here" --inputs "$inp") &&
        echo "sail cache: driver $ckey: $cout" || echo "sail cache: not stored"
      rm -f "$inp"
    fi
  fi
  # The qemu oracle CLI (its comparator is shared) and the framework's oracle: incremental builds.
  mkdir -p "$here/bin"
  (cd "$root/oracle" && go build -o "$here/bin/oracle" ./cmd/oracle)
  (cd "$root" && memguard_lake build janus-oracle >/dev/null) ||
    echo "warning: lake build janus-oracle failed; using the existing $root/.lake/build/bin/janus-oracle" >&2
}

do_build_driver() {
  fetch_crate
  local plain
  case "$SAIL_MODEL" in
    vendored)
      plain="$DEPS/model-vendored-${CRATE_REV:0:7}"
      # the unpacked vendored model is checked against the pinned (CRATE_MODEL_GZ_SHA256) archive and the pinned
      # checkout's model.h / model_missing.cpp on every build, not only when it is first extracted
      if [ ! -f "$plain/model.cpp" ] ||
         [ "$(gzip -dc "$crate/vendor/model.cpp.gz" | sha256sum | cut -d' ' -f1)" != "$(sha256_of "$plain/model.cpp")" ] ||
         ! cmp -s "$crate/vendor/model.h" "$plain/model.h" || ! cmp -s "$crate/vendor/model_missing.cpp" "$plain/model_missing.cpp"; then
        [ ! -f "$plain/model.cpp" ] || echo "oracle-sail: $plain does not match the pinned vendored model: re-extracting" >&2
        mkdir -p "$plain"
        gzip -dc "$crate/vendor/model.cpp.gz" > "$plain/model.cpp.tmp.$$" && mv "$plain/model.cpp.tmp.$$" "$plain/model.cpp"
        cp "$crate/vendor/model.h" "$crate/vendor/model_missing.cpp" "$plain/"
      fi ;;
    regen) plain="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/cpp"
      [ -f "$plain/model.cpp" ] || { echo "run '$0 regen' first" >&2; exit 2; } ;;
    *) echo "SAIL_MODEL must be vendored or regen" >&2; exit 2 ;;
  esac
  local inst="$DEPS/model-instrumented-${CRATE_REV:0:7}"
  [ "$SAIL_MODEL" = regen ] && inst="$DEPS/model-instrumented-regen-${SAIL_ARM_REV:0:7}"
  model_dir "$plain" "$inst"
  case "$SAIL_SPLIT" in
    0) (cd "$here" &&
         AARCH64_ORACLE_SAIL_MODEL_C="$inst/model.cpp" \
           cargo build $SAIL_CARGO_FLAGS) ;;
    1) local parts cfg
       parts=$(split_parts "$inst"); cfg=$(split_crate_cfg)
       (cd "$here" &&
         AARCH64_ORACLE_SAIL_MODEL_C="$parts/model_part_00.cpp" AARCH64_ORACLE_SAIL_MODEL_INC="$parts" \
         AARCH64_ORACLE_SAIL_MODEL_PARTS="$parts" \
           cargo build $SAIL_CARGO_FLAGS --config "$cfg") ;;
    *) echo "SAIL_SPLIT must be 0 or 1" >&2; exit 2 ;;
  esac
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

prune_run() {
  art_prune --copies "$OUT"/janus-vs-sail "$OUT"/qemu-vs-sail "$OUT"/janus-vs-qemu "$OUT"/spalign
  art_prune "$OUT"
}

do_run() {
  art_exists "$QEMU_OUT/cases.jsonl" && art_exists "$QEMU_OUT/hw.jsonl" ||
    { echo "no qemu corpus in $QEMU_OUT: run scripts/oracle.sh full first" >&2; exit 2; }
  mkdir -p "$OUT"/{janus-vs-sail,qemu-vs-sail,janus-vs-qemu}
  # However the run ends, the multi-GB dumps are pruned (KEEP=1 keeps them).
  trap prune_run EXIT
  # Freeze the corpus and qemu's results (the qemu oracle may be re-run concurrently).
  art_cat "$QEMU_OUT/cases.jsonl" > "$OUT/cases.jsonl"
  art_cat "$QEMU_OUT/hw.jsonl" > "$OUT/qemu.jsonl"
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
  # sail-arm stubs the exclusive monitor (IsExclusiveLocal/IsExclusiveGlobal/IsExclusiveVA are
  # TRUE: every store-exclusive passes), so Janus runs with --monitor-stub: each store-exclusive
  # first gets a monitor marking its own bytes, which makes "pass" one of the model's outcomes.
  # The Open-state rule (fail) is checked against qemu only (docs/ORACLE-SAIL.md).
  janus_stub="$OUT/janus-vs-sail/janus-monitor-stub.sh"
  printf '#!/bin/sh\nexec %s --monitor-stub "$@"\n' "$janus_bin" > "$janus_stub"
  chmod +x "$janus_stub"
  cp "$OUT/sail.jsonl" "$OUT/janus-vs-sail/hw.jsonl"
  "$oracle_bin" run -reuse-native -model "$janus_stub" -j "$JOBS" \
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
    JANUS_SAIL_JOBS=1 "$oracle_bin" minimize -qemu "" -runner "$sail_bin" -model "$janus_stub" \
      -out "$OUT/janus-vs-sail" -max 200 > /dev/null
    echo "minimal reproductions: $OUT/janus-vs-sail/repro.md"
  fi
  echo "== Sail-only: SP-based accesses with a misaligned SP (qemu does not check SP alignment)"
  mkdir -p "$OUT/spalign"
  python3 -I "$here/spalign.py" "$OUT/cases.sail-dczid.jsonl" > "$OUT/spalign/cases.in.jsonl"
  if [ -s "$OUT/spalign/cases.in.jsonl" ]; then
    JANUS_SAIL_JOBS=1 "$oracle_bin" run -qemu "" -runner "$sail_bin" -model "$janus_stub" -j "$JOBS" \
      -cases "$OUT/spalign/cases.in.jsonl" -out "$OUT/spalign" > /dev/null
    sed -n 5p "$OUT/spalign/summary.md"
  else
    echo "(no SP-based accesses in this corpus: spalign skipped)"
  fi
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
  art_exists "$OUT/cases.jsonl" && art_exists "$OUT/sail.jsonl" || { echo "run '$0 run' first" >&2; exit 2; }
  # The corpus and Sail's results may be compressed (scripts/lib/artifacts.sh): decompressed for
  # the comparison, removed again afterwards.
  trap art_cleanup EXIT
  art_input "$OUT/cases.jsonl" >/dev/null
  art_input "$OUT/sail.jsonl" >/dev/null
  local plain="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/cpp"
  [ -f "$plain/model.cpp" ] || { echo "run '$0 regen' first" >&2; exit 2; }
  local inst="$DEPS/model-instrumented-regen-${SAIL_ARM_REV:0:7}"
  model_dir "$plain" "$inst"
  (cd "$here" && CARGO_TARGET_DIR="$DEPS/target-regen" AARCH64_ORACLE_SAIL_MODEL_C="$inst/model.cpp" \
    cargo build --release --locked)
  JANUS_SAIL_JOBS="$JOBS" "$DEPS/target-regen/release/janus-oracle-sail" < "$OUT/cases.jsonl" > "$OUT/sail-regen.jsonl"
  if cmp -s "$OUT/sail.jsonl" "$OUT/sail-regen.jsonl"; then
    echo "crosscheck: regenerated model (sail-arm ${SAIL_ARM_REV:0:7}, Sail $SAIL_VERSION) and vendored model agree on all $(wc -l < "$OUT/cases.jsonl") cases"
    [ "$(art_mode)" = raw ] || rm -f "$OUT/sail-regen.jsonl"
  else
    echo "crosscheck: results DIFFER on $(diff "$OUT/sail.jsonl" "$OUT/sail-regen.jsonl" | grep -c '^<') cases (diff $OUT/sail.jsonl $OUT/sail-regen.jsonl)"
    # Keep the regenerated results for the diff (compressed unless KEEP=1).
    [ "$(art_mode)" = raw ] || art_zstd "$OUT/sail-regen.jsonl" || true
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

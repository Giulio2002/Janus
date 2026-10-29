#!/usr/bin/env bash
# JanusASL: Janus' AArch64 model against Arm's ASL inside Lean (docs/ASL.md).
#
#   scripts/asl.sh deps    install the pinned toolchain into $DEPS: an opam root with Sail 0.20.3
#                          plus 8 upstream Lean-backend commits and JanusASL's backend fixes (JanusASL/sail/*.patch),
#                          the slicing plugin, sail-arm at the pin, lean-sail at the pin
#   scripts/asl.sh gen     slice sail-arm to the Janus subset and generate Lean (JanusASL/ArmASL*),
#                          then compare with the vendored copy (GEN_UPDATE=1 replaces the vendored copy)
#   scripts/asl.sh restore unpack the vendored model (if needed) and copy its build from ASL_CACHE (no build)
#   scripts/asl.sh model   unpack the vendored model (if needed) and build only ArmASL (lake; uses ASL_CACHE)
#   scripts/asl.sh build   unpack the vendored model (if needed) and build JanusASL (lake)
#   scripts/asl.sh check   build + `lake exe janus-asl-check` on the oracle corpus (default)
#   scripts/asl.sh prove   build the proofs (JanusASL.Proofs) and audit their axioms
#   scripts/asl.sh replay  kernel-replay every JanusASL module with leanchecker, in batches
#   scripts/asl.sh verify  build + `janus verify --asl` on the shipped Add, Max, Mul64 and Add128
#                          proofs: their ASL corollaries, derived from the artifacts (docs/ASL.md)
#
# Environment:
#   DEPS     pinned external sources/toolchains (default /srv/janus-asl-deps)
#   CASES    corpus (default artifacts/oracle/cases.jsonl; made by `scripts/oracle.sh full` if missing)
#   OUT      output dir for the check (default artifacts/asl)
#   KEEP     1: keep the check's verdicts.jsonl raw (default: compressed to verdicts.jsonl.zst,
#            MISMATCH verdicts in mismatches.jsonl; scripts/lib/artifacts.sh). CASES may be
#            compressed (.zst next to the named file).
#   JOBS     parallel tasks for the check (default nproc)
#   ASL_CACHE          the shared build cache (a directory; default /srv/janus-asl-cache if it exists,
#                      else ~/.cache/janus/asl; "off" or empty disables it). Before building,
#                      the generated model's build (and the lean-sail package) is copied from
#                      the cache entry for this model and toolchain, if there is one; after a
#                      build, it is stored there if not. Entries are keyed by a hash of every input
#                      (JanusASL/tools/asl_cache_key.py: the vendored tarball, the splitter, the
#                      toolchain by content, the lean-sail manifest entry, the lakefile settings that
#                      reach ArmASL's modules, the compiler environment, the machine), carry a
#                      SHA-256 manifest AND an HMAC of it under a per-user key
#                      (scripts/lib/bcache.py; ~/.cache/janus/asl-cache-key/asl-cache.key), both checked on every
#                      copy, and are published atomically under a per-key lock, so worktrees and CI
#                      runners share one build of the ~45 min model. A missing, unsigned, tampered
#                      or incomplete entry is rebuilt from source, never used.
#                      The same directory also caches every JanusASL and Janus module's build
#                      (ASL_CACHE/mods, JanusASL/tools/asl_mod_cache.py): one entry per module,
#                      keyed by what Lake traces (source, imports' keys, package settings,
#                      toolchain), restored before and published after the JanusASL build.
#   JANUS_ASL_CACHE=0  force a cold build: neither reads nor writes the cache (also off/no/false)
#   ASL_CACHE_READONLY=1   use the cache but never write to it
#   ASL_CACHE_MAX      size budget of ASL_CACHE (default 15G; off: none), kept after every publish
#                      by `asl_mod_cache.py gc` (least recently restored first; unreferenced
#                      ArmASL entries always; nothing used in the last hour)
#   GEN      work directory of `gen` (default $DEPS/gen)
#   ASL_MEM_GB   memory budget of `build`/`prove` (default: the smaller of 24 and 60% of MemAvailable)
#   ASL_JOBS     Lean processes Lake runs at once (default ASL_MEM_GB / ASL_JOB_GB, at least 1)
#   ASL_JOB_GB   peak of the largest single Lean process of the build (default 8, docs/ASL.md "Memory")
#   REPLAY_BATCH modules per leanchecker process in `replay` (default 4)
#   ASL_EXAMPLES  examples for `verify` (default "Add Max Mul64 Add128")
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
# shellcheck source=lib/artifacts.sh
. "$root/scripts/lib/artifacts.sh"
memguard_self "$@"
mode="${1:-check}"
DEPS="${DEPS:-/srv/janus-asl-deps}"
CASES="${CASES:-$root/artifacts/oracle/cases.jsonl}"
OUT="${OUT:-$root/artifacts/asl}"
JOBS="${JOBS:-$(nproc)}"
pkg="$root/JanusASL"
here="$pkg/sail"

# The build cache is on by default (docs/SOUNDNESS.md "Build caches"): ASL_CACHE=<dir> picks it,
# ASL_CACHE=off (or empty) disables it, unset means /srv/janus-asl-cache if that exists, else
# ~/.cache/janus/asl. Entries are content-keyed, HMAC-signed and hash-checked on every use.
# JANUS_ASL_CACHE=<dir> is an alias of ASL_CACHE (scripts/gate.sh forwards it); 0/off/no/false is the opt-out below.
case "${JANUS_ASL_CACHE:-}" in ''|0|off|no|false) ;; *) : "${ASL_CACHE:=$JANUS_ASL_CACHE}" ;; esac
if [ "${ASL_CACHE-unset}" = unset ]; then
  if [ -d /srv/janus-asl-cache ]; then ASL_CACHE=/srv/janus-asl-cache
  else ASL_CACHE="${XDG_CACHE_HOME:-$HOME/.cache}/janus/asl"; fi
fi
[ "$ASL_CACHE" = off ] && ASL_CACHE=""
# JANUS_ASL_CACHE=0 (also off/no/false) forces a cold build and publishes nothing: the full gate before a
# push to main uses it. It wins over ASL_CACHE.
case "${JANUS_ASL_CACHE:-}" in 0|off|no|false) ASL_CACHE="" ;; esac
export ASL_CACHE

# ---- pins (keep in sync with docs/ASL.md) ----
SAIL_URL=https://github.com/rems-project/sail
SAIL_TAG=0.20.3
SAIL_REV=0.20.3                 # tag; the patch adds later upstream Lean-backend fixes + JanusASL's
SAIL_ARM_URL=https://github.com/rems-project/sail-arm
SAIL_ARM_REV=7d0581642d0e3aaca367bbc5650aca7c53057543   # upstream master (includes the Lean MOD fix)
OCAML_VERSION=5.2.1
SWITCH=sail-0.20.3-janus
VENDOR="$pkg/vendor/ArmASL.tar.gz"
# split_lean.py: parts of at most this many bytes (a larger declaration gets a part of its own)
PART_BYTES=150000

export OPAMROOT="$DEPS/opam" OPAMYES=1
sailarm="$DEPS/sail-arm-${SAIL_ARM_REV:0:7}/arm-v9.4-a/src"

do_deps() {
  mkdir -p "$DEPS"
  command -v opam >/dev/null || apt-get install -y opam z3 libgmp-dev pkg-config
  if [ ! -d "$DEPS/sail-arm-${SAIL_ARM_REV:0:7}" ]; then
    [ -d "$DEPS/sail-arm/.git" ] || git clone -q "$SAIL_ARM_URL" "$DEPS/sail-arm"
    git -C "$DEPS/sail-arm" worktree add -q --detach "$DEPS/sail-arm-${SAIL_ARM_REV:0:7}" "$SAIL_ARM_REV"
  fi
  local src="$DEPS/sail-$SAIL_TAG-janus"
  if [ ! -d "$src" ]; then
    [ -d "$DEPS/sail/.git" ] || git clone -q "$SAIL_URL" "$DEPS/sail"
    git -C "$DEPS/sail" worktree add -q --detach "$src" "$SAIL_REV"
    git -C "$src" apply "$here/sail-0.20.3-upstream-backports.patch"   # 8 upstream Lean-backend commits
    git -C "$src" apply "$here/sail-0.20.3-janus-lean-fixes.patch"     # JanusASL's backend fixes
  fi
  [ -d "$OPAMROOT" ] || opam init --bare --disable-sandboxing -n
  if ! opam switch list 2>/dev/null | grep -q "$SWITCH"; then
    opam switch create "$SWITCH" --empty
    opam install --switch="$SWITCH" "ocaml-base-compiler.$OCAML_VERSION"
    opam pin add -n -k path --switch="$SWITCH" "$src"
    opam install --switch="$SWITCH" sail
  fi
  eval "$(opam env --switch="$SWITCH" --set-switch)"
  (cd "$here/plugin" && dune build ./sail_plugin_janus.cmxs)
}

do_gen() {
  do_deps
  eval "$(opam env --switch="$SWITCH" --set-switch)"
  local w="${GEN:-$DEPS/gen}"
  rm -rf "$w/sliced" "$w/out"; mkdir -p "$w/sliced" "$w/out"
  python3 -I "$here/slice.py" "$sailarm" "$w/sliced" "$here/keep.txt" > "$w/slice-stats.json"
  local S="$w/sliced"
  local files=("$S/prelude.sail" "$S/decode_start.sail" "$S/builtins.sail" "$S/v8_base.sail"
    "$here/janus_regs.sail" "$S/stubs.sail" "$S/interrupts.sail" "$S/interface.sail" "$S/devices.sail"
    "$S/impdefs.sail" "$S/mem.sail" "$S/sysregs_autogen.sail" "$S/sysregs.sail" "$S/reset.sail"
    "$S/instrs32.sail" "$S/instrs64.sail" "$S/instrs64_sve.sail" "$S/instrs64_sme.sail"
    "$S/decode_end.sail" "$S/fetch.sail" "$S/map_clauses.sail" "$S/event_clauses.sail"
    "$here/harness.sail" "$S/termination_measures.sail")
  # Lake fetches lean-sail itself; the generated lakefile is not used (JanusASL/lakefile.toml is).
  (cd "$w" && ulimit -s unlimited &&
    sail --plugin "$here/plugin/_build/default/sail_plugin_janus.cmxs" --janus-lean \
      --janus-roots "$(grep -v '^#' "$here/roots.txt" | tr '\n' ' ')" \
      --splice "$here/janus_splice.sail" --splice "$S/janus_pac_splice.sail" --splice "$S/janus_sysreg_splice.sail" --lean-import-file "$here/JanusExtras.lean" --lean-partial-function Reduce__1 \
      --lean-output-dir "$w/out" --lean-force-output --lean-single-file --lean-line-width 100000 \
      -o ArmASL "${files[@]}" > "$w/sail.log" 2>&1) ||
    { tail -30 "$w/sail.log"; exit 1; }
  # The slice paths are recorded in assertion messages; make them independent of $DEPS.
  sed -i "s#$S/#sail-arm/arm-v9.4-a/src/#g" "$w/out/ArmASL/ArmASL.lean"
  # integer_update_subrange without the Lean library's truncating set_slice_int (FCVTXN).
  python3 -I "$here/sail_int_fix.py" "$w/out/ArmASL/ArmASL.lean"
  # An exact-enough square root for FSQRT (the toolchain's goes through Float).
  python3 -I "$here/fakereal_sqrt.py" "$w/out/ArmASL/ArmASL/FakeReal.lean"
  # Chained modules of at most PART_BYTES each (JanusASL/sail/split_lean.py).
  rm -rf "$w/split"; mkdir -p "$w/split"
  python3 -I "$here/split_lean.py" "$w/out/ArmASL/ArmASL.lean" "$w/split" --bytes "$PART_BYTES"
  cp "$w/out/ArmASL/ArmASL/"*.lean "$w/split/ArmASL/"
  (cd "$w/split" && tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - \
     ArmASL.lean ArmASL | gzip -n -9 > "$w/ArmASL.tar.gz")
  if [ -f "$VENDOR" ] && cmp -s "$w/ArmASL.tar.gz" "$VENDOR"; then
    echo "gen: regenerated model is byte-identical to $VENDOR"
  elif [ "${GEN_UPDATE:-0}" = 1 ]; then
    mkdir -p "$(dirname "$VENDOR")"; cp "$w/ArmASL.tar.gz" "$VENDOR"
    sha256sum "$VENDOR" | awk '{print $1}' > "$VENDOR.sha256"
    rm -rf "$pkg/ArmASL" "$pkg/ArmASL.lean"
    echo "gen: vendored model updated ($(cat "$VENDOR.sha256"))"
  else
    echo "gen: regenerated model DIFFERS from $VENDOR (GEN_UPDATE=1 to replace it)"; exit 1
  fi
}

# ---- shared ArmASL build cache (ASL_CACHE) ----
asl_cache_key() {
  python3 -I "$pkg/tools/asl_cache_key.py" "$root"
}

# The ArmASL build outputs and the lean-sail package, as files relative to $pkg/.lake (NUL-separated).
asl_cache_files() {
  (cd "$pkg/.lake" && for p in packages/Sail build/lib/lean/ArmASL build/lib/lean/ArmASL.* build/ir/ArmASL build/ir/ArmASL.*; do
    [ -e "$p" ] && find "$p" -type f -print0; done) || true
}

# Restore the entry for this model and toolchain into $pkg/.lake: the entry's HMAC (under the
# per-user key, scripts/lib/bcache.py) and the SHA-256 of every copied file are checked; anything
# wrong (no entry, unsigned or tampered entry, missing file, no usable key) leaves nothing copied
# and the model is built from source by the lake call that follows. A rejected entry is replaced by
# the publish after that build.
cache_restore() {
  [ -n "${ASL_CACHE:-}" ] || return 0
  local key rc=0 out
  key=$(asl_cache_key)
  mkdir -p "$pkg/.lake"
  out=$(python3 -I "$root/scripts/lib/bcache.py" fetch armasl "$ASL_CACHE" "$key" "$pkg/.lake") || rc=$?
  case $rc in
    0) echo "asl cache: ArmASL $key: $out ($ASL_CACHE)" ;;
    2) echo "asl cache: no entry for ArmASL $key ($ASL_CACHE); building" ;;
    3) echo "asl cache: the entry for ArmASL $key was REJECTED (above); building from source" ;;
    *) echo "asl cache: not usable here (above); building from source" ;;
  esac
  return 0
}

cache_publish() {
  [ -n "${ASL_CACHE:-}" ] && [ "${ASL_CACHE_READONLY:-0}" != 1 ] || return 0
  local key inp rc=0 out
  key=$(asl_cache_key)
  mkdir -p "$ASL_CACHE" || return 0
  inp=$(mktemp "${TMPDIR:-/tmp}/asl-cache-inputs.XXXXXX")
  python3 -I "$pkg/tools/asl_cache_key.py" "$root" --show > "$inp"
  out=$(asl_cache_files | python3 -I "$root/scripts/lib/bcache.py" store armasl "$ASL_CACHE" "$key" "$pkg/.lake" --inputs "$inp") || rc=$?
  rm -f "$inp"
  [ $rc = 0 ] && echo "asl cache: ArmASL $key: $out" || echo "asl cache: not stored (rc $rc)"
  cache_gc
}

# Keep the cache within $ASL_CACHE_MAX (default 15G): unreferenced ArmASL entries first, then the
# least recently restored entries (JanusASL/tools/asl_mod_cache.py gc; the checkout's own ArmASL
# entry and anything used in the last hour are kept). ASL_CACHE_MAX=off disables it.
cache_gc() {
  [ -n "${ASL_CACHE:-}" ] && [ "${ASL_CACHE_READONLY:-0}" != 1 ] && [ "${ASL_CACHE_MAX:-15G}" != off ] || return 0
  python3 -I "$pkg/tools/asl_mod_cache.py" gc "$ASL_CACHE" --max "${ASL_CACHE_MAX:-15G}" --root "$root" || true
}

# ---- shared per-module cache of the JanusASL and Janus modules (ASL_CACHE/mods) ----
# JanusASL/tools/asl_mod_cache.py: one entry per module, keyed by what Lake traces (source,
# imports' keys, package settings, toolchain), with a SHA-256 manifest checked on every copy.
modcache_restore() {
  [ -n "${ASL_CACHE:-}" ] || return 0
  python3 -I "$pkg/tools/asl_mod_cache.py" restore "$root" "$ASL_CACHE" || true
}

modcache_publish() {  # modcache_publish [--exe]
  [ -n "${ASL_CACHE:-}" ] && [ "${ASL_CACHE_READONLY:-0}" != 1 ] || return 0
  python3 -I "$pkg/tools/asl_mod_cache.py" publish "$root" "$ASL_CACHE" "$@" || true
  cache_gc
}

unpack() {
  echo "$(cat "$VENDOR.sha256")  $VENDOR" | sha256sum -c --quiet
  if [ ! -f "$pkg/ArmASL.lean" ] || [ "$VENDOR" -nt "$pkg/ArmASL.lean" ]; then
    (cd "$pkg" && rm -rf ArmASL ArmASL.lean && tar -xzf "$VENDOR" && touch ArmASL.lean)
  fi
}

# Lake starts as many Lean processes as its thread pool has threads (LEAN_NUM_THREADS); each Lean
# process gets the same value for its own elaboration threads. Bound both by memory: every process
# of the build stays under ASL_JOB_GB (docs/ASL.md, "Memory"), so ASL_JOBS of them fit ASL_MEM_GB.
asl_jobs() {
  local avail budget per
  avail=$(awk '/^MemAvailable:/ {print int($2 / 1048576)}' /proc/meminfo)
  budget="${ASL_MEM_GB:-$(( avail * 6 / 10 < 24 ? avail * 6 / 10 : 24 ))}"
  per="${ASL_JOB_GB:-8}"
  ASL_JOBS="${ASL_JOBS:-$(( budget / per > 0 ? budget / per : 1 ))}"
  echo "asl: ${ASL_JOBS} Lean processes at once (budget ${budget} GB, ${per} GB each, ${avail} GB available)" >&2
}

lake_asl() {
  asl_jobs
  (cd "$pkg" && LEAN_NUM_THREADS="$ASL_JOBS" memguard_lake "$@")
}

do_build() {
  unpack
  cache_restore
  lake_asl build ArmASL
  cache_publish
  modcache_restore
  lake_asl build ArmASL JanusASL janus-asl-check
  cache_publish
  modcache_publish --exe
}

# Only the cache restore (JanusASL/tools/test_asl_cache.sh).
do_restore() {
  unpack
  cache_restore
}

# Only the model: restore, `lake build ArmASL`, publish.
do_model() {
  unpack
  cache_restore
  lake_asl build ArmASL
  cache_publish
}

do_check() {
  do_build
  if ! art_exists "$CASES"; then "$root/scripts/oracle.sh" full; fi
  mkdir -p "$OUT"
  # The corpus may be zstd-compressed (scripts/lib/artifacts.sh): decompressed for the check and
  # removed again; the verdicts are compressed afterwards (KEEP=1 keeps them raw).
  trap 'art_cleanup; art_prune "$OUT"' EXIT
  art_input "$CASES" >/dev/null
  (cd "$pkg" && memguard_run -n janus-asl-check -- lake exe janus-asl-check "$CASES" "$OUT/verdicts.jsonl" "$JOBS") | tee "$OUT/summary.txt"
}

do_prove() {
  unpack
  cache_restore
  lake_asl build ArmASL
  cache_publish
  modcache_restore
  lake_asl build JanusASL
  modcache_publish
  (cd "$pkg" && lake env lean JanusASL/Audit.lean)
}

# leanchecker replays each target module in its own task, every one importing that module's whole
# environment (the ArmASL model included), so `leanchecker JanusASL.Proofs` holds up to
# LEAN_NUM_THREADS such environments at once and keeps its heap at the largest. Replay every module
# of the package instead, REPLAY_BATCH modules per process, one process at a time.
do_replay() {
  unpack
  cache_restore
  modcache_restore
  lake_asl build JanusASL
  modcache_publish
  # The modules: the import closure of JanusASL.Proofs within the package (what
  # `leanchecker JanusASL.Proofs` replays, less files that nothing imports). leanchecker's targets
  # are name prefixes, so a module with submodules (JanusASL.Proofs itself, a split file's import
  # list) would pull all of them into one process: pass only the leaves, after checking that the
  # others declare nothing (imports and comments only).
  local mods=() m batch="${REPLAY_BATCH:-4}" list
  list="$(python3 -I - "$pkg" <<'PY'
import os, re, sys
pkg = sys.argv[1]
path = lambda m: os.path.join(pkg, *m.split(".")) + ".lean"
seen, todo = set(), ["JanusASL.Proofs"]
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    todo += [i for i in re.findall(r"^import (JanusASL\.\S+)", open(path(m)).read(), re.M)]
for m in sorted(seen):
    if any(o.startswith(m + ".") for o in seen):
        txt = re.sub(r"/-!.*?-/", "", open(path(m)).read(), flags=re.S)
        if any(l.strip() and not l.startswith(("import ", "--")) for l in txt.split("\n")):
            sys.exit("replay: %s has submodules and declarations; cannot replay it alone" % m)
    else:
        print(m)
PY
)" || exit 1
  for m in $list; do mods+=("$m"); done
  local i
  for ((i = 0; i < ${#mods[@]}; i += batch)); do
    (cd "$pkg" && LEAN_NUM_THREADS="${JANUS_REPLAY_THREADS:-4}" memguard_run -n "leanchecker" -- lake env leanchecker "${mods[@]:i:batch}") ||
      { echo "replay: leanchecker failed on ${mods[*]:i:batch}" >&2; exit 1; }
  done
  echo "replay: leanchecker passed on all ${#mods[@]} modules of JanusASL.Proofs (LEAN_NUM_THREADS=${JANUS_REPLAY_THREADS:-4}, $batch per process)"
}

# janus verify --asl builds JanusASL in its own cache (`janus framework --json` .asl.cacheDir). Seed
# that build from the in-tree one (Lake reuses modules by content hash), so the model is built
# once, then verify each example with --asl from a fresh extraction.
do_verify() {
  do_build
  export PATH=/usr/local/go/bin:$PATH
  (cd "$root" && CGO_ENABLED=0 go build -o bin/janus ./cmd/janus)
  "$root/scripts/build-examples.sh" >/dev/null
  local d
  d=$("$root/bin/janus" framework --janus-root "$root" --json |
    python3 -I -c 'import json, sys; print(json.load(sys.stdin)["asl"]["cacheDir"])')
  # $d is janus's private cache for this verification: its .lake must be a real directory of its own, never a
  # link into a checkout (a gate tree's JanusASL/.lake is itself a symlink to the main checkout's; `cp -a` of
  # it copied the link, and janus then wrote its package override and built through it into the checkout).
  # A link left by an earlier run is removed (the link only), and the seed is a DEREFERENCED copy.
  if [ -L "$d/.lake" ]; then echo "verify: removing the symlinked $d/.lake (the link, not its target)"; rm -f "$d/.lake"; fi
  if [ ! -d "$d/.lake" ] && [ -d "$pkg/.lake" ]; then
    echo "verify: seeding $d from $pkg/.lake (a private, dereferenced copy)"
    mkdir -p "$d" && cp -aL --reflink=auto "$pkg/.lake" "$d/.lake" && rm -f "$d/.lake/package-overrides.json"
    [ -d "$d/.lake" ] && [ ! -L "$d/.lake" ] || { echo "verify: the seed is not a private directory" >&2; return 1; }
  fi
  local fail=0 n
  mkdir -p "$OUT"
  for n in ${ASL_EXAMPLES:-Add Max Mul64 Add128}; do
    "$root/bin/janus" extract "$root/artifacts/examples-arm64" "example.com/basic.$n" "$root/artifacts/$n" >/dev/null
    if "$root/bin/janus" verify "$root/artifacts/$n" --proof "$root/examples/proofs/$n.lean" --janus-root "$root" --asl \
         > "$OUT/verify-$n.log" 2>&1 && grep -q '^ASL corollary: Verified: JanusASLCorollary.correctness_asl' "$OUT/verify-$n.log"; then
      echo "$n: ASL corollary verified"
      sed -n '/^ASL corollary/,/^  Assumptions/p' "$OUT/verify-$n.log" | grep -A1 '^  Statement:' | tail -1
    else
      echo "$n: FAILED (see $OUT/verify-$n.log)"; tail -20 "$OUT/verify-$n.log"; fail=1
    fi
  done
  return $fail
}

case "$mode" in
  deps) do_deps ;;
  gen) do_gen ;;
  restore) do_restore ;;
  model) do_model ;;
  build) do_build ;;
  check) do_check ;;
  prove) do_prove ;;
  replay) do_replay ;;
  verify) do_verify ;;
  *) echo "usage: $0 deps|gen|restore|model|build|check|prove|replay|verify" >&2; exit 2 ;;
esac

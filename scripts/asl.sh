#!/usr/bin/env bash
# JanusASL: Janus' AArch64 model against Arm's ASL inside Lean (docs/ASL.md).
#
#   scripts/asl.sh deps    install the pinned toolchain into $DEPS: an opam root with Sail 0.20.3
#                          plus 8 upstream Lean-backend commits and JanusASL's backend fixes (JanusASL/sail/*.patch),
#                          the slicing plugin, sail-arm at the pin, lean-sail at the pin
#   scripts/asl.sh gen     slice sail-arm to the Janus subset and generate Lean (JanusASL/ArmASL*),
#                          then compare with the vendored copy (GEN_UPDATE=1 replaces the vendored copy)
#   scripts/asl.sh build   unpack the vendored model (if needed) and build JanusASL (lake)
#   scripts/asl.sh check   build + `lake exe janus-asl-check` on the oracle corpus (default)
#   scripts/asl.sh prove   build the proofs (JanusASL.Proofs) and audit their axioms
#
# Environment:
#   DEPS     pinned external sources/toolchains (default /srv/janus-asl-deps)
#   CASES    corpus (default artifacts/oracle/cases.jsonl; made by `scripts/oracle.sh full` if missing)
#   OUT      output dir for the check (default artifacts/asl)
#   JOBS     parallel tasks for the check (default nproc)
#   ASL_CACHE          a shared ArmASL build cache (a directory; off by default). Before building,
#                      the generated model's build (and the lean-sail package) is copied from
#                      the cache entry for this model and toolchain, if there is one; after a
#                      build, it is stored there if not. Entries are keyed by the SHA-256 of the
#                      vendored tarball, lean-toolchain, JanusASL's lakefile and manifest and the
#                      splitter, carry a SHA-256 manifest that is checked on every copy, and are
#                      published atomically, so worktrees and CI runners share one build of the
#                      ~45 min model. The cache must be writable only by users you trust: its
#                      oleans are what the JanusASL proofs are checked against.
#   ASL_CACHE_READONLY=1   use the cache but never write to it
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
mode="${1:-check}"
DEPS="${DEPS:-/srv/janus-asl-deps}"
CASES="${CASES:-$root/artifacts/oracle/cases.jsonl}"
OUT="${OUT:-$root/artifacts/asl}"
JOBS="${JOBS:-$(nproc)}"
pkg="$root/JanusASL"
here="$pkg/sail"

# ---- pins (keep in sync with docs/ASL.md) ----
SAIL_URL=https://github.com/rems-project/sail
SAIL_TAG=0.20.3
SAIL_REV=0.20.3                 # tag; the patch adds later upstream Lean-backend fixes + JanusASL's
SAIL_ARM_URL=https://github.com/rems-project/sail-arm
SAIL_ARM_REV=7d0581642d0e3aaca367bbc5650aca7c53057543   # upstream master (includes the Lean MOD fix)
OCAML_VERSION=5.2.1
SWITCH=sail-0.20.3-janus
VENDOR="$pkg/vendor/ArmASL.tar.gz"

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
  local w="$DEPS/gen"
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
  # One module per ~1/24 of the declarations, chained (JanusASL/sail/split_lean.py).
  rm -rf "$w/split"; mkdir -p "$w/split"
  python3 -I "$here/split_lean.py" "$w/out/ArmASL/ArmASL.lean" "$w/split" 24
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
  { cat "$VENDOR.sha256"; cat "$root/lean-toolchain"; cat "$pkg/lakefile.toml" "$pkg/lake-manifest.json" "$here/split_lean.py"; } |
    sha256sum | cut -c1-32
}

# The ArmASL build outputs and the lean-sail package, relative to $pkg/.lake.
asl_cache_paths() {
  (cd "$pkg/.lake" && for p in packages/Sail build/lib/lean/ArmASL build/lib/lean/ArmASL.* build/ir/ArmASL build/ir/ArmASL.*; do
    [ -e "$p" ] && echo "$p"; done) || true
}

cache_restore() {
  [ -n "${ASL_CACHE:-}" ] || return 0
  local e; e="$ASL_CACHE/$(asl_cache_key)"
  [ -f "$e/MANIFEST.sha256" ] || { echo "asl cache: no entry for this model and toolchain ($e)"; return 0; }
  if [ -f "$pkg/.lake/build/lib/lean/ArmASL.olean" ] && (cd "$pkg/.lake" && sha256sum -c --quiet --status "$e/MANIFEST.sha256" 2>/dev/null); then
    echo "asl cache: the ArmASL build already matches $e"; return 0
  fi
  echo "asl cache: copying the ArmASL build from $e"
  mkdir -p "$pkg/.lake"
  (cd "$e/tree" && tar -cf - .) | (cd "$pkg/.lake" && tar -xf -)
  (cd "$pkg/.lake" && sha256sum -c --quiet "$e/MANIFEST.sha256") ||
    { echo "asl cache: the copy does not match the entry's manifest; building instead" >&2
      (cd "$pkg/.lake" && rm -rf packages/Sail build/lib/lean/ArmASL build/lib/lean/ArmASL.* build/ir/ArmASL build/ir/ArmASL.*); }
}

cache_publish() {
  [ -n "${ASL_CACHE:-}" ] && [ "${ASL_CACHE_READONLY:-0}" != 1 ] || return 0
  local key e tmp
  key=$(asl_cache_key); e="$ASL_CACHE/$key"
  mkdir -p "$ASL_CACHE" || return 0
  # One publisher per key at a time; an entry that has the C sources too is not replaced.
  exec 9>"$ASL_CACHE/$key.lock"
  flock 9
  if [ -f "$e/MANIFEST.sha256" ] && { [ ! -d "$pkg/.lake/build/ir/ArmASL" ] || [ -d "$e/tree/build/ir/ArmASL" ]; }; then
    flock -u 9; return 0
  fi
  tmp=$(mktemp -d "$ASL_CACHE/.tmp-$key.XXXXXX")
  mkdir -p "$tmp/tree"
  (cd "$pkg/.lake" && asl_cache_paths | tar -cf - -T -) | (cd "$tmp/tree" && tar -xf -)
  (cd "$tmp/tree" && find . -type f -print0 | sort -z | xargs -0 sha256sum) > "$tmp/MANIFEST.sha256"
  rm -rf "$e.old"; [ -d "$e" ] && mv "$e" "$e.old"
  mv "$tmp" "$e" && rm -rf "$e.old"
  echo "asl cache: stored the ArmASL build in $e"
  flock -u 9
}

unpack() {
  echo "$(cat "$VENDOR.sha256")  $VENDOR" | sha256sum -c --quiet
  if [ ! -f "$pkg/ArmASL.lean" ] || [ "$VENDOR" -nt "$pkg/ArmASL.lean" ]; then
    (cd "$pkg" && rm -rf ArmASL ArmASL.lean && tar -xzf "$VENDOR" && touch ArmASL.lean)
  fi
}

do_build() {
  unpack
  cache_restore
  (cd "$pkg" && memguard_lake build ArmASL)
  cache_publish
  (cd "$pkg" && memguard_lake build ArmASL JanusASL janus-asl-check)
  cache_publish
}

do_check() {
  do_build
  if [ ! -f "$CASES" ]; then "$root/scripts/oracle.sh" full; fi
  mkdir -p "$OUT"
  (cd "$pkg" && memguard_run -n janus-asl-check -- lake exe janus-asl-check "$CASES" "$OUT/verdicts.jsonl" "$JOBS") | tee "$OUT/summary.txt"
}

do_prove() {
  unpack
  cache_restore
  (cd "$pkg" && memguard_lake build ArmASL)
  cache_publish
  (cd "$pkg" && memguard_lake build JanusASL && lake env lean JanusASL/Audit.lean)
}

case "$mode" in
  deps) do_deps ;;
  gen) do_gen ;;
  build) do_build ;;
  check) do_check ;;
  prove) do_prove ;;
  *) echo "usage: $0 deps|gen|build|check|prove" >&2; exit 2 ;;
esac

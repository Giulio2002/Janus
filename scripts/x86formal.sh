#!/usr/bin/env bash
# JanusX86: Janus' amd64 model against the Sail x86 model (ACL2 X86isa) inside Lean (docs/X86FORMAL.md).
#
#   scripts/x86formal.sh deps    the pinned toolchain: JanusASL's opam root with Sail 0.20.3 and its
#                                patches (scripts/asl.sh deps), the slicing plugin (JanusASL's, built
#                                into $X86DEPS), sail-x86-from-acl2 at the pin
#   scripts/x86formal.sh gen     slice the model to the Janus subset and generate Lean (JanusX86/X86Sail*),
#                                then compare with the vendored copy (GEN_UPDATE=1 replaces the vendored copy)
#   scripts/x86formal.sh build   unpack the vendored model (if needed) and build JanusX86 (lake)
#   scripts/x86formal.sh check   build + `lake exe janus-x86-check` on the amd64 oracle corpus (default)
#   scripts/x86formal.sh prove   build the proofs (JanusX86.Proofs) and audit their axioms
#
# Environment:
#   DEPS     JanusASL's pinned toolchain (default /srv/janus-asl-deps; scripts/asl.sh)
#   X86DEPS  sail-x86-from-acl2 checkout, plugin build, generation work dir (default /srv/janus-x86-deps)
#   CASES    corpus (default artifacts/oracle-amd64/cases.jsonl; made by `scripts/oracle-amd64.sh full`)
#   HW       hardware results of the corpus (default: hw.jsonl next to CASES)
#   OUT      output dir for the check (default artifacts/x86formal)
#   JOBS     parallel tasks for the check (default nproc)
#   JANUS_LAKE_JOB_MEM  per-lake-job memory budget (default 3G): lake runs with
#            LEAN_NUM_THREADS = budget / this (scripts/lib/memguard.sh). Measured peaks
#            (scripts/peak-mem.sh, one job): X86Sail/Part12 2.6 GB RSS, the proof files <= 1.9 GB.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
export JANUS_LAKE_JOB_MEM="${JANUS_LAKE_JOB_MEM:-3G}"
mode="${1:-check}"
DEPS="${DEPS:-/srv/janus-asl-deps}"
X86DEPS="${X86DEPS:-/srv/janus-x86-deps}"
CASES="${CASES:-$root/artifacts/oracle-amd64/cases.jsonl}"
HW="${HW:-$(dirname "$CASES")/hw.jsonl}"
OUT="${OUT:-$root/artifacts/x86formal}"
JOBS="${JOBS:-$(nproc)}"
pkg="$root/JanusX86"
here="$pkg/sail"

# ---- pins (keep in sync with docs/X86FORMAL.md) ----
X86_URL=https://github.com/rems-project/sail-x86-from-acl2
X86_REV=0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf   # Nov 2024; the commit oracle-amd64-formal/build.sh uses
SWITCH=sail-0.20.3-janus                          # JanusASL's opam switch (Sail 0.20.3 + patches)
VENDOR="$pkg/vendor/X86Sail.tar.gz"

export OPAMROOT="$DEPS/opam" OPAMYES=1
model="$X86DEPS/sail-x86-from-acl2-${X86_REV:0:7}/model"
plugin="$X86DEPS/plugin-build/default/sail_plugin_janus.cmxs"

do_deps() {
  mkdir -p "$X86DEPS"
  if ! opam switch list 2>/dev/null | grep -q "$SWITCH"; then "$root/scripts/asl.sh" deps; fi
  if [ ! -d "$X86DEPS/sail-x86-from-acl2-${X86_REV:0:7}" ]; then
    [ -d "$X86DEPS/sail-x86-from-acl2/.git" ] || git clone -q "$X86_URL" "$X86DEPS/sail-x86-from-acl2"
    git -C "$X86DEPS/sail-x86-from-acl2" worktree add -q --detach "$X86DEPS/sail-x86-from-acl2-${X86_REV:0:7}" "$X86_REV"
  fi
  eval "$(opam env --switch="$SWITCH" --set-switch)"
  # JanusASL's slicing plugin, unchanged, built outside the source tree
  (cd "$root/JanusASL/sail/plugin" && dune build --build-dir "$X86DEPS/plugin-build" ./sail_plugin_janus.cmxs)
}

do_gen() {
  do_deps
  eval "$(opam env --switch="$SWITCH" --set-switch)"
  local w="$X86DEPS/gen"
  rm -rf "$w/sliced" "$w/out" "$w/split"; mkdir -p "$w/out" "$w/split"
  python3 -I "$here/slice.py" "$model" "$w/sliced" "$here/keep.txt" > "$w/slice-stats.json"
  # The harness and the termination measures are copied next to the sliced sources, so that every
  # path Sail records (assertion messages) is relative.
  cp "$here/harness.sail" "$here/termination_measures.sail" "$w/sliced/"
  local files=(prelude.sail register_types.sail registers.sail register_accessors.sail opcode_ext.sail
    memory_accessors.sail init.sail config.sail logging.sail step.sail main.sail harness.sail
    termination_measures.sail)
  # Lake fetches lean-sail itself; the generated lakefile is not used (JanusX86/lakefile.toml is).
  (cd "$w/sliced" && ulimit -s unlimited &&
    sail --plugin "$plugin" --janus-lean \
      --lean-import-file "$here/JanusX86Extras.lean" \
      --janus-roots "$(grep -v '^#' "$here/roots.txt" | tr '\n' ' ')" \
      --lean-output-dir "$w/out" --lean-force-output --lean-single-file --lean-line-width 100000 \
      -o X86Sail "${files[@]}" > "$w/sail.log" 2>&1) ||
    { grep -v -i warning "$w/sail.log" | tail -30; exit 1; }
  # One module per ~1/12 of the declarations, chained (JanusX86/sail/split_lean.py).
  python3 -I "$here/split_lean.py" "$w/out/X86Sail/X86Sail.lean" "$w/split" 12
  cp "$w/out/X86Sail/X86Sail/"*.lean "$w/split/X86Sail/"
  (cd "$w/split" && tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - \
     X86Sail.lean X86Sail | gzip -n -9 > "$w/X86Sail.tar.gz")
  if [ -f "$VENDOR" ] && cmp -s "$w/X86Sail.tar.gz" "$VENDOR"; then
    echo "gen: regenerated model is byte-identical to $VENDOR"
  elif [ "${GEN_UPDATE:-0}" = 1 ]; then
    mkdir -p "$(dirname "$VENDOR")"; cp "$w/X86Sail.tar.gz" "$VENDOR"
    sha256sum "$VENDOR" | awk '{print $1}' > "$VENDOR.sha256"
    rm -rf "$pkg/X86Sail" "$pkg/X86Sail.lean"
    echo "gen: vendored model updated ($(cat "$VENDOR.sha256"))"
  else
    echo "gen: regenerated model DIFFERS from $VENDOR (GEN_UPDATE=1 to replace it)"; exit 1
  fi
}

unpack() {
  echo "$(cat "$VENDOR.sha256")  $VENDOR" | sha256sum -c --quiet
  if [ ! -f "$pkg/X86Sail.lean" ] || [ "$VENDOR" -nt "$pkg/X86Sail.lean" ]; then
    (cd "$pkg" && rm -rf X86Sail X86Sail.lean && tar -xzf "$VENDOR" && touch X86Sail.lean)
  fi
}

do_build() {
  unpack
  (cd "$pkg" && memguard_lake build X86Sail JanusX86 janus-x86-check)
}

do_check() {
  do_build
  if [ ! -f "$CASES" ]; then "$root/scripts/oracle-amd64.sh" full; fi
  mkdir -p "$OUT"
  (cd "$pkg" && memguard_run -n janus-x86-check -- lake exe janus-x86-check "$CASES" "$HW" "$OUT/verdicts.jsonl" "$JOBS") | tee "$OUT/summary.txt"
}

do_prove() {
  unpack
  (cd "$pkg" && memguard_lake build JanusX86 && memguard_run -n audit -- lake env lean JanusX86/Audit.lean)
}

case "$mode" in
  deps) do_deps ;;
  gen) do_gen ;;
  build) do_build ;;
  check) do_check ;;
  prove) do_prove ;;
  *) echo "usage: $0 deps|gen|build|check|prove" >&2; exit 2 ;;
esac

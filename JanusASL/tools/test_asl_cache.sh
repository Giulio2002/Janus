#!/usr/bin/env bash
# Tests of the shared ArmASL build cache key (scripts/asl.sh ASL_CACHE; docs/ASL.md "Build cache").
#
#   JanusASL/tools/test_asl_cache.sh              key tests (seconds): edits that cannot change
#                                                 the ArmASL build keep the key, edits that can change it
#   JanusASL/tools/test_asl_cache.sh --e2e CACHE  also end to end, from an existing entry in CACHE
#                                                 (only read): restore into a copy of this checkout,
#                                                 publish into a temporary cache, restore that into a
#                                                 copy with an edited JanusASL lakefile (new lib, new
#                                                 exe, other roots) and check that `lake build ArmASL`
#                                                 has nothing to do there; then that an edit Lake does
#                                                 trace (ArmASL's moreLeanArgs) changes the key and
#                                                 makes Lake want to rebuild.
#
# Everything happens in mktemp directories, which are removed at the end.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
e2e=""
if [ "${1:-}" = --e2e ]; then e2e="${2:?--e2e CACHE}"; fi
t=$(mktemp -d "${TMPDIR:-/tmp}/asl-cache-test.XXXXXX")
trap 'rm -rf "$t"' EXIT
fail=0

copy() {  # copy DIR: a copy of the checkout without builds
  rm -rf "$1"; mkdir -p "$1"
  rsync -a --exclude=.git --exclude=.lake --exclude=artifacts --exclude='JanusASL/ArmASL' \
    --exclude='JanusASL/ArmASL.lean' "$root/" "$1/"
}
key() { python3 -I "$1/JanusASL/tools/asl_cache_key.py" "$1"; }

# edit NAME PYTHON: apply PYTHON (with `r` = the copy's root, `sub(path, old, new)`, `app(path, text)`)
edit() {
  python3 -I - "$1" "$2" <<'PY'
import os, sys
r = sys.argv[1]
def sub(p, old, new):
    p = os.path.join(r, p); s = open(p).read()
    assert old in s, (p, old); open(p, "w").write(s.replace(old, new, 1))
def app(p, text):
    open(os.path.join(r, p), "a").write(text)
exec(sys.argv[2])
PY
}

lf=JanusASL/lakefile.toml
# A copy like agent/aslverify's: other JanusASL roots, a new lib and a new exe. (agent/aslverify's
# own roots are on main now; this drops one and adds another.)
ROOTS='roots = [\"JanusASL.Proofs\", \"JanusASL.Classify\", \"JanusASL.Verify\"]'
VERIFY_EDIT='sub("'$lf'", "'"$ROOTS"'", "roots = [\"JanusASL.Proofs\", \"JanusASL.Verify\", \"JanusASL.Extra\"]")
app("'$lf'", "\n[[lean_lib]]\nname = \"JanusASLExtra\"\nroots = [\"JanusASL.Verify\"]\n\n[[lean_exe]]\nname = \"janus-asl-verify\"\nroot = \"JanusASL.Verify\"\n")'

same=(
  "aslverify-style lakefile (roots, new lib, new exe)|$VERIFY_EDIT"
  "comments, blank lines|app(\"$lf\", \"\\n# a comment\\n\\n\")"
  "ArmASL table keys reordered|sub(\"$lf\", 'moreLeanArgs = [\"--tstack=400000\"]\nmoreLeancArgs = [\"-fbracket-depth=100000\"]', 'moreLeancArgs = [\"-fbracket-depth=100000\"]\nmoreLeanArgs = [\"--tstack=400000\"]')"
  "version, defaultTargets|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.2.0\"'); sub(\"$lf\", 'defaultTargets = [\"JanusASL\", \"janus-asl-check\"]', 'defaultTargets = [\"JanusASL\"]')"
  "janus-asl-check exe's leanc args|sub(\"$lf\", 'root = \"JanusASL.Check\"\nmoreLeancArgs = [\"-fbracket-depth=100000\"]', 'root = \"JanusASL.Check\"\nmoreLeancArgs = [\"-fbracket-depth=99999\", \"-O2\"]')"
  "JanusASL lib options|sub(\"$lf\", \"$ROOTS\", \"$ROOTS\nmoreLeanArgs = [\\\"--tstack=1\\\"]\nleanOptions = { maxHeartbeats = 1 }\")"
  "a JanusASL proof file|app(\"JanusASL/JanusASL/Proofs.lean\", \"\\n-- edited\\n\")"
  "the framework's sources|app(\"Janus.lean\", \"\\n-- edited\\n\")"
  "the janus package's lakefile (a new exe)|app(\"lakefile.toml\", \"\\n[[lean_exe]]\\nname = \\\"x\\\"\\nroot = \\\"X\\\"\\n\")"
)
differ=(
  "ArmASL moreLeanArgs|sub(\"$lf\", '--tstack=400000', '--tstack=400001')"
  "ArmASL leanOptions|sub(\"$lf\", 'nameCheck = false', 'nameCheck = true')"
  "ArmASL moreLeancArgs|sub(\"$lf\", 'name = \"ArmASL\"\nmoreLeanArgs = [\"--tstack=400000\"]\nmoreLeancArgs = [\"-fbracket-depth=100000\"]', 'name = \"ArmASL\"\nmoreLeanArgs = [\"--tstack=400000\"]\nmoreLeancArgs = [\"-fbracket-depth=100001\"]')"
  "ArmASL weakLeanArgs|sub(\"$lf\", 'name = \"ArmASL\"\n', 'name = \"ArmASL\"\nweakLeanArgs = [\"-DmaxHeartbeats=1\"]\n')"
  "ArmASL srcDir|sub(\"$lf\", 'name = \"ArmASL\"\n', 'name = \"ArmASL\"\nsrcDir = \"gen\"\n')"
  "package moreLeanArgs|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.1.0\"\nmoreLeanArgs = [\"--tstack=1\"]')"
  "package leanOptions|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.1.0\"\nleanOptions = { maxHeartbeats = 1 }')"
  "package precompileModules|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.1.0\"\nprecompileModules = true')"
  "package buildType|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.1.0\"\nbuildType = \"debug\"')"
  "package name|sub(\"$lf\", 'name = \"janusasl\"', 'name = \"janusasl2\"')"
  "an unknown package setting|sub(\"$lf\", 'version = \"0.1.0\"', 'version = \"0.1.0\"\nsomeFutureSetting = 1')"
  "a lib before ArmASL that claims ArmASL.*|sub(\"$lf\", '[[lean_lib]]\nname = \"ArmASL\"', '[[lean_lib]]\nname = \"Other\"\nglobs = [\"ArmASL.+\"]\n\n[[lean_lib]]\nname = \"ArmASL\"')"
  "an exe rooted in ArmASL|app(\"$lf\", '\n[[lean_exe]]\nname = \"m\"\nroot = \"ArmASL.Main\"\n')"
  "lean-sail rev in the manifest|sub(\"JanusASL/lake-manifest.json\", '01bb54c7c8a69e52ba11863c67e7c403a6cd198a', '01bb54c7c8a69e52ba11863c67e7c403a6cd198b')"
  "lean-sail url in the manifest|sub(\"JanusASL/lake-manifest.json\", 'rems-project/lean-sail', 'someone/lean-sail')"
  "manifest packagesDir|sub(\"JanusASL/lake-manifest.json\", '\"packagesDir\": \".lake/packages\"', '\"packagesDir\": \"pkgs\"')"
  "JanusASL lean-toolchain|sub(\"JanusASL/lean-toolchain\", 'v4.34.1', 'v4.35.0')"
  "root lean-toolchain|sub(\"lean-toolchain\", 'v4.34.1', 'v4.35.0')"
  "the model tarball|sub(\"JanusASL/vendor/ArmASL.tar.gz.sha256\", open(os.path.join(r, \"JanusASL/vendor/ArmASL.tar.gz.sha256\")).read()[:2], 'zz')"
  "the splitter|app(\"JanusASL/sail/split_lean.py\", \"\\n# edited\\n\")"
  "the janus package's extraDepTargets|sub(\"lakefile.toml\", 'defaultTargets = [\"Janus\"]', 'defaultTargets = [\"Janus\"]\nextraDepTargets = [\"Janus\"]')"
  "JanusASL switched to lakefile.lean|app(\"JanusASL/lakefile.lean\", \"import Lake\\n\")"
)

copy "$t/k"
base=$(key "$t/k")
echo "base key $base"
for c in "${same[@]}"; do
  copy "$t/k"; edit "$t/k" "${c#*|}"
  k=$(key "$t/k")
  if [ "$k" = "$base" ]; then echo "ok   same key:    ${c%%|*}"; else echo "FAIL key changed: ${c%%|*}"; fail=1; fi
done
for c in "${differ[@]}"; do
  copy "$t/k"; edit "$t/k" "${c#*|}"
  k=$(key "$t/k") || k=error
  if [[ $k =~ ^[0-9a-f]{32}$ ]] && [ "$k" != "$base" ]; then echo "ok   new key:     ${c%%|*}"; else echo "FAIL same key:    ${c%%|*}"; fail=1; fi
done

if [ -n "$e2e" ]; then
  hashes() { (cd "$1/JanusASL/.lake" && find build/lib/lean/ArmASL* build/ir/ArmASL* packages/Sail/.lake/build -type f -print0 | sort -z | xargs -0 sha256sum); }
  # A: this checkout, restored from CACHE (read only), then published into a temporary cache.
  copy "$t/a"; mkdir -p "$t/cache"
  ASL_CACHE="$e2e" ASL_CACHE_READONLY=1 "$t/a/scripts/asl.sh" restore
  [ -f "$t/a/JanusASL/.lake/build/lib/lean/ArmASL.olean" ] || { echo "FAIL $e2e has no entry for this checkout"; exit 1; }
  (cd "$t/a/JanusASL" && lake build ArmASL --no-build) || { echo "FAIL lake wants to rebuild ArmASL after a restore of an unedited checkout"; exit 1; }
  ASL_CACHE="$t/cache" "$t/a/scripts/asl.sh" model | tee "$t/a.log"
  grep -q "asl cache: ArmASL .*: stored" "$t/a.log" || { echo "FAIL nothing published"; fail=1; }
  # B: the aslverify-style lakefile, restored from the temporary cache.
  copy "$t/b"; edit "$t/b" "$VERIFY_EDIT"
  [ "$(key "$t/b")" = "$(key "$t/a")" ] || { echo "FAIL the edited copy has another key"; exit 1; }
  s=$(date +%s%N)
  ASL_CACHE="$t/cache" ASL_CACHE_READONLY=1 "$t/b/scripts/asl.sh" restore
  echo "restore took $(( ($(date +%s%N) - s) / 1000000 )) ms"
  # The restored tree is the entry, byte for byte (also checked by the restore itself). Checked
  # before Lake runs: Lake's git calls refresh the stat cache in packages/Sail/.git/index.
  e="$t/cache/$(key "$t/b")"
  (cd "$t/b/JanusASL/.lake" && sha256sum -c --quiet "$e/MANIFEST.sha256") &&
    echo "ok   restored tree matches the entry's manifest ($(wc -l < "$e/MANIFEST.sha256") files)" ||
    { echo "FAIL restored tree differs from the entry"; fail=1; }
  hashes "$t/b" > "$t/b.before"
  if (cd "$t/b/JanusASL" && lake build ArmASL --no-build); then
    echo "ok   lake build ArmASL --no-build: up to date after the restore (edited lakefile)"
  else echo "FAIL lake wants to rebuild ArmASL after the restore (edited lakefile)"; exit 1; fi
  (cd "$t/b/JanusASL" && lake build ArmASL 2>&1) | tee "$t/b.log"
  hashes "$t/b" > "$t/b.after"
  if grep -Eq "Built|Building|Compiling" "$t/b.log"; then echo "FAIL lake built something"; fail=1;
  else echo "ok   lake build ArmASL built nothing"; fi
  if cmp -s "$t/b.before" "$t/b.after"; then echo "ok   $(wc -l < "$t/b.after") output files unchanged by lake build ArmASL";
  else echo "FAIL lake build ArmASL changed outputs"; fail=1; fi
  # Control: an edit Lake traces makes it want to rebuild, and changes the key.
  edit "$t/b" "sub('$lf', '--tstack=400000', '--tstack=400001')"
  rc=0; (cd "$t/b/JanusASL" && lake build ArmASL --no-build >/dev/null 2>&1) || rc=$?
  if [ "$rc" = 3 ] && [ "$(key "$t/b")" != "$(key "$t/a")" ]; then
    echo "ok   control: with ArmASL's moreLeanArgs edited, lake build --no-build exits 3 (needs a rebuild) and the key changes"
  else echo "FAIL control: lake build --no-build exited $rc, key $(key "$t/b")"; fail=1; fi
fi

[ "$fail" = 0 ] && echo "asl cache tests: all passed" || { echo "asl cache tests: FAILED"; exit 1; }

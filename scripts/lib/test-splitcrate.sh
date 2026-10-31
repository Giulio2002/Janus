#!/usr/bin/env bash
# Self-test of the Sail split hardening (small fixtures, no Sail build, seconds):
#   oracle-sail/split_crate.py  the patched crate copy is verified against the pinned checkout at every depth
#   oracle-sail/dir_digest.py   + the model_dir / split_parts functions of scripts/oracle-sail.sh: a tampered part,
#                               model.h, model_missing.cpp or instrumented model is regenerated, never reused
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-splitcrate.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0
ok() { echo "ok   $1"; }
bad() { echo "FAIL $1"; fail=1; }

# ---------- split_crate.py ----------
ck="$t/ck"; mkdir -p "$ck/csrc" "$ck/vendor/sail-runtime" "$ck/src"
printf 'fn main() {\n    let a = 1;\n    let b = 2;\n    let c = 3;\n}\n' > "$ck/build.rs"
echo 'x' > "$ck/csrc/a.h"; echo y > "$ck/vendor/sail-runtime/r.c"; printf '#!/bin/sh\n' > "$ck/src/run.sh"; chmod +x "$ck/src/run.sh"
git -C "$ck" init -q && git -C "$ck" add -A && git -C "$ck" -c user.name=t -c user.email=t@t commit -qm c
cp "$ck/build.rs" "$t/new.rs"; sed -i 's/let b = 2;/let b = 22;/' "$t/new.rs"
(cd "$t" && diff -u --label build.rs --label build.rs ck/build.rs new.rs > patch.diff)
osha=$(sha256sum "$ck/build.rs" | cut -d' ' -f1); psha=$(sha256sum "$t/new.rs" | cut -d' ' -f1)
sc() { python3 -I "$root/oracle-sail/split_crate.py" "$ck" "$t/dest" "$osha" "$psha" "$t/patch.diff" 2>&1; }
c="$t/dest/sail-aarch64-oracle"
out=$(sc) && [ -f "$c/build.rs" ] && ok "split_crate: a clean copy is made and verified" || bad "clean copy: $out"
out=$(sc) && ok "split_crate: an unchanged copy re-verifies" || bad "re-verify: $out"
want_reject() { # DESC SETUP-COMMAND UNDO
  eval "$2"; local o rc=0; o=$(sc) || rc=$?
  if [ "$rc" != 0 ]; then ok "split_crate rejects $1"; else bad "split_crate accepted $1"; fi
  eval "$3"
}
want_reject "a planted csrc/target/x.h" 'mkdir -p "$c/csrc/target"; echo p > "$c/csrc/target/x.h"' 'rm -rf "$c/csrc/target"'
want_reject "a planted vendor/sail-runtime/.git/y.h" 'mkdir -p "$c/vendor/sail-runtime/.git"; echo p > "$c/vendor/sail-runtime/.git/y.h"' 'rm -rf "$c/vendor/sail-runtime/.git"'
want_reject "a planted dotted file csrc/.hidden.h" 'echo p > "$c/csrc/.hidden.h"' 'rm -f "$c/csrc/.hidden.h"'
want_reject "a planted root target/ directory" 'mkdir -p "$c/target"; echo p > "$c/target/z"' 'rm -rf "$c/target"'
want_reject "a planted root .git/ directory" 'mkdir -p "$c/.git"; echo p > "$c/.git/z"' 'rm -rf "$c/.git"'
want_reject "a changed executable bit" 'chmod +x "$c/csrc/a.h"' 'chmod -x "$c/csrc/a.h"'
want_reject "a lost executable bit" 'chmod -x "$c/src/run.sh"' 'chmod +x "$c/src/run.sh"'
want_reject "a modified file" 'echo z >> "$c/csrc/a.h"' 'echo x > "$c/csrc/a.h"'
want_reject "a planted empty directory" 'mkdir "$c/csrc/empty"' 'rmdir "$c/csrc/empty"'
want_reject "a symlinked directory" 'ln -s /nonexistent "$c/csrc/lnk"' 'rm -f "$c/csrc/lnk"'
want_reject "a symlinked file" 'ln -s a.h "$c/csrc/lnk.h"' 'rm -f "$c/csrc/lnk.h"'
out=$(sc) && ok "split_crate: the copy is accepted again after every plant is removed" || bad "after undo: $out"
# the checkout's own root .git and target/ are not part of the crate, but a nested one is compared
mkdir -p "$ck/target"; echo b > "$ck/target/built"
out=$(sc) && ok "split_crate: the checkout's root target/ is ignored" || bad "root target: $out"
rm -rf "$ck/target"

# ---------- dir_digest.py ----------
dd() { python3 -I "$root/oracle-sail/dir_digest.py" "$@"; }
p="$t/parts"; mkdir -p "$p"; for i in 00 01 02; do echo "part $i" > "$p/model_part_$i.cpp"; done; echo h > "$p/model.h"; echo m > "$p/model_missing.cpp"
dd record "$p/.complete" "$p" -- inst=I >/dev/null && dd check "$p/.complete" "$p" -- inst=I 2>/dev/null && ok "dir_digest: a fresh record checks" || bad "fresh record"
chk_bad() { # DESC SETUP UNDO
  eval "$2"; if dd check "$p/.complete" "$p" -- inst=I 2>/dev/null; then bad "dir_digest accepted $1"; else ok "dir_digest detects $1"; fi; eval "$3"
}
chk_bad "a tampered part" 'echo evil >> "$p/model_part_01.cpp"' 'echo "part 01" > "$p/model_part_01.cpp"'
chk_bad "a same-size tampered part" 'echo "part 0X" > "$p/model_part_01.cpp"' 'echo "part 01" > "$p/model_part_01.cpp"'
chk_bad "a tampered model.h" 'echo evil >> "$p/model.h"' 'echo h > "$p/model.h"'
chk_bad "a tampered model_missing.cpp" 'echo evil >> "$p/model_missing.cpp"' 'echo m > "$p/model_missing.cpp"'
chk_bad "an extra part" 'echo e > "$p/model_part_03.cpp"' 'rm "$p/model_part_03.cpp"'
chk_bad "a planted dotfile" 'echo e > "$p/.x"' 'rm "$p/.x"'
chk_bad "a removed part" 'mv "$p/model_part_02.cpp" "$t/keep"' 'mv "$t/keep" "$p/model_part_02.cpp"'
chk_bad "a planted subdirectory" 'mkdir "$p/sub"' 'rmdir "$p/sub"'
dd check "$p/.complete" "$p" -- inst=J 2>/dev/null && bad "dir_digest accepted another recorded value" || ok "dir_digest detects a changed recorded value (inst)"
dd check "$p/.complete" "$p" -- inst=I 2>/dev/null && ok "dir_digest: accepted again after every tamper is undone" || bad "after undo"

# ---------- model_dir / split_parts of scripts/oracle-sail.sh (fake instrumenter and splitter) ----------
here="$t/here"; mkdir -p "$here"; cp "$root/oracle-sail/dir_digest.py" "$here/"
cat > "$here/instrument_model.py" <<'PY'
import sys
open(sys.argv[2], "w").write("INSTR\n" + open(sys.argv[1]).read())
open(sys.argv[2] + ".count", "a").write("x")
PY
cat > "$here/split_model.py" <<'PY'
import sys
n = int(sys.argv[3])
for i in range(n):
    open("%s/model_part_%02d.cpp" % (sys.argv[2], i), "w").write("part %d of %s" % (i, open(sys.argv[1]).read()))
open("/dev/null", "w")
PY
fn="$t/fn.sh"
{ echo 'here="'$here'"; SAIL_SPLIT_PARTS=4'
  for f in sha256_of model_dir split_parts; do awk -v n="$f" '$0 ~ "^"n"\\(\\) \\{" {p=1} p {print} p && /^}/ {exit}' "$root/scripts/oracle-sail.sh"; done; } > "$fn"
src="$t/src"; mkdir -p "$src"; echo "MODEL" > "$src/model.cpp"; echo H > "$src/model.h"; echo M > "$src/model_missing.cpp"
inst="$t/inst"
run() { bash -c 'set -euo pipefail; . "$1"; shift; "$@"' _ "$fn" "$@" 2>"$t/err"; }
run model_dir "$src" "$inst" && grep -q INSTR "$inst/model.cpp" && ok "model_dir: instruments once" || bad "model_dir first"
m1=$(stat -c %Y "$inst/model.cpp"); sleep 1.1
run model_dir "$src" "$inst" && [ "$(stat -c %Y "$inst/model.cpp")" = "$m1" ] && ok "model_dir: an intact directory is reused" || bad "model_dir reuse"
echo evil >> "$inst/model.cpp"; touch -d '2000-01-01' "$inst/model.cpp"
run model_dir "$src" "$inst" && ! grep -q evil "$inst/model.cpp" && grep -q regenerating "$t/err" && ok "model_dir: a tampered instrumented model (old mtime) is regenerated" || bad "model_dir tamper"
echo evil > "$inst/model.h"; touch -d '2000-01-01' "$inst/model.h"
run model_dir "$src" "$inst" && [ "$(cat "$inst/model.h")" = H ] && ok "model_dir: a tampered model.h is regenerated" || bad "model_dir model.h"
echo evil > "$inst/model_missing.cpp"
run model_dir "$src" "$inst" && [ "$(cat "$inst/model_missing.cpp")" = M ] && ok "model_dir: a tampered model_missing.cpp is regenerated" || bad "model_dir missing"
rm "$inst/.inst-complete"
run model_dir "$src" "$inst" && [ -f "$inst/.inst-complete" ] && grep -q regenerating "$t/err" && ok "model_dir: a directory without a record is regenerated" || bad "model_dir no record"
echo "MODEL2" > "$src/model.cpp"; touch -d '2000-01-01' "$src/model.cpp"
run model_dir "$src" "$inst" && grep -q MODEL2 "$inst/model.cpp" && ok "model_dir: a changed source model (old mtime) is picked up" || bad "model_dir src change"
d1=$(run split_parts "$inst") && [ -f "$d1/.complete" ] && [ "$(ls "$d1" | grep -c model_part_)" = 4 ] && ok "split_parts: splits once" || bad "split_parts first"
c1=$(stat -c %Y "$d1/model_part_00.cpp"); sleep 1.1
d2=$(run split_parts "$inst") && [ "$d2" = "$d1" ] && [ "$(stat -c %Y "$d1/model_part_00.cpp")" = "$c1" ] && ok "split_parts: an intact directory is reused" || bad "split_parts reuse"
for f in model_part_02.cpp model.h model_missing.cpp; do
  echo evil >> "$d1/$f"; touch -d '2000-01-01' "$d1/$f"
  d3=$(run split_parts "$inst") && ! grep -q evil "$d3/$f" && grep -q regenerating "$t/err" && ok "split_parts: a tampered $f (old mtime) is regenerated" || bad "split_parts tamper $f"
done
echo e > "$d1/model_part_09.cpp"
d3=$(run split_parts "$inst") && [ ! -e "$d3/model_part_09.cpp" ] && ok "split_parts: an extra part is regenerated away" || bad "split_parts extra"
rm "$d1/model_part_01.cpp"
d3=$(run split_parts "$inst") && [ -f "$d3/model_part_01.cpp" ] && ok "split_parts: a removed part is regenerated" || bad "split_parts removed"
rm "$d1/.complete"
d3=$(run split_parts "$inst") && [ -f "$d3/.complete" ] && ok "split_parts: a directory without .complete is regenerated" || bad "split_parts no record"
[ "$fail" = 0 ] && echo "splitcrate tests: all passed" || { echo "splitcrate tests: FAILED"; exit 1; }

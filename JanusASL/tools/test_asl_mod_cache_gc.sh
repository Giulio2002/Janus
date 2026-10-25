#!/usr/bin/env bash
# Tests of the ASL cache collector (JanusASL/tools/asl_mod_cache.py gc; scripts/asl.sh cache_gc).
#
#   JanusASL/tools/test_asl_mod_cache_gc.sh               fixture tests (seconds)
#   JanusASL/tools/test_asl_mod_cache_gc.sh --sample CACHE   also a stress test on a COPY (in mktemp)
#                                                  of CACHE's entries for this checkout's modules:
#                                                  restores race `gc --max 0 --grace 0`; every
#                                                  module must end up restored exactly as its
#                                                  entry's manifest says, or not at all. CACHE is
#                                                  only read.
#
# Everything happens in mktemp directories (on disk, under ${TMPDIR:-/var/tmp}), removed at the end.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
sample=""
if [ "${1:-}" = --sample ]; then sample="${2:?--sample CACHE}"; fi
t=$(mktemp -d "${TMPDIR:-/var/tmp}/asl-gc-test.XXXXXX")
trap 'rm -rf "$t"' EXIT
tool="$root/JanusASL/tools/asl_mod_cache.py"

python3 -I - "$tool" "$root" "$t" <<'PY'
import importlib.util, os, subprocess, sys, time, fcntl, json
tool, root, t = sys.argv[1:4]
spec = importlib.util.spec_from_file_location("m", tool)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
fail = 0
def ok(c, msg):
    global fail
    print(("ok   " if c else "FAIL ") + msg)
    fail |= not c

cur = sorted(m.checkout_armasl_keys(root))
now = time.time()
def mk(cache):
    """A fixture: ArmASL entries A (this checkout's key), B (referenced by module m1), C (unreferenced,
    old), D (unreferenced, used a minute ago); modules m1..m6 of 1 MiB each, oldest first, m7 used a
    minute ago."""
    os.makedirs(cache)
    def entry(path, mb, age, refs=()):
        os.makedirs(os.path.join(path, "tree"))
        with open(os.path.join(path, "tree", "blob"), "wb") as f:
            f.write(b"x" * (mb << 20))
        with open(os.path.join(path, "MANIFEST.sha256"), "w") as f:
            f.write("0  janus/blob\n")
        if refs is not None:
            with open(os.path.join(path, "INPUTS.json"), "w") as f:
                json.dump({"imports": [["ArmASL", "armasl:" + r] for r in refs]}, f)
        open(path + ".lock", "w").close()
        for p in (path, path + ".lock"):
            os.utime(p, (now - age, now - age))
    keys = {"A": cur[0], "B": "b" * 32, "C": "c" * 32, "D": "d" * 32}
    for n, age in (("A", 9e5), ("B", 9e5), ("C", 9e5), ("D", 60)):
        entry(os.path.join(cache, keys[n]), 2, age, refs=None)
    mods = {}
    for i in range(1, 8):
        k = ("%d" % i) * 40
        mods[i] = os.path.join(cache, "mods", k[:2], k)
        entry(mods[i], 1, 60 if i == 7 else 8e5 - i * 1000, refs=[keys["B"]] if i == 1 else [])
    return keys, mods

c1 = os.path.join(t, "c1"); keys, mods = mk(c1)
names = lambda c: sorted(e.key for e in m.scan(c))
before = names(c1)
m.gc(c1, None, root=root, dry=True)
ok(names(c1) == before, "a dry run removes nothing")
r = m.gc(c1, None, root=root)
ok([e.key for e in r] == [keys["C"]], "no budget: only the unreferenced, old ArmASL entry C goes (B is referenced, D recent, A is the checkout's)")
ok(not os.path.exists(os.path.join(c1, keys["C"] + ".lock")), "its lock file goes with it")
ok(not [n for n in os.listdir(c1) if n.startswith(".gc-trash-")], "no trash is left")

c2 = os.path.join(t, "c2"); keys, mods = mk(c2)
total = sum(e.size for e in m.scan(c2))
budget = total - (6 << 20)
r = m.gc(c2, budget, root=root)
got = [e.key for e in r]
lru = [os.path.basename(mods[i]) for i in range(1, 7)]
gone_mods = [g for g in got if g in lru]
ok(got[:2] == [keys["C"], keys["B"]] and gone_mods == lru[:len(gone_mods)] and len(gone_mods) >= 2,
   "over budget: C (unreferenced), then least recently used first: B, m1, m2, ... (%d modules)" % len(gone_mods))
ok(keys["A"] not in got and os.path.basename(mods[7]) not in got and keys["D"] not in got,
   "the checkout's ArmASL entry and recently used entries stay")
ok(sum(e.size for e in m.scan(c2)) <= budget, "the cache fits the budget")

# A reader holding an entry's lock (shared, as restore does) keeps it, even with no budget and no grace.
c3 = os.path.join(t, "c3"); keys, mods = mk(c3)
rd = subprocess.Popen([sys.executable, "-I", "-c",
    "import fcntl,sys,time; f=open(sys.argv[1],'a+'); fcntl.flock(f,fcntl.LOCK_SH); print('held',flush=True); time.sleep(60)",
    mods[2] + ".lock"], stdout=subprocess.PIPE, text=True)
rd.stdout.readline()
m.gc(c3, 0, root=root, grace=0)
ok(os.path.isdir(mods[2]) and not os.path.isdir(mods[3]), "gc --max 0 --grace 0 keeps the entry being read, removes the others")
rd.kill(); rd.wait()
m.gc(c3, 0, root=root, grace=0)
ok(not os.path.isdir(mods[2]), "released, it goes")
ok(os.path.isdir(os.path.join(c3, keys["A"])), "the checkout's ArmASL entry is never collected")

# A use stamp (a restore) makes an entry recent again.
c4 = os.path.join(t, "c4"); keys, mods = mk(c4)
m.touch_use(mods[1])
m.gc(c4, 0, root=root)
ok(os.path.isdir(mods[1]) and not os.path.isdir(mods[2]), "a restore's use stamp keeps the entry for the grace period")

# lock_path retries when the lock file it waited on was removed by its holder.
lp = os.path.join(t, "x.lock")
h = m.lock_path(lp, shared=False)
os.unlink(lp)
h.close()
h2 = m.lock_path(lp, shared=True)
ok(os.path.samestat(os.fstat(h2.fileno()), os.stat(lp)), "a lock is taken on the file the path names now")
h2.close()

# Old leftovers: a trash and a publish temporary directory older than a day go; fresh ones stay.
c5 = os.path.join(t, "c5"); mk(c5)
old_trash, new_tmp = os.path.join(c5, ".gc-trash-old"), os.path.join(c5, "mods", "11", ".tmp-new")
for d, age in ((old_trash, 2e5), (new_tmp, 10)):
    os.makedirs(d); os.utime(d, (now - age, now - age))
m.gc(c5, None, root=root)
ok(not os.path.exists(old_trash) and os.path.exists(new_tmp), "a day-old trash is removed, a publish in progress is not")
sys.exit(fail)
PY

if [ -n "$sample" ]; then
  # A copy of this checkout and of the sample cache's entries for its modules (read-only use of
  # $sample); then, several rounds of: a fresh copy of those entries, a restore, and racing it a
  # collector that removes everything it can (gc --max 0 --grace 0 in a loop).
  mkdir -p "$t/w" "$t/pristine/mods"
  rsync -a --exclude=.git --exclude=.lake --exclude=artifacts "$root/" "$t/w/"
  n=0
  while read -r mod key; do
    [ "$key" != None ] && [ -f "$sample/mods/${key:0:2}/$key/MANIFEST.sha256" ] || continue
    mkdir -p "$t/pristine/mods/${key:0:2}"; cp -a "$sample/mods/${key:0:2}/$key" "$t/pristine/mods/${key:0:2}/"; n=$((n + 1))
  done < <(python3 -I "$tool" keys "$t/w")
  echo "sample: $n entries copied ($(du -sh "$t/pristine" | cut -f1))"
  fail=0
  for round in 1 2 3 4 5; do
    rm -rf "$t/cache" "$t/w/.lake/build" "$t/w/JanusASL/.lake/build"; cp -a "$t/pristine" "$t/cache"
    ( sleep "0.$((round * 2))"; while :; do python3 -I "$tool" gc "$t/cache" --max 0 --grace 0 >/dev/null 2>&1; done ) &
    gcp=$!
    python3 -I "$tool" restore "$t/w" "$t/cache" 2>&1 | tail -1
    kill "$gcp" 2>/dev/null; wait "$gcp" 2>/dev/null || true
    # Every module's outputs in the copy are either absent or exactly its entry's manifest (taken
    # from the sample, which holds the same bytes), never a mixture.
    python3 -I - "$tool" "$t/w" "$sample" "$round" <<'PY' || fail=1
import importlib.util, os, sys
tool, w, sample, rnd = sys.argv[1:5]
spec = importlib.util.spec_from_file_location("m", tool)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
ks = m.Keys(w)
good = absent = mixed = 0
for mod in ks.modules():
    k = ks.key(mod)
    if k is None:
        continue
    e = m.entry_dir(sample, k)
    if not os.path.isfile(os.path.join(e, "MANIFEST.sha256")):
        continue
    p = ks.pkg_of(mod)
    man = {r.split("/", 1)[1]: h for r, h in m.read_manifest(e).items()}
    have = [rel for rel in man if os.path.exists(os.path.join(p.dir, rel))]
    if not have:
        absent += 1
    elif len(have) == len(man) and all(m.sha_file(os.path.join(p.dir, rel)) == man[rel] for rel in man):
        good += 1
    else:
        mixed += 1
print(("ok   " if mixed == 0 else "FAIL ") + "round %s, a looping gc --max 0 --grace 0 racing the restore: %d modules restored whole, %d not restored, %d mixed" % (rnd, good, absent, mixed))
sys.exit(1 if mixed else 0)
PY
  done
  exit $fail
fi

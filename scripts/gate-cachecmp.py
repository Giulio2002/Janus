#!/usr/bin/env python3
"""Cache-vs-cold comparison for the nightly cold gate (scripts/nightly-cold-gate.sh; docs/TESTING.md
"Build cache policy").

    gate-cachecmp.py hashes WORKTREE OUT.json     SHA-256 of the build artifacts the ASL/Sail caches serve:
                                                  every ArmASL and JanusASL .olean (and their combined digest)
                                                  and the Sail oracle driver binary, plus the build
                                                  configuration the driver depends on (config:SAIL_SPLIT from
                                                  the environment, default 1, and config:SAIL_SPLIT_PARTS from
                                                  scripts/oracle-sail.sh), which is not part of the digest
    gate-cachecmp.py compare CACHED_OUT COLD_OUT  compare two gate output directories (timeline.jsonl and
                                                  artifact-hashes.json each)

Byte hashes of .olean files are not comparable across directories: Lean 4.34 stores the module's linter messages
(`Lean.Linter.lintLogExt`) in the .olean together with the absolute source path, so a module that emits a warning
differs between two worktrees (and from the copy a cache entry was published from) in thousands of bytes although every
declaration is the same. `hashes` therefore also records `sem:<module>` = a digest of what the module declares
(tools/oleandigest: every piece of the module re-serialized on its own: the constants and every environment extension
entry array, INCLUDING the compiled-code (IR) and simp/instance/attribute extensions), computed over all pieces EXCEPT the
message log. `compare` accepts a file-hash difference ONLY when the semantic digests are equal ("path-only", counted and
listed); any other difference, a module in only one run, or a missing semantic digest is a P0 / fail-closed.

`compare` exits 0 when the two runs agree on the commit, on the status of every prebuild step, stage, item
and lane (PASS/FAIL), and on every artifact hash; 1 with a "P0 CACHE BUG" report on any difference (the
cached run and the truly cold run of one commit must not differ: any difference means the cache served
something the inputs do not determine, or a key misses an input); 2 when a run cannot be compared (missing
or malformed files, different commits, or DIFFERENT BUILD CONFIGURATION: the cached and the cold run recorded
another SAIL_SPLIT or parts count, so their drivers differ by construction and a difference between them says nothing
about the cache; reported as a CONFIGURATION MISMATCH, never as a P0 CACHE BUG, and never a pass. Run both gates with
the same SAIL_SPLIT set explicitly (scripts/nightly-cold-gate.sh does))."""
import hashlib
import json
import os
import re
import subprocess
import sys

CONFIG = "config:"
SEM = "sem:"
# the one piece that carries the absolute source path (and only warnings): excluded from the semantic digest
PATH_PIECES = ("ext:Lean.Linter.lintLogExt",)


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def digest_tool(worktree):
    """Build (once) and return tools/oleandigest's executable of this worktree, or None."""
    d = os.path.join(worktree, "tools", "oleandigest")
    exe = os.path.join(d, ".lake", "build", "bin", "janus-olean-digest")
    if not os.path.isdir(d):
        return None
    r = subprocess.run(["lake", "build"], cwd=d, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0 or not os.access(exe, os.X_OK):
        sys.stderr.write("cachecmp: cannot build %s: %s\n" % (d, r.stdout[-500:]))
        return None
    return exe


def semantic(exe, paths):
    """{path: sha256 over its pieces except PATH_PIECES} from janus-olean-digest, run in batches."""
    out = {}
    pieces = {}
    for i in range(0, len(paths), 40):
        r = subprocess.run([exe] + paths[i:i + 40], stdout=subprocess.PIPE, text=True)
        for line in r.stdout.splitlines():
            w = line.split()
            if len(w) == 4:
                pieces.setdefault(w[0], []).append((w[1], w[2], w[3]))
    for p in paths:
        ps = pieces.get(p)
        if not ps:
            continue
        h = hashlib.sha256()
        for name, dg, n in sorted(ps):
            if name in PATH_PIECES:
                continue
            h.update(("%s %s %s\n" % (name, dg, n)).encode())
        out[p] = h.hexdigest()
    return out


def hashes(worktree):
    out = {}
    lib = os.path.join(worktree, "JanusASL", ".lake", "build", "lib", "lean")
    oleans = []
    for d, dirs, files in os.walk(lib):
        dirs.sort()
        for f in sorted(files):
            if f.endswith(".olean"):
                p = os.path.join(d, f)
                out["olean:" + os.path.relpath(p, lib)] = sha_file(p)
                oleans.append(p)
    exe = digest_tool(worktree)
    if exe and oleans:
        for p, dg in semantic(exe, oleans).items():
            out[SEM + os.path.relpath(p, lib)] = dg
    drv = os.path.join(worktree, "oracle-sail", "target", "release", "janus-oracle-sail")
    if os.path.isfile(drv):
        out["sail-driver"] = sha_file(drv)
    out.update(config(worktree))
    # `combined`: the semantic digests and the driver (path independent); `combined:bytes` the file hashes (informational)
    h = hashlib.sha256()
    for k in sorted(k for k in out if not k.startswith(CONFIG) and not k.startswith("olean:")):
        h.update(("%s %s\n" % (k, out[k])).encode())
    out["combined"] = h.hexdigest()
    hb = hashlib.sha256()
    for k in sorted(k for k in out if k.startswith("olean:")):
        hb.update(("%s %s\n" % (k, out[k])).encode())
    out["combined:bytes"] = hb.hexdigest()
    return out


def config(worktree):
    """The build configuration the Sail driver is a function of, recorded next to its hash."""
    parts = "unknown"
    try:
        m = re.search(r"^SAIL_SPLIT_PARTS=(\d+)\s*$", open(os.path.join(worktree, "scripts", "oracle-sail.sh")).read(), re.M)
        if m:
            parts = m.group(1)
    except OSError:
        pass
    return {CONFIG + "SAIL_SPLIT": os.environ.get("SAIL_SPLIT", "1"), CONFIG + "SAIL_SPLIT_PARTS": parts}


def load_timeline(d):
    rows = []
    with open(os.path.join(d, "timeline.jsonl")) as f:
        for line in f:
            if line.strip():
                rows.append(json.loads(line))
    gate = next((r for r in rows if r.get("kind") == "gate"), None)
    st = {}
    for r in rows:
        k = r.get("kind")
        if k in ("prebuild", "stage"):
            st["%s:%s" % (k, r["name"])] = "PASS" if r.get("rc") in (0, "0") else "FAIL"
        elif k == "item":
            st["item:%s:%s" % (r.get("pool"), r["id"])] = "PASS" if str(r.get("status")).upper().startswith("PASS") else "FAIL(%s)" % r.get("status")
    return gate, st


def compare(cached, cold):
    try:
        g1, s1 = load_timeline(cached)
        g2, s2 = load_timeline(cold)
        h1 = json.load(open(os.path.join(cached, "artifact-hashes.json")))
        h2 = json.load(open(os.path.join(cold, "artifact-hashes.json")))
    except (OSError, ValueError, KeyError) as ex:
        print("cachecmp: cannot compare the runs: %s" % ex)
        return 2
    if not g1 or not g2 or g1.get("commit") != g2.get("commit"):
        print("cachecmp: the runs are of different commits (%s vs %s): not comparable" % (
            (g1 or {}).get("commit"), (g2 or {}).get("commit")))
        return 2
    # an unrecorded setting (artifact-hashes.json of an older gate) is a mismatch too: fail closed
    cfg = [k for k in sorted(set(h1) | set(h2) | {CONFIG + "SAIL_SPLIT", CONFIG + "SAIL_SPLIT_PARTS"})
           if k.startswith(CONFIG) and (h1.get(k) is None or h1.get(k) != h2.get(k))]
    if cfg:
        print("cachecmp: CONFIGURATION MISMATCH (not a cache verdict): the cached and the cold run of commit %s were built with different settings:" % g1.get("commit"))
        for k in cfg:
            print("  %s: cached %s, cold %s" % (k[len(CONFIG):], h1.get(k, "not recorded"), h2.get(k, "not recorded")))
        print("cachecmp: not comparable (the Sail drivers differ by construction). Re-run both with the same SAIL_SPLIT set explicitly.")
        return 2
    diffs = []
    for k in sorted(set(s1) | set(s2)):
        a, b = s1.get(k, "MISSING"), s2.get(k, "MISSING")
        if a != b:
            diffs.append("%s: cached run %s, cold run %s" % (k, a, b))
    path_only = []
    for k in sorted(k for k in set(h1) | set(h2) if not k.startswith(CONFIG)):
        a, b = h1.get(k), h2.get(k)
        if k == "combined:bytes":
            continue
        if k.startswith(SEM):
            # judged together with the file hash of the same module below (when that module exists in both runs)
            ok = k[len(SEM):]
            if ("olean:" + ok) in h1 and ("olean:" + ok) in h2:
                continue
        if k.startswith("olean:"):
            sk = SEM + k[len("olean:"):]
            sa, sb = h1.get(sk), h2.get(sk)
            if a and b and a == b:
                if sa and sb and sa != sb:
                    diffs.append("artifact %s: identical files but different semantic digests (cached %s, cold %s)" % (k, sa[:16], sb[:16]))
                continue
            if a and b:
                if sa and sb and sa == sb:
                    path_only.append(k[len("olean:"):])
                elif not sa or not sb:
                    diffs.append("artifact %s: file hashes differ and a semantic digest is not recorded (cached %s, cold %s): fail closed" % (
                        k, "yes" if sa else "NO", "yes" if sb else "NO"))
                else:
                    diffs.append("artifact %s: cached %s, cold %s; SEMANTIC digests differ (cached %s, cold %s): the module declares something different" % (
                        k, a[:16], b[:16], sa[:16], sb[:16]))
                continue
        if a != b:
            diffs.append("artifact %s: cached %s, cold %s" % (k, (a or "MISSING")[:16], (b or "MISSING")[:16]))
    if diffs:
        print("P0 CACHE BUG: the cached gate and the cold gate of commit %s disagree (%d differences):" % (g1.get("commit"), len(diffs)))
        for d in diffs:
            print("  " + d)
        print("P0: owner is the main session (docs/TESTING.md 'Build cache policy'): treat every cached gate result since the last agreeing nightly as unproven.")
        return 1
    if path_only:
        print("cachecmp: %d module file hashes differ ONLY by the stored message log / source path (semantic digests equal): %s" % (
            len(path_only), ", ".join(path_only[:40]) + (" ..." if len(path_only) > 40 else "")))
    print("cachecmp: cached and cold runs of commit %s agree on %d prebuild steps/stages/items/lanes and %d artifact hashes (SAIL_SPLIT=%s, %s parts; %d path-only)" % (
        g1.get("commit"), len(s1), len([k for k in h1 if not k.startswith(CONFIG)]), h1[CONFIG + "SAIL_SPLIT"], h1[CONFIG + "SAIL_SPLIT_PARTS"], len(path_only)))
    return 0


def main(a):
    if len(a) == 3 and a[0] == "hashes":
        json.dump(hashes(a[1]), open(a[2], "w"), sort_keys=True, indent=1)
        return 0
    if len(a) == 3 and a[0] == "compare":
        return compare(a[1], a[2])
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

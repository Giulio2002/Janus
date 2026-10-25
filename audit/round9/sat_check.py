"""Round 9 SAT row: every runtime contract defined in Janus/Contracts/*.lean (a `def … : Prop`
whose body is a `Summary`, possibly under `∀`) must have a kernel-checked non-vacuity witness
`theorem <name>_satisfiable` in the framework module `Janus.Contracts.<File>Sat` (for
`<File>Amd64.lean`: `<File>SatAmd64`), which Janus.lean must import, where <name> is the
contract's name with `Contract` removed and the first letter lower-cased
(`NewobjectContract64` → `newobject64_satisfiable`, `Access1` → `access1_satisfiable`).
Contracts listed in audit/round9/sat-pending.txt are reported as OPEN (with their owner) instead
of failing; any other missing witness fails the row.
Usage: python3 -I audit/round9/sat_check.py ROOT"""
import os, re, subprocess, sys
root = os.path.realpath(sys.argv[1])

# Round 10: read only the tree under test. Every file read must be a regular file whose real path
# is inside ROOT (no symbolic link out of the tree, no other checkout, no cache copy). In a git
# checkout the files are the tracked and the untracked-but-not-ignored ones under Janus/ (a stray
# ignored file is not part of the tree); elsewhere (the self-test's copy) a walk that follows no
# link. Anything else fails the row, with the path, instead of being read.
def tree_files():
    out = None
    if os.path.exists(os.path.join(root, ".git")):
        try:
            out = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached", "--others",
                                  "--exclude-standard", "--", "Janus", "Janus.lean"],
                                 capture_output=True, check=True).stdout.decode().split("\0")
        except (OSError, subprocess.CalledProcessError):
            out = None
    if out is None:
        out = ["Janus.lean"]
        for dp, dns, fs in os.walk(os.path.join(root, "Janus")):
            dns[:] = [d for d in dns if not os.path.islink(os.path.join(dp, d))]
            out += [os.path.relpath(os.path.join(dp, f), root) for f in fs]
    files = {}
    for rel in sorted(set(r for r in out if r)):
        p = os.path.join(root, rel)
        if not os.path.lexists(p):
            continue   # tracked but deleted in the work tree
        rp = os.path.realpath(p)
        if os.path.islink(p) or not os.path.isfile(p) or os.path.commonpath([rp, root]) != root:
            print("SAT ERROR   %s is not a regular file of the tree under test %s (it resolves to %s)" % (rel, root, rp))
            sys.exit(1)
        files[rel] = p
    return files
FILES = tree_files()
print("SAT tree    %s (%d files)" % (root, len(FILES)))
contracts = []
for rel in sorted(r for r in FILES if r.startswith("Janus/Contracts/") and r.count("/") == 2):
    f = rel.split("/")[-1]
    if not f.endswith(".lean"):
        continue
    lines = open(FILES[rel], encoding="utf-8").read().split("\n")
    for i, l in enumerate(lines):
        m = re.match(r"^def ([A-Z][A-Za-z0-9]*)\b", l)
        if not m:
            continue
        body = []
        for l2 in lines[i:i + 6]:
            body.append(l2)
            if l2.strip() == "":
                break
        text = " ".join(body)
        if not re.search(r":\s*Prop\s*:=", text):
            continue
        after = text.split(":=", 1)[1]
        if re.match(r"\s*(∀[^,]*,\s*)?([\w.]*\.)?Summary\b", after):
            contracts.append((f, m.group(1)))
imports = set(re.findall(r"^import (\S+)", open(FILES["Janus.lean"], encoding="utf-8").read(), re.M))
sat = {}
for rel, p in FILES.items():
    if True:
        if rel.startswith("Janus/") and rel.endswith(".lean"):
            mod = rel[:-5].replace("/", ".")
            text = open(p, encoding="utf-8").read()
            for m in re.finditer(r"^theorem (\w+)_satisfiable\b(.*?):=", text, re.M | re.S):
                # round 10: the witness must be about the contract (its statement names it and
                # gives a state), not just a theorem of that name
                sat.setdefault(m.group(1), []).append((mod, m.group(2)))
pending = {}
pf = os.path.join(root, "audit", "round9", "sat-pending.txt")
if os.path.isfile(pf) and not os.path.islink(pf):
    for l in open(pf, encoding="utf-8"):
        l = l.split("#", 1)[0].strip()
        if l:
            name, owner = (l.split(None, 1) + [""])[:2]
            pending[name] = owner
ok = missing = opened = 0
for f, c in contracts:
    w = c.replace("Contract", "")
    w = w[0].lower() + w[1:]
    stem = f[:-5]
    satmod = "Janus.Contracts." + (stem[:-5] + "SatAmd64" if stem.endswith("Amd64") else stem + "Sat")
    mods = [m for m, stmt in sat.get(w, []) if m in imports and m == satmod
            and re.search(r"\b%s\b" % re.escape(c), stmt) and re.search(r"∃[^,]*\bs\b", stmt)]
    if mods:
        ok += 1
        print("  SAT ok      %-22s %-20s %s_satisfiable (%s)" % (c, f, w, mods[0]))
    elif f + ":" + c in pending:
        opened += 1
        print("  SAT OPEN    %-22s %-20s no %s_satisfiable yet (%s)" % (c, f, w, pending[f + ":" + c]))
    else:
        missing += 1
        print("  SAT MISSING %-22s %-20s no %s_satisfiable in %s (imported by Janus.lean)" % (c, f, w, satmod))
print("SAT contracts=%d witnessed=%d open=%d missing=%d" % (len(contracts), ok, opened, missing))
sys.exit(1 if missing or not contracts else 0)

"""Round 9 SAT row: every runtime contract defined in Janus/Contracts/*.lean (a `def … : Prop`
whose body is a `Summary`, possibly under `∀`, or whose name ends in `Contract`, such as R7's
`MorestackContract`, a relation over the prologue's `morestack` call states) must have a kernel-checked non-vacuity witness
`theorem <name>_satisfiable` in the framework module `Janus.Contracts.<File>Sat` (for
`<File>Amd64.lean`: `<File>SatAmd64`), which Janus.lean must import, where <name> is the
contract's name with `Contract` removed and the first letter lower-cased
(`NewobjectContract64` → `newobject64_satisfiable`, `Access1` → `access1_satisfiable`).
Contracts listed in audit/round9/sat-pending.txt are reported as OPEN (with their owner) instead
of failing; any other missing witness fails the row.
Usage: python3 -I audit/round9/sat_check.py ROOT"""
import os, re, sys
root = sys.argv[1]
cdir = os.path.join(root, "Janus", "Contracts")
contracts = []
for f in sorted(os.listdir(cdir)):
    if not f.endswith(".lean"):
        continue
    lines = open(os.path.join(cdir, f), encoding="utf-8").read().split("\n")
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
        if re.match(r"\s*(∀[^,]*,\s*)?([\w.]*\.)?Summary\b", after) or m.group(1).endswith("Contract"):
            contracts.append((f, m.group(1)))
imports = set(re.findall(r"^import (\S+)", open(os.path.join(root, "Janus.lean"), encoding="utf-8").read(), re.M))
sat = {}
for dp, _, fs in os.walk(os.path.join(root, "Janus")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
            for n in re.findall(r"^theorem (\w+)_satisfiable\b", open(p, encoding="utf-8").read(), re.M):
                sat.setdefault(n, []).append(mod)
pending = {}
pf = os.path.join(root, "audit", "round9", "sat-pending.txt")
if os.path.exists(pf):
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
    mods = [m for m in sat.get(w, []) if m in imports and m == satmod]
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

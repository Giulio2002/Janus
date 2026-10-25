"""Round 9 SAT row: every runtime contract defined in Janus/Contracts/*.lean (a `def … : Prop`
whose body is a `Summary`, possibly under `∀`), and every external-stub contract (a `def … :
Contract`) there and in Janus/FFI.lean and Janus/Amd64/FFI.lean (K2: the trusted cgo, callback,
libc and setjmp contracts), must have a kernel-checked non-vacuity witness
`theorem <name>_satisfiable` in the framework module `Janus.Contracts.<File>Sat` (for
`<File>Amd64.lean`: `<File>SatAmd64`; for Janus/FFI.lean `Janus.FFISat`, for Janus/Amd64/FFI.lean
`Janus.Amd64.FFISat`), which Janus.lean must import, where <name> is the
contract's name with `Contract` removed and the first letter lower-cased
(`NewobjectContract64` → `newobject64_satisfiable`, `Access1` → `access1_satisfiable`).
Contracts listed in audit/round9/sat-pending.txt are reported as OPEN (with their owner) instead
of failing; any other missing witness fails the row.
Usage: python3 -I audit/round9/sat_check.py ROOT"""
import os, re, sys
root = sys.argv[1]
cdir = os.path.join(root, "Janus", "Contracts")
files = [(f, os.path.join(cdir, f), "Janus.Contracts." + (f[:-5][:-5] + "SatAmd64" if f[:-5].endswith("Amd64") else f[:-5] + "Sat"))
         for f in sorted(os.listdir(cdir)) if f.endswith(".lean")]
files += [("FFI.lean", os.path.join(root, "Janus", "FFI.lean"), "Janus.FFISat"),
          ("Amd64/FFI.lean", os.path.join(root, "Janus", "Amd64", "FFI.lean"), "Janus.Amd64.FFISat")]
contracts = []
for f, path, satmod in files:
    if not os.path.exists(path):
        continue
    lines = open(path, encoding="utf-8").read().split("\n")
    for i, l in enumerate(lines):
        m = re.match(r"^def ([A-Z][A-Za-z0-9]*)(?![.\w])", l)
        if not m:
            continue
        body = []
        for l2 in lines[i:i + 6]:
            body.append(l2)
            if l2.strip() == "":
                break
        text = " ".join(body)
        if re.search(r":\s*Contract\s*(where|:=)", text.split(":=", 1)[0] + ":=" if ":=" in text else text) or \
                re.search(r":\s*Contract\s*where", text):
            contracts.append((f, m.group(1), satmod))
            continue
        if not re.search(r":\s*Prop\s*:=", text):
            continue
        after = text.split(":=", 1)[1]
        if re.match(r"\s*(∀[^,]*,\s*)?([\w.]*\.)?Summary\b", after):
            contracts.append((f, m.group(1), satmod))
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
for f, c, satmod in contracts:
    w = c.replace("Contract", "") or c
    w = w[0].lower() + w[1:]
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

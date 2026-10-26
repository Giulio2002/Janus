"""Round 9 SAT row: every runtime contract defined in Janus/Contracts/*.lean (a `def … : Prop`
whose body is a `Summary`, possibly under `∀`), and every external-stub contract (a `def … :
Contract`) there and in Janus/FFI.lean and Janus/Amd64/FFI.lean (K2: the trusted cgo, callback,
libc and setjmp contracts), must have a kernel-checked non-vacuity witness
`theorem <name>_satisfiable` in the framework module `Janus.Contracts.<File>Sat` (for
`<File>Amd64.lean`: `<File>SatAmd64`; for Janus/FFI.lean `Janus.FFISat`, for Janus/Amd64/FFI.lean
`Janus.Amd64.FFISat`), which Janus.lean must import, where <name> is the
contract's name with `Contract` removed and the first letter lower-cased
(`NewobjectContract64` → `newobject64_satisfiable`, `Access1` → `access1_satisfiable`).
Round 10: the witness's statement must name the contract and give a state, and only the tree
under test is read.
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
external = set()   # `def … : Contract` (external stubs): witnessed by `.Total`
srcs = [(rel.split("/")[-1], rel, "Janus.Contracts." + (rel.split("/")[-1][:-10] + "SatAmd64"
         if rel.split("/")[-1][:-5].endswith("Amd64") else rel.split("/")[-1][:-5] + "Sat"))
        for rel in sorted(FILES) if rel.startswith("Janus/Contracts/") and rel.count("/") == 2
        and rel.endswith(".lean")]
srcs += [(f, rel, mod) for f, rel, mod in [("FFI.lean", "Janus/FFI.lean", "Janus.FFISat"),
         ("Amd64/FFI.lean", "Janus/Amd64/FFI.lean", "Janus.Amd64.FFISat")] if rel in FILES]
for f, rel, satmod in srcs:
    lines = open(FILES[rel], encoding="utf-8").read().split("\n")
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
            external.add(m.group(1))
            continue
        if not re.search(r":\s*Prop\s*:=", text):
            continue
        after = text.split(":=", 1)[1]
        if re.match(r"\s*(∀[^,]*,\s*)?([\w.]*\.)?Summary\b", after):
            contracts.append((f, m.group(1), satmod))
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

# A witness statement is about contract c when it names c and gives a call state (`∃ … s`), or
# names a definition of the framework whose body does (rtstr's `Sat.Satisfiable spec`), or, for
# an external-stub contract (`: Contract`), states `(c …).Total` (every safe state has a successor).
DEFS = {}
for rel, p in FILES.items():
    if rel.startswith("Janus/") and rel.endswith(".lean"):
        for m in re.finditer(r"^def (\w+)\b(.*?)(?=^\S)", open(p, encoding="utf-8").read(), re.M | re.S):
            DEFS.setdefault(m.group(1), []).append(m.group(2))
def names_state(c, text):
    return re.search(r"\b%s\b" % re.escape(c), text) and re.search(r"∃[^,]*\bs\b", text)
def about(c, stmt):
    if names_state(c, stmt):
        return True
    if c in external and re.search(r"\(%s\b.*\)\.Total|\b%s\.Total" % (re.escape(c), re.escape(c)), stmt, re.S):
        return True
    for d in set(re.findall(r"\b(?:\w+\.)*(\w+)\b", stmt)):
        if d != c and any(names_state(c, b) for b in DEFS.get(d, [])):
            return True
    return False
pending = {}
pf = os.path.join(root, "audit", "round9", "sat-pending.txt")
if os.path.isfile(pf) and not os.path.islink(pf):
    for l in open(pf, encoding="utf-8"):
        l = l.split("#", 1)[0].strip()
        if l:
            name, owner = (l.split(None, 1) + [""])[:2]
            pending[name] = owner
ok = missing = opened = 0
for f, c, satmod in contracts:
    w = c.replace("Contract", "") or c
    w = w[0].lower() + w[1:]
    mods = [m for m, stmt in sat.get(w, []) if m in imports and m == satmod and about(c, stmt)]
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

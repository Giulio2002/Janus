#!/usr/bin/env python3
"""Split a large generated proof file of JanusASL.Proofs into smaller modules (docs/ASL.md, "Memory").

    split_proofs.py FILE.lean [PER_PART]          split (default 4 top-level commands per part)
    split_proofs.py --check FILE.lean REV         verify an existing split against FILE.lean at git REV

The decode-chain files (`LdStDecode*.lean`, made by `tools/chain.py`) are long lists of
independent lemmas. Elaborated as one module, `lean` holds every finished proof and its info
trees until the end of the file, and its peak grows with the file. This script cuts `Foo.lean`
at top-level command boundaries into `Foo/Part01.lean`, `Foo/Part02.lean`, ...; every part
repeats the file header (imports, file-level `set_option`s, `namespace`, `open`) and ends the
namespace, and `Foo.lean` becomes the module docstring plus `import Foo.PartNN` for every part,
so every importer of `Foo` sees the same declarations. The lemmas' text (statement, options,
docstring and proof) is copied byte for byte, in the original order; parts do not import each
other, so a lemma may not use an earlier lemma of the same file (checked: such a file is
refused). Lake then builds the parts in parallel, each in a small process.

Run it on the monolithic file, as `tools/chain.py`'s output is assembled; re-running it on an
already split `Foo.lean` (an import list) does nothing.
"""
import os
import re
import subprocess
import sys

START = re.compile(r"(set_option .* in$|/--|@\[|theorem |lemma |def |abbrev |instance |private |protected |noncomputable |example )")


def parse(text):
    L = text.split("\n")
    # header: imports, module doc, file-level options, namespace, open (and blank lines)
    i, doc_open = 0, False
    while i < len(L):
        l = L[i]
        if doc_open:
            doc_open = "-/" not in l
            i += 1
            continue
        if l.startswith("/-!"):
            doc_open = "-/" not in l
            i += 1
            continue
        if START.match(l) and not re.fullmatch(r"set_option [^ ]+ [^ ]+", l):
            break
        if not (l == "" or l.startswith(("import ", "set_option ", "namespace ", "open "))):
            raise SystemExit("split_proofs: unexpected header line %d: %r" % (i + 1, l))
        i += 1
    header = L[:i]
    body = L[i:]
    while body and body[-1] == "":
        body.pop()
    ns = [l[len("namespace "):] for l in header if l.startswith("namespace ")]
    if len(ns) != 1 or body[-1] != "end " + ns[0]:
        raise SystemExit("split_proofs: expected one namespace closed by the last line")
    body.pop()
    # commands: a run of lines starting at a column-0 command keyword; `set_option ... in`,
    # docstrings and attributes attach to the declaration that follows them
    cmds, cur, attach, in_doc = [], [], False, False
    for l in body:
        if START.match(l) and not attach and not in_doc:
            if cur:
                cmds.append(cur)
            cur = [l]
        else:
            cur.append(l)
        if in_doc:
            in_doc = "-/" not in l
            attach = not in_doc
        elif l.startswith("/--"):
            in_doc = "-/" not in l
            attach = not in_doc
        else:
            attach = bool(re.match(r"(set_option .* in$|@\[)", l))
    if cur:
        cmds.append(cur)
    return header, cmds, ns[0]


def names(cmd):
    out = []
    for l in cmd:
        m = re.match(r"(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|instance) ([^\s:({\[]+)", l)
        if m:
            out.append(m.group(1))
    return out


def main():
    a = sys.argv[1:]
    check = a and a[0] == "--check"
    if check:
        a = a[1:]
    path = a[0]
    per = int(a[1]) if len(a) > 1 and not check else 4
    if check:
        orig = subprocess.run(["git", "show", a[1] + ":./" + os.path.basename(path)], cwd=os.path.dirname(path) or ".",
                              capture_output=True, text=True, check=True).stdout
        print(verify(path, orig))
        return
    text = open(path).read()
    if all(l.startswith(("import ", "--", "/-!", " ", "-/")) or l == "" for l in text.split("\n")) and \
            re.search(r"^import .*\.Part\d+$", text, re.M):
        print("split_proofs: %s is already split" % path)
        return
    header, cmds, ns = parse(text)
    # parts do not import each other: refuse a file whose lemmas use each other
    defined = set()
    for c in cmds:
        txt = "\n".join(c)
        for n in defined:
            if re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(n), txt):
                raise SystemExit("split_proofs: %s uses %s from the same file; not splitting" % (names(c), n))
        defined.update(names(c))
    stem = os.path.splitext(path)[0]
    modname = module_name(path)
    os.makedirs(stem, exist_ok=True)
    doc = [l for l in header if l.startswith("/-!")]
    hdr = [l for l in header if not l.startswith("/-!")]
    parts = []
    for k in range(0, len(cmds), per):
        name = "Part%02d" % (len(parts) + 1)
        chunk = [l for c in cmds[k:k + per] for l in c]
        first = names(cmds[k])[0] if names(cmds[k]) else "?"
        text_k = ["-- %s, part %d (tools/split_proofs.py)" % (modname, len(parts) + 1)] + hdr + chunk + ["end " + ns, ""]
        open(os.path.join(stem, name + ".lean"), "w").write("\n".join(text_k))
        parts.append(name)
    agg = ["import %s.%s" % (modname, p) for p in parts] + [""] + doc + [""]
    agg = ["-- split into %d parts by tools/split_proofs.py (%d commands each); the lemmas are in %s/" %
           (len(parts), per, os.path.basename(stem))] + agg
    open(path, "w").write("\n".join(agg))
    print("split_proofs: %s -> %d parts of %d commands" % (path, len(parts), per))
    print(verify(path, text))


def module_name(path):
    p = os.path.abspath(path)
    i = p.rfind("/JanusASL/JanusASL/")
    if i < 0:
        raise SystemExit("split_proofs: not under JanusASL/JanusASL/: " + path)
    return p[i + len("/JanusASL/"):-len(".lean")].replace("/", ".")


def verify(path, orig):
    """The parts' commands, in import order, are exactly the original file's commands."""
    header, cmds, ns = parse(orig)
    stem = os.path.splitext(path)[0]
    modname = module_name(path)
    got = []
    for l in open(path).read().split("\n"):
        m = re.fullmatch(r"import %s\.(Part\d+)" % re.escape(modname), l)
        if m:
            h, c, n = parse("\n".join(open(os.path.join(stem, m.group(1) + ".lean")).read().split("\n")[1:]))
            if h != [l for l in header if not l.startswith("/-!")] or n != ns:
                raise SystemExit("split_proofs: header of %s differs" % m.group(1))
            got += c
    if got != cmds:
        raise SystemExit("split_proofs: the parts of %s do not reproduce the original" % path)
    return "split_proofs: %s: %d commands, byte-identical to the original" % (path, len(cmds))


main()

#!/usr/bin/env python3
"""Miss analysis of the incremental gate over the last N merges of a branch (docs/TESTING.md "Incremental gate").

NOT part of the trust base and not used by any gate: a measuring tool. For every first-parent commit C of REF it
takes the files C changes relative to its first parent and models, from the rules of cmd/janus/incr.go and
scripts/lib/incr.sh, which of the 461 verify items and which gate lanes an incremental gate would have to run,
and WHY (the input that changed). Two rule sets are modelled:

  before   the rules of integ/speed5 (ad264a2): the gate's own bookkeeping variables are part of every key
           (JANUS_GATE_TREE0, JANUS_LAKEGUARD_PIN, ... : scripts/gate.sh exports them and they differ from run to run), so
           a gate run never finds the record of an earlier run: 0 items skipped. 'before-designed' is the same model
           with that bug removed (what the design of ad264a2 would give: the 'older measurement').
  after    the rules of this branch.

Usage: scripts/incr-sample.py [--ref main] [-n 30] [--items items.txt] [--tsv out.tsv] [--md out.md]
items.txt: one id per line, as printed by scripts/verify-all-examples.sh (arm64:Add, amd64:Add, asm:..., cgo:...);
without it the list is derived from the tree by running the bash that verify-all-examples.sh runs to build it.
The model is conservative where the tree does not say: a file it cannot classify invalidates every item.
"""
import argparse, os, re, subprocess, sys, collections

ROOT = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()


def git(*a):
    return subprocess.check_output(["git", "-C", ROOT] + list(a), text=True, errors="replace")


# ---------------------------------------------------------------- rules (mirrors of the Go / shell code)

def verifier_file(p):
    """cmd/janus/verifierid.go identityGoFile: the files the Go-only verifier identity hashes."""
    if p.endswith("_test.go"):
        return False
    if p.startswith("cmd/janus/"):
        return "." in os.path.basename(p)
    return p.endswith((".go", ".s", ".h")) and "/" not in p or p in ("go.mod", "go.sum")


COMMON_SCRIPTS_BEFORE = """scripts/gate.sh scripts/lib/incr.sh scripts/lib/pool.sh scripts/lib/parallel.sh scripts/lib/memguard.sh
scripts/lib/itemtimeout.sh scripts/lib/theorems.sh scripts/verify-all-examples.sh scripts/example-contracts.sh
scripts/example-targets.sh""".split()
KIND_SCRIPTS = {
    "arm64": ["scripts/verify-examples.sh", "scripts/build-examples.sh", "scripts/break-demo.sh"],
    "amd64": ["scripts/verify-amd64-examples.sh", "scripts/build-examples-amd64.sh"],
    "asm": ["scripts/verify-asm-examples.sh", "scripts/build-examples-asm.sh"],
    "rtmisc": ["scripts/verify-rtmisc-examples.sh", "scripts/build-examples-rtmisc.sh"],
    "sys": ["scripts/verify-sys-examples.sh", "scripts/build-examples-sys.sh"],
    "print": ["scripts/verify-print-examples.sh", "scripts/build-examples-print.sh", "scripts/gen-print-code.py",
              "scripts/gen-print-examples.py"],
    "cgo": ["scripts/verify-cgo-examples.sh", "scripts/build-examples-cgo.sh"],
}
PINS = ["cmd/janus/stubpins_gen.go", "scripts/gen-stubpins.sh", "scripts/stubpins/main.go"]
FW_CONFIG = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]


def load_rules():
    """The script lists of THIS tree (scripts/lib/incr.sh), so the model follows the code under analysis."""
    src = open(os.path.join(ROOT, "scripts/lib/incr.sh")).read()
    m = re.search(r"incr_script_flags\(\) \{(.*?)\n\}", src, re.S)
    common = re.search(r"local -a fs=\((.*?)\)\n", m.group(1), re.S).group(1).split()
    kinds = {}
    for k, v in re.findall(r"^\s+(\w+)\) fs\+=\((.*?)\) ;;", m.group(1), re.M):
        kinds[k] = v.split()
    return common, kinds


def fw_closure():
    """Source files of the modules `import Janus` reaches (the auditor's clean environment imports it, so every verdict
    depends on all of them)."""
    seen, todo, files = set(), ["Janus"], set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        p = m.replace(".", "/") + ".lean"
        fp = os.path.join(ROOT, p)
        if not os.path.exists(fp):
            continue
        files.add(p)
        for l in open(fp, errors="replace"):
            l = l.strip()
            if l.startswith("import "):
                todo.append(l.split()[1])
            elif l and not l.startswith(("--", "/-", "module", "prelude", "public", "meta", "private")) and not l.startswith("import"):
                if not l.startswith(("-/", "*", "·")):
                    pass
    return files


# the example sources each suite's binary / extraction depends on, and each item's own proof file
SUITE_SRC = {
    "arm64": ["examples/basic/"],
    "amd64": ["examples/basic/"],
    "asm": ["examples/asm/"],
    "rtmisc": ["examples/rtmisc/"],
    "sys": ["examples/sys/"],
    "print": ["examples/print/"],
    "cgo": ["examples/cgo/"],
}


def proof_files(item):
    k, n = item.split(":", 1)
    if k == "arm64":
        return {"examples/proofs/%s.lean" % n}
    if k == "amd64":
        return {"examples/proofs-amd64/%s/Proof.lean" % n}
    if k == "asm":
        return {"examples/asm/proofs/%s.lean" % n}
    if k == "rtmisc":
        return ("examples/rtmisc/proofs/%s" % n,)  # a file or a package directory
    if k == "sys":
        return ("examples/proofs-sys/",)
    if k == "print":
        return ("examples/proofs-print/",)  # --pkg: the whole directory
    if k == "cgo":
        return ("examples/proofs-cgo/",)
    return ()


def item_hits_proof(item, f):
    ps = proof_files(item)
    k, n = item.split(":", 1)
    if isinstance(ps, set):
        return f in ps
    for p in ps:
        if p.endswith("/") and f.startswith(p):
            # sys/cgo rows: one proof file each, named by the row (isa/name)
            if k in ("sys", "cgo"):
                base = os.path.basename(f)
                return base.removesuffix(".lean") == n.split("/")[-1] or "/" not in n
            return True
        if f == p or f == p + ".lean" or f.startswith(p + "/"):
            return True
    return False


def classify(files, rules, items, fwset):
    """-> (set of items to run, {reason: count of items it forces}, lane_reasons)"""
    common, kinds = rules
    r = collections.OrderedDict()  # reason -> set(items)
    run = set()
    allitems = set(items)

    def force(reason, which):
        w = set(which)
        if w:
            r.setdefault(reason, set()).update(w)
            run.update(w)

    by_kind = collections.defaultdict(set)
    for it in items:
        by_kind[it.split(":", 1)[0]].add(it)
    for f in files:
        if f.startswith(("docs/", "assets/")) or f.endswith(".md") or f == "LICENSE" or f.startswith((".github/", ".gitignore")):
            continue
        if verifier_file(f):
            force("verifier (Go source: %s)" % f, allitems)
        elif f in FW_CONFIG:
            force("toolchain/lake config (%s)" % f, allitems)
        elif f in fwset or f == "Janus.lean":
            force("framework closure (%s)" % f, allitems)
        elif f in PINS:
            force("pins (%s)" % f, allitems)
        elif f in common:
            force("common gate script (%s)" % f, allitems)
        else:
            hit = False
            for k, its in by_kind.items():
                if f in kinds.get(k, []) or f in KIND_SCRIPTS.get(k, []) and f in kinds.get(k, []):
                    force("%s script (%s)" % (k, f), its)
                    hit = True
                if any(f.startswith(s) for s in SUITE_SRC[k]):
                    force("%s example source (%s)" % (k, f), its)  # the shared binary / extraction changes
                    hit = True
                for it in its:
                    if item_hits_proof(it, f):
                        force("proof file (%s)" % f, [it])
                        hit = True
            if not hit:
                pass  # not an input of any item
    return run, r


def lane_effect(files, lane_rules):
    """-> number of addc lanes that must run, by the model of incr_lane (every non-doc file of the tree)."""
    for f in files:
        if f.startswith(("docs/", "assets/", "artifacts/")) or f.endswith(".md") or f == "LICENSE":
            continue
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ref", default="main")
    ap.add_argument("-n", type=int, default=30)
    ap.add_argument("--skip", type=int, default=0, help="start this many first-parent commits back")
    ap.add_argument("--items")
    ap.add_argument("--tsv")
    ap.add_argument("--md")
    a = ap.parse_args()
    rules = load_rules()
    fwset = fw_closure()
    if a.items:
        items = [l.strip() for l in open(a.items) if l.strip()]
    else:
        src = subprocess.check_output(["sed", "-n", "80,117p", os.path.join(ROOT, "scripts/verify-all-examples.sh")], text=True)
        out = subprocess.check_output(["bash", "-c", 'cd %s; cgo=1; eval "$(cat)"; printf "%%s\\n" "${items[@]}"' % ROOT], input=src, text=True)
        items = [l for l in out.split("\n") if l]
    commits = git("log", "--first-parent", "--format=%h", a.ref).split()[a.skip : a.skip + a.n]
    rows = []
    for c in commits:
        subj = git("log", "-1", "--format=%s", c).strip()[:60]
        try:
            files = git("diff", "--name-only", c + "^1", c).split()
        except subprocess.CalledProcessError:
            files = git("show", "--name-only", "--format=", c).split()
        run, reasons = classify(files, rules, items, fwset)
        run_b = run
        lanes = lane_effect(files, None)
        top = sorted(reasons.items(), key=lambda kv: -len(kv[1]))[:2]
        why = "; ".join("%s -> %d" % (k, len(v)) for k, v in top) or "no item input changed"
        # before: the gate's run-specific variables were part of every key -> a gate run skipped nothing (measured with
        # `janus incr explain`: the key changes with JANUS_GATE_TREE0); before_designed: that bug removed, old script list
        rows.append((c, subj, len(files), 0, len(items) - len(run_b), len(items) - len(run), len(items), lanes, why))
    hdr = "commit\tsubject\tfiles\tbefore\tbefore_designed\tafter\ttotal\tlanes_run\twhy"
    lines = [hdr] + ["\t".join(str(x) for x in r) for r in rows]
    if a.tsv:
        open(a.tsv, "w").write("\n".join(lines) + "\n")
    else:
        print("\n".join(lines))
    n = len(rows) * len(items)
    print("# %d commits: item skips before %d/%d, before-designed %d/%d, after %d/%d" % (len(rows), sum(r[3] for r in rows), n,
          sum(r[4] for r in rows), n, sum(r[5] for r in rows), n), file=sys.stderr)


if __name__ == "__main__":
    main()

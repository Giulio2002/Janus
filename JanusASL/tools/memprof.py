#!/usr/bin/env python3
"""Peak memory of a command and of every process it starts (docs/ASL.md, "Memory").

    memprof.py [--json OUT] [--interval S] [--cap GB] -- CMD ARGS...

Runs CMD and samples /proc every S seconds (default 0.2). For every descendant process it
records the peak resident set (`VmHWM`, which the kernel keeps itself, so a sample only misses
growth in the last interval before the process exits) with its command line, and for the whole
tree the peaks of the summed `VmRSS` and of the summed `RssAnon` (the summed RSS counts the
pages of the mmapped .olean files once per process; the anonymous part is private memory). With `--cap GB` the command runs in a transient systemd
scope with `MemoryMax=GB` and no swap, so a runaway build is killed by the kernel instead of
taking the host down; the scope's `memory.peak` (which also counts page cache) is reported too.

Output: one line per process with peak >= 256 MiB (`peak_MiB  wall_s  argv`), then the tree
total; with --json, all of it as JSON. Exit status is CMD's.
"""
import json
import os
import subprocess
import sys
import time


def parse():
    a = sys.argv[1:]
    opts = {"json": None, "interval": 0.2, "cap": None}
    while a and a[0] != "--":
        k = a.pop(0)
        if k == "--json":
            opts["json"] = a.pop(0)
        elif k == "--interval":
            opts["interval"] = float(a.pop(0))
        elif k == "--cap":
            opts["cap"] = a.pop(0)
        else:
            sys.exit("memprof: unknown option %s" % k)
    if not a:
        sys.exit(__doc__)
    return opts, a[1:]


def status(pid):
    try:
        with open("/proc/%d/status" % pid) as f:
            s = f.read()
    except OSError:
        return None
    d = {}
    for line in s.split("\n"):
        if line.startswith(("PPid:", "VmHWM:", "VmRSS:", "RssAnon:")):
            k, v = line.split(":", 1)
            d[k] = int(v.split()[0])
    return d


def cmdline(pid):
    try:
        with open("/proc/%d/cmdline" % pid, "rb") as f:
            return f.read().replace(b"\0", b" ").decode(errors="replace").strip()
    except OSError:
        return ""


def main():
    opts, cmd = parse()
    unit = None
    if opts["cap"]:
        unit = "memprof-%d-%d" % (os.getpid(), int(time.time()))
        cmd = ["systemd-run", "--scope", "-q", "--unit", unit, "-p", "MemoryMax=%sG" % opts["cap"],
               "-p", "MemorySwapMax=0", "--"] + cmd
    t0 = time.time()
    p = subprocess.Popen(cmd)
    procs = {}  # pid -> {argv, hwm, first, last}
    tree_peak = 0
    anon_peak = 0
    cg_peak = None
    while True:
        ppid = {}
        st = {}
        for e in os.listdir("/proc"):
            if e.isdigit():
                s = status(int(e))
                if s and "PPid" in s:
                    ppid[int(e)] = s["PPid"]
                    st[int(e)] = s
        kids = {}
        for c, par in ppid.items():
            kids.setdefault(par, []).append(c)
        todo, tree = [p.pid], []
        while todo:
            x = todo.pop()
            tree.append(x)
            todo.extend(kids.get(x, []))
        now = time.time() - t0
        total = 0
        anon = 0
        for x in tree:
            s = st.get(x)
            if not s or "VmHWM" not in s:
                continue
            total += s.get("VmRSS", 0)
            anon += s.get("RssAnon", 0)
            r = procs.get(x)
            if r is None:
                r = procs[x] = {"argv": cmdline(x), "hwm": 0, "anon": 0, "first": now, "last": now}
            r["hwm"] = max(r["hwm"], s["VmHWM"])
            r["anon"] = max(r["anon"], s.get("RssAnon", 0))
            r["last"] = now
            if not r["argv"] or r["argv"].startswith("systemd-run "):
                r["argv"] = cmdline(x) or r["argv"]
        tree_peak = max(tree_peak, total)
        anon_peak = max(anon_peak, anon)
        if unit:
            try:
                cg = open("/proc/%d/cgroup" % p.pid).read().strip().split("::", 1)[1]
                with open("/sys/fs/cgroup%s/memory.peak" % cg) as f:
                    cg_peak = int(f.read()) // 1024
            except (OSError, IndexError, ValueError):
                pass
        if p.poll() is not None:
            break
        time.sleep(opts["interval"])
    rc = p.returncode
    wall = time.time() - t0
    rows = sorted(({"pid": k, **v} for k, v in procs.items()), key=lambda r: -r["hwm"])
    out = sys.stderr
    print("memprof: rc=%d wall=%.0fs tree-peak-RSS=%.0f MiB tree-peak-anon=%.0f MiB%s" % (
        rc, wall, tree_peak / 1024, anon_peak / 1024,
        "" if cg_peak is None else " scope-memory.peak=%.0f MiB" % (cg_peak / 1024)), file=out)
    for r in rows:
        if r["hwm"] >= 256 * 1024:
            print("  %8.0f MiB (anon %6.0f) %7.0fs  %s" % (r["hwm"] / 1024, r["anon"] / 1024, r["last"] - r["first"],
                                                       r["argv"][:300]), file=out)
    if opts["json"]:
        with open(opts["json"], "w") as f:
            json.dump({"cmd": cmd, "rc": rc, "wall_s": wall, "tree_peak_kib": tree_peak, "tree_anon_peak_kib": anon_peak,
                       "scope_peak_kib": cg_peak, "procs": rows}, f, indent=1)
    sys.exit(rc)


main()

#!/usr/bin/env python3
"""Third oracle: run Janus amd64 oracle cases on the Sail x86 model (translated from ACL2
X86isa) and compare with the Lean model (model.jsonl) and hardware (hw.jsonl).

Each case runs twice, with the model's undefined-value source (`undef_read`) returning 0 and
then 1; a status flag that differs between the two runs is one the formal model treats as
undefined. See README.md.

usage: compare.py EMULATOR ORACLE_DIR OUT_JSON [--sample N] [--jobs J] [--seed S]
"""
import json, os, random, subprocess, sys, tempfile, collections
from multiprocessing import Pool

CODE_PAGE = 0x10_0000_0000
TEST_PC = CODE_PAGE + 0x800
DATA_BASE = CODE_PAGE + 0x4_0000
DATA_SIZE = 4096
STATUS = 0x8D5  # CF PF AF ZF SF OF
REGN = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
FLAGN = {0x1: "CF", 0x4: "PF", 0x10: "AF", 0x40: "ZF", 0x80: "SF", 0x800: "OF"}

def pattern(seed, i):
    return (i * 157 + seed * 89 + (i // 256) * 41 + 7) % 256

EMU = None
TMP = None

def init(emu):
    global EMU, TMP
    EMU = emu
    TMP = tempfile.mkdtemp(prefix="sailx86-")

def run_once(case, undef, code_path, data_path):
    args = [EMU, "-b", f"{TEST_PC:#x},{code_path}", "-b", f"{DATA_BASE:#x},{data_path}",
            "-C", f"rip={TEST_PC:#x}", "-C", f"rflags={(case['rflags'] & STATUS) | 2}",
            "-C", "cr4=512", "-C", "set64bit=1", "-C", "app_view=1",
            "-C", "log_register_writes=0", "-C", f"undef={undef}"]
    for i, n in enumerate(REGN):
        v = int(case['regs'][i], 16)
        if v >= 1 << 63:
            v -= 1 << 64  # the Sail C runtime parses config values with strtoll
        args += ["-C", f"{n}={v}"]
    try:
        out = subprocess.run(args, capture_output=True, text=True, timeout=10).stdout
    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    r = {"status": "?", "regs": {}, "writes": []}
    for line in out.splitlines():
        if line.startswith("STATUS"):
            r["status"] = "ok" if line == "STATUS ok" else "error"
            r["msg"] = line[7:]
        elif " = 0x" in line and not line.startswith("0x"):
            k, v = line.split(" = ")
            r["regs"][k.strip()] = int(v, 16)
        elif ": W 0x" in line:
            p = line.split()
            r["writes"].append((int(p[2], 16), int(p[3]), int(p[4], 16)))
    return r

def work(item):
    case, model, hw = item
    code = bytes.fromhex(case["bytes"])
    code = code + b"\xcc" * (0x800 - len(code))
    buf = bytearray(pattern(case["seed"], i) for i in range(DATA_SIZE))
    for off, b in case.get("init") or []:
        buf[off] = b
    cp = os.path.join(TMP, f"c{os.getpid()}.bin"); dp = os.path.join(TMP, f"d{os.getpid()}.bin")
    open(cp, "wb").write(code); open(dp, "wb").write(bytes(buf))
    r0 = run_once(case, 0, cp, dp)
    r1 = run_once(case, 1, cp, dp)
    res = {"id": case["id"], "class": case["class"], "bytes": case["bytes"]}
    if r0["status"] != "ok" or r1["status"] != "ok":
        res["sail"] = "fault"
        res["msg"] = r0.get("msg", r0["status"])
        return res
    res["sail"] = "ok"
    f0, f1 = r0["regs"]["rflags"] & STATUS, r1["regs"]["rflags"] & STATUS
    res["sail_defined"] = STATUS & ~(f0 ^ f1)
    res["sail_flags"] = f0
    res["undef_regs"] = [n for n in REGN if r0["regs"].get(n) != r1["regs"].get(n)]
    res["regs"] = [r0["regs"].get(n, 0) for n in REGN]
    res["rip"] = r0["regs"]["rip"]
    mem = bytearray(buf)
    for addr, size, val in r0["writes"]:
        for k in range(size):
            a = addr + k
            if DATA_BASE <= a < DATA_BASE + DATA_SIZE:
                mem[a - DATA_BASE] = (val >> (8 * k)) & 0xFF
    res["mem"] = sorted((i, mem[i]) for i in range(DATA_SIZE) if mem[i] != buf[i])
    res["outside_writes"] = any(not (DATA_BASE <= a < DATA_BASE + DATA_SIZE) for a, _, _ in r0["writes"])
    return res

def main():
    emu, odir, out = sys.argv[1], sys.argv[2], sys.argv[3]
    opts = dict(zip(sys.argv[4::2], sys.argv[5::2]))
    n = int(opts.get("--sample", 20000)); jobs = int(opts.get("--jobs", 16))
    random.seed(int(opts.get("--seed", 1)))
    model = {}
    for line in open(os.path.join(odir, "model.jsonl")):
        m = json.loads(line); model[m.get("id")] = m
    hw = {}
    for line in open(os.path.join(odir, "hw.jsonl")):
        h = json.loads(line); hw[h["id"]] = h
    cases = []
    sse = ("mov", "xorp", "pxor", "movd", "movq")
    for line in open(os.path.join(odir, "cases.jsonl")):
        c = json.loads(line)
        cl = c["class"]
        if not (cl.startswith("gen/") or cl.startswith("edge/") or cl.startswith("harvest/")):
            continue
        name = cl.split("/", 1)[1]
        if any(name.startswith(p) for p in ("movups", "movaps", "movupd", "movapd", "movdq", "movq", "movd", "xorp", "pxor", "movss", "movsd")) or name == "sse-align":
            continue  # XMM state cannot be initialised in the Sail driver
        if model.get(c["id"], {}).get("status") != "ok":
            continue  # only cases our model accepts can be unsound
        cases.append(c)
    random.shuffle(cases)
    # stratify: at most n / #classes per class first, then fill
    by = collections.defaultdict(list)
    for c in cases:
        by[c["class"]].append(c)
    per = max(1, n // max(1, len(by)))
    sample = []
    for cl, cs in by.items():
        sample += cs[:per]
    rest = [c for cl, cs in by.items() for c in cs[per:]]
    sample += rest[: max(0, n - len(sample))]
    items = [(c, model.get(c["id"]), hw.get(c["id"])) for c in sample]
    with Pool(jobs, initializer=init, initargs=(emu,)) as p:
        results = p.map(work, items, chunksize=32)
    stats = collections.Counter()
    flag_more_undef = collections.Counter()  # sail undefined, ours defined
    flag_less_undef = collections.Counter()  # ours undefined, sail defined
    undef_result = collections.Counter()
    diffs = collections.Counter()
    examples = collections.defaultdict(list)
    for (c, m, h), r in zip(items, results):
        cl = c["class"]
        stats["cases"] += 1
        if r["sail"] != "ok":
            stats["sail-fault"] += 1
            stats["sail-fault/" + cl] += 1
            continue
        stats["both-ok"] += 1
        ours = m["defined"]
        sd = r["sail_defined"]
        for bit, nm in FLAGN.items():
            if (sd & bit) == 0 and (ours & bit):
                flag_more_undef[f"{cl} {nm}"] += 1
                if len(examples[f"undef {cl} {nm}"]) < 3:
                    examples[f"undef {cl} {nm}"].append((c["id"], c["bytes"]))
            if (ours & bit) == 0 and (sd & bit):
                flag_less_undef[f"{cl} {nm}"] += 1
        if r["undef_regs"]:
            undef_result[cl] += 1
            if len(examples[f"undefres {cl}"]) < 3:
                examples[f"undefres {cl}"].append((c["bytes"], r["undef_regs"]))
        d = []
        mregs = [int(x, 16) for x in m["regs"]]
        for i, nm in enumerate(REGN):
            if nm not in r["undef_regs"] and r["regs"][i] != mregs[i]:
                d.append("reg")
        if r["rip"] != int(m["pc"], 16) % (1 << 48):
            d.append("pc")
        mask = ours & sd
        if (r["sail_flags"] & mask) != (m["rflags"] & mask):
            d.append("flags")
        mm = sorted(tuple(x) for x in (m.get("mem") or []))
        if [tuple(x) for x in r["mem"]] != mm:
            d.append("mem")
        if d:
            k = cl + " " + "+".join(sorted(set(d)))
            diffs[k] += 1
            if len(examples["diff " + k]) < 3:
                examples["diff " + k].append(c["id"])
        else:
            stats["agree"] += 1
    json.dump({"stats": stats, "sail_undef_ours_defined": flag_more_undef,
               "ours_undef_sail_defined": flag_less_undef, "sail_undefined_result": undef_result,
               "result_diffs": diffs, "examples": examples}, open(out, "w"), indent=1, sort_keys=True)
    print(json.dumps({"stats": {k: v for k, v in stats.items() if "/" not in k},
                      "sail_undef_ours_defined": sum(flag_more_undef.values()),
                      "result_diffs": sum(diffs.values())}))

if __name__ == "__main__":
    main()

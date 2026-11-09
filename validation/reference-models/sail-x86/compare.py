#!/usr/bin/env python3
"""Third oracle: run Janus amd64 oracle cases on the Sail x86 model (translated from ACL2
X86isa) and compare with the Lean model (model.jsonl) and hardware (hw.jsonl).

Each case runs twice, with the model's undefined-value source (`undef_read`) returning 0 and
then 1; a status flag that differs between the two runs is one the formal model treats as
undefined. See README.md.

usage: compare.py EMULATOR ORACLE_DIR OUT_JSON [--sample N] [--jobs J] [--seed S] [--classes REGEX] [--fs 1]

--classes keeps only the case classes matching REGEX (e.g. the atomics and string classes).
--fs 1 keeps only cases with a 64 (FS segment) prefix.

The driver sets the 16 GPRs, RFLAGS, RIP, the FS base and bits 255:0 of YMM0-15 (case xmm =
bits 127:0, ymmh = bits 255:128) and compares GPRs, RIP, defined flags, DF (must stay clear),
the data buffer and YMM0-15 (model.jsonl xmm/ymmh) with our model.
"""
import json, os, random, subprocess, sys, tempfile, collections
from multiprocessing import Pool

CODE_PAGE = 0x10_0000_0000
TEST_PC = CODE_PAGE + 0x800
DATA_BASE = CODE_PAGE + 0x4_0000
DATA_SIZE = 4096
STATUS = 0x8D5  # CF PF AF ZF SF OF
REGN = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"] + [f"r{i}" for i in range(8, 16)]
DF = 0x400
def s64(v):
    return v - (1 << 64) if v >= 1 << 63 else v  # the Sail C runtime parses config values with strtoll

def legacy_prefixes(code):
    i = 0
    while i < len(code) and (code[i] in (0x66, 0x67, 0xF2, 0xF3, 0xF0, 0x2E, 0x3E, 0x26, 0x36, 0x64, 0x65) or 0x40 <= code[i] <= 0x4F):
        i += 1
    return code[:i]

def ymm_of(xmm, ymmh, i):
    """Bits 255:0 of YMMi from an oracle record (xmm = low 128 bits, ymmh = high 128, absent = 0)."""
    lo = int(xmm[i], 16) if xmm else 0
    hi = int(ymmh[i], 16) if ymmh else 0
    return lo | (hi << 128)

YMMN = [f"ymm{i}" for i in range(16)]
FLAGN = {0x1: "CF", 0x4: "PF", 0x10: "AF", 0x40: "ZF", 0x80: "SF", 0x800: "OF"}

def pattern(seed, i):
    return (i * 157 + seed * 89 + (i // 256) * 41 + 7) % 256

EMU = None
TMP = None

def init(emu):
    global EMU, TMP
    EMU = emu
    TMP = tempfile.mkdtemp(prefix="sailx86-")

def is_rep_string(code):
    """A string instruction with an F2/F3 prefix (layout.IsRepString)."""
    i = 0
    while i < len(code) and (code[i] in (0x66, 0x67, 0xF2, 0xF3, 0xF0, 0x2E, 0x3E, 0x26, 0x36, 0x64, 0x65) or 0x40 <= code[i] <= 0x4F):
        i += 1
    return i < len(code) and any(b in (0xF2, 0xF3) for b in code[:i]) and code[i] in (
        0xA4, 0xA5, 0xA6, 0xA7, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF)

def run_rep(case, undef, code_path, data_path, buf):
    """Run a REP string instruction to completion: the formal model executes one iteration
    per step and leaves RIP at the instruction until the count is exhausted, so the state
    (registers, flags, buffer) is fed back until RIP moves (at most RCX + 2 steps)."""
    c = dict(case)
    mem = bytearray(buf)
    writes = []
    dp = data_path + ".rep"
    r = None
    for _ in range(min(int(case["regs"][1], 16) + 2, 5000)):
        open(dp, "wb").write(bytes(mem))
        r = run_once(c, undef, code_path, dp)
        if r["status"] != "ok":
            return r
        for addr, size, val in r["writes"]:
            writes.append((addr, size, val))
            for k in range(size):
                a = addr + k
                if DATA_BASE <= a < DATA_BASE + DATA_SIZE:
                    mem[a - DATA_BASE] = (val >> (8 * k)) & 0xFF
        if r["regs"]["rip"] != TEST_PC:
            break
        c["regs"] = [hex(r["regs"][n]) for n in REGN]
        c["rflags"] = r["regs"]["rflags"]
    r["writes"] = writes
    return r

def run_once(case, undef, code_path, data_path):
    args = [EMU, "-b", f"{TEST_PC:#x},{code_path}", "-b", f"{DATA_BASE:#x},{data_path}",
            "-C", f"rip={TEST_PC:#x}", "-C", f"rflags={(case['rflags'] & STATUS) | 2}",
            "-C", "cr4=512", "-C", "set64bit=1", "-C", "app_view=1",
            "-C", "log_register_writes=0", "-C", f"undef={undef}"]
    for i, n in enumerate(REGN):
        args += ["-C", f"{n}={s64(int(case['regs'][i], 16))}"]
    args += ["-C", f"fsbase={s64(int(case.get('fsbase') or '0', 16))}"]
    for i in range(16):
        y = ymm_of(case.get("xmm"), case.get("ymmh"), i)
        for j in range(4):
            args += ["-C", f"ymm{i}q{j}={s64((y >> (64 * j)) & ((1 << 64) - 1))}"]
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
    if is_rep_string(bytes.fromhex(case["bytes"])):
        r0 = run_rep(case, 0, cp, dp, buf)
        r1 = run_rep(case, 1, cp, dp, buf)
    else:
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
    res["undef_regs"] = [n for n in REGN + YMMN if r0["regs"].get(n) != r1["regs"].get(n)]
    res["regs"] = [r0["regs"].get(n, 0) for n in REGN]
    res["ymm"] = [r0["regs"].get(n, 0) for n in YMMN]
    res["df"] = bool(r0["regs"]["rflags"] & DF)
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

def open_jsonl(path):
    """The JSON-lines file at path, or its zstd-compressed copy path.zst (the oracle drivers keep
    their dumps compressed unless KEEP=1, scripts/lib/artifacts.sh)."""
    if os.path.exists(path) or not os.path.exists(path + ".zst"):
        return open(path)
    p = subprocess.Popen(["zstd", "-q", "-dc", path + ".zst"], stdout=subprocess.PIPE, text=True)
    return p.stdout

def main():
    emu, odir, out = sys.argv[1], sys.argv[2], sys.argv[3]
    opts = dict(zip(sys.argv[4::2], sys.argv[5::2]))
    n = int(opts.get("--sample", 20000)); jobs = int(opts.get("--jobs", 16))
    import re
    only = re.compile(opts["--classes"]) if "--classes" in opts else None
    random.seed(int(opts.get("--seed", 1)))
    fs_only = opts.get("--fs", "0") not in ("0", "")
    cases = []
    for line in open_jsonl(os.path.join(odir, "cases.jsonl")):
        c = json.loads(line)
        cl = c["class"]
        if not (cl.startswith("gen/") or cl.startswith("edge/") or cl.startswith("harvest/")):
            continue
        if only is not None and not only.search(cl):
            continue
        if fs_only and 0x64 not in legacy_prefixes(bytes.fromhex(c["bytes"])):
            continue
        cases.append(c)
    ids = {c["id"] for c in cases}  # load only the records of the selected cases
    model = {}
    for line in open_jsonl(os.path.join(odir, "model.jsonl")):
        if int(line[6:line.index(",")]) in ids:
            m = json.loads(line); model[m.get("id")] = m
    hw = {}
    for line in open_jsonl(os.path.join(odir, "hw.jsonl")):
        if int(line[6:line.index(",")]) in ids:
            h = json.loads(line); hw[h["id"]] = h
    # only cases our model accepts can be unsound
    cases = [c for c in cases if model.get(c["id"], {}).get("status") == "ok"]
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
    diffs_hw_ours = collections.Counter()  # result diffs where hardware equals ours on every differing field
    faults = collections.defaultdict(collections.Counter)  # class -> formal-model fault message -> count
    examples = collections.defaultdict(list)
    per_class = collections.defaultdict(collections.Counter)
    for (c, m, h), r in zip(items, results):
        cl = c["class"]
        pc = per_class[cl]
        stats["cases"] += 1; pc["cases"] += 1
        if r["sail"] != "ok":
            stats["sail-fault"] += 1; pc["sail-fault"] += 1
            stats["sail-fault/" + cl] += 1
            faults[cl][r.get("msg", "?")[:100]] += 1
            continue
        stats["both-ok"] += 1; pc["both-ok"] += 1
        ours = m["defined"]
        sd = r["sail_defined"]
        for bit, nm in FLAGN.items():
            if (sd & bit) == 0 and (ours & bit):
                flag_more_undef[f"{cl} {nm}"] += 1; pc["sail-undef-ours-defined"] += 1
                if len(examples[f"undef {cl} {nm}"]) < 3:
                    examples[f"undef {cl} {nm}"].append((c["id"], c["bytes"]))
            if (ours & bit) == 0 and (sd & bit):
                flag_less_undef[f"{cl} {nm}"] += 1; pc["ours-undef-sail-defined"] += 1
                if len(examples[f"oursundef {cl} {nm}"]) < 3:
                    examples[f"oursundef {cl} {nm}"].append((c["id"], c["bytes"]))
        if r["undef_regs"]:
            undef_result[cl] += 1; pc["sail-undef-result"] += 1
            if len(examples[f"undefres {cl}"]) < 3:
                examples[f"undefres {cl}"].append((c["bytes"], r["undef_regs"]))
        hok = h is not None and h.get("status") == "ok"
        d = []  # (kind, field, sail value, our value, hw value or None)
        mregs = [int(x, 16) for x in m["regs"]]
        hregs = [int(x, 16) for x in h["regs"]] if hok and h.get("regs") else None
        for i, nm in enumerate(REGN):
            if nm not in r["undef_regs"] and r["regs"][i] != mregs[i]:
                d.append(("reg", nm, hex(r["regs"][i]), hex(mregs[i]), hex(hregs[i]) if hregs else None))
        mpc = int(m["pc"], 16) % (1 << 48)
        if r["rip"] != mpc:
            d.append(("pc", "rip", hex(r["rip"]), hex(mpc), hex(int(h["pc"], 16) % (1 << 48)) if hok and h.get("pc") else None))
        mask = ours & sd
        if (r["sail_flags"] & mask) != (m["rflags"] & mask):
            d.append(("flags", f"mask {mask:#x}", hex(r["sail_flags"] & mask), hex(m["rflags"] & mask),
                      hex(h["rflags"] & mask) if hok else None))
        if r["df"]:
            d.append(("df", "DF", True, False, h.get("df", False) if hok else None))
        mm = sorted(tuple(x) for x in (m.get("mem") or []))
        if [tuple(x) for x in r["mem"]] != mm:
            hm = sorted(tuple(x) for x in (h.get("mem") or [])) if hok else None
            d.append(("mem", "buffer", r["mem"][:16], mm[:16], hm[:16] if hm is not None else None))
        for i, nm in enumerate(YMMN):
            if nm in r["undef_regs"]:
                continue
            my = ymm_of(m.get("xmm"), m.get("ymmh"), i)
            if r["ymm"][i] != my:
                hy = ymm_of(h.get("xmm"), h.get("ymmh"), i) if hok and h.get("xmm") else None
                d.append(("ymm", nm, f"{r['ymm'][i]:#066x}", f"{my:#066x}", f"{hy:#066x}" if hy is not None else None))
        if d:
            k = cl + " " + "+".join(sorted(set(x[0] for x in d)))
            diffs[k] += 1; pc["result-diff"] += 1
            hw_ours = hok and all(x[4] is not None and x[4] == x[3] for x in d)
            if hw_ours:
                diffs_hw_ours[k] += 1; pc["result-diff-hw-agrees-ours"] += 1
            if len(examples["diff " + k]) < 3:
                examples["diff " + k].append({"id": c["id"], "bytes": c["bytes"], "hw_agrees_ours": hw_ours,
                                              "fields": [dict(zip(("kind", "field", "sail", "ours", "hw"), x)) for x in d]})
        else:
            stats["agree"] += 1; pc["agree"] += 1
    json.dump({"stats": stats, "per_class": per_class, "sail_faults": faults, "sail_undef_ours_defined": flag_more_undef,
               "ours_undef_sail_defined": flag_less_undef, "sail_undefined_result": undef_result,
               "result_diffs": diffs, "result_diffs_hw_agrees_ours": diffs_hw_ours, "examples": examples},
              open(out, "w"), indent=1, sort_keys=True)
    print(json.dumps({"stats": {k: v for k, v in stats.items() if "/" not in k},
                      "sail_undef_ours_defined": sum(flag_more_undef.values()),
                      "ours_undef_sail_defined": sum(flag_less_undef.values()),
                      "result_diffs": sum(diffs.values()),
                      "result_diffs_hw_agrees_ours": sum(diffs_hw_ours.values())}))

if __name__ == "__main__":
    main()

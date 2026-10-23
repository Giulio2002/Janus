#!/usr/bin/env python3
"""Hand-written sanity cases for janus-oracle-sail, with the expected Sail outcome.

usage: smoke.py                  print the cases (layout.Case JSON lines)
       smoke.py --check OUT      check janus-oracle-sail's output for them
Each expectation follows from the Arm ARM / Linux, independent of qemu and of Janus.
"""
import json
import sys

BASE = 0x10_0000_0000 + 0x4_0000  # layout.DataBase
PC = 0x10_0000_0800  # layout.TestPC


def pattern(seed, i):
    return (i * 157 + seed * 89 + (i // 256) * 41 + 7) % 256


def le(seed, off, n):
    return sum(pattern(seed, off + k) << (8 * k) for k in range(n))


SEED = 3
CASES = [
    # (id, word, regs, sp, nzcv, expectation)
    (1, 0x8B020020, {1: 3, 2: 4}, None, 0, ("ok", {"x0": 7, "pc": PC + 4})),  # add x0, x1, x2
    (2, 0xF9400020, {1: BASE + 3}, None, 0, ("ok", {"x0": le(SEED, 3, 8)})),  # ldr unaligned: Normal mem, SCTLR.A=0
    (3, 0xF9400020, {1: 0x2000}, None, 0, ("fault", {"sig": 11, "code": 1, "addr": 0x2000})),  # unmapped
    (4, 0xF94003E0, {}, BASE + 0x804, 0, ("fault", {"sig": 7})),  # ldr x0,[sp], SP%16 != 0, SA0=1
    (5, 0xD61F0020, {1: 0x8000_0000_0000_0000}, None, 0, ("ok", {"pc": 0})),  # br: TBI0 => PC[63:56] = PC[55]
    (6, 0x00000000, {}, None, 0, ("fault", {"sig": 4})),  # udf #0
    (7, 0xD4200000, {}, None, 0, ("fault", {"sig": 5})),  # brk #0
    (8, 0xF9000020, {0: 0xDEADBEEF, 1: BASE + 8}, None, 0, ("ok", {"mem": [[8, 0xEF], [9, 0xBE], [10, 0xAD], [11, 0xDE], [12, 0], [13, 0], [14, 0], [15, 0]]})),  # str x0,[x1]
    (9, 0x14000000, {}, None, 0, ("selfloop", {})),  # b .
    (10, 0xF9400020, {1: 0xFF00_0010_0004_0010}, None, 0, ("ok", {"x0": le(SEED, 16, 8)})),  # tagged pointer load (TBI0)
    (11, 0xC85F7C20, {1: BASE + 12}, None, 0, ("fault", {"sig": 7})),  # ldxr crossing 16 bytes: alignment fault
    (12, 0xF8200020, {1: BASE + 12}, None, 0, ("fault", {"sig": 7})),  # ldadd x0,x0,[x1] crossing 16 bytes
    (13, 0xD503207F, {}, None, 0, ("ok", {"pc": PC + 4})),  # wfi: trapped, skipped by Linux
    (14, 0xD69F03E0, {}, None, 0, ("fault", {"sig": 4})),  # eret at EL0: UNDEFINED
    (15, 0xF9000020, {1: PC}, None, 0, ("ok", {})),  # store into the (RWX) code page
    (16, 0xF9000020, {1: BASE + 4092}, None, 0, ("fault", {"sig": 11, "addr": BASE + 4096})),  # str crossing the buffer end
    (17, 0x9AC10C00, {0: 7, 1: 0}, None, 0, ("ok", {"x0": 0})),  # sdiv by zero = 0
    # ldxr x8,[x1] with Rs = 01000 (an Arm ARM "(1)" should-be-one field): CONSTRAINED
    # UNPREDICTABLE; sail-arm's decode pattern hard-codes the 1s, so it is UNDEFINED there.
    (18, 0xC8487C28, {1: BASE + 32}, None, 0, ("fault", {"sig": 4})),
]


def emit():
    for cid, w, regs, sp, nzcv, _ in CASES:
        x = ["0x0"] * 31
        for k, v in regs.items():
            x[k] = hex(v)
        print(json.dumps({"id": cid, "class": "smoke", "word": hex(w), "pc": hex(PC), "x": x,
                          "sp": hex(sp if sp is not None else BASE + 2048), "nzcv": nzcv, "seed": SEED}))


def check(path):
    got = {}
    for line in open(path):
        v = json.loads(line)
        got[v["id"]] = v
    bad = 0
    for cid, w, regs, sp, nzcv, (status, exp) in CASES:
        r = got.get(cid, {})
        errs = []
        if status == "unpredictable":
            if not r.get("unpredictable"):
                errs.append("expected an UNPREDICTABLE event to be counted")
        elif r.get("status") != status:
            errs.append(f"status {r.get('status')} != {status}")
        for k, v in exp.items():
            if k.startswith("x"):
                g = int(r.get("x", ["0x0"] * 31)[int(k[1:])], 16)
            elif k == "mem":
                g = r.get("mem", [])
            elif k in ("pc", "addr"):
                g = int(r.get(k, "0x0"), 16)
            else:
                g = r.get(k)
            if g != v:
                errs.append(f"{k}: got {g!r} expected {v!r}")
        print(f"{'ok  ' if not errs else 'FAIL'} {cid:2d} {w:#010x} {r.get('note', '')} {'; '.join(errs)}")
        bad += bool(errs)
    print(f"{len(CASES) - bad}/{len(CASES)} Sail smoke cases as expected")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "--check":
        check(sys.argv[2])
    else:
        emit()

#!/usr/bin/env python3
"""FSQRT probe cases for the `sqrt_real` replacement (audit/rt-asl/run.sh, row A5 fsqrt).

    gen_cases.py > cases.jsonl

Deterministic (fixed seed). FSQRT S0, S1 / FSQRT D0, D1 with V1 = the operand (upper bits of V1 and
V0 set to junk, to check the zeroing of the destination), every rounding mode (FPCR.RMode), with
FPCR.FZ and FPCR.DN on and off (AH, FIZ, NEP and the trap enables 0). Operands: random normals,
denormals, exact squares, inexact roots near a rounding midpoint (the square of a midpoint,
rounded to the format, and its neighbours), +-0, +-inf, negative normals and denormals, quiet and
signalling NaNs with payloads.
"""
import json, random, sys
from fractions import Fraction

random.seed(20261025)
FMT = {32: (8, 23), 64: (11, 52)}

def pack(n, s, e, f):
    E, F = FMT[n]
    return (s << (E + F)) | (e << F) | f

def enc_value(n, v):
    """Round the positive Fraction v to format n (round to nearest even); return the encoding."""
    E, F = FMT[n]
    bias = (1 << (E - 1)) - 1
    if v == 0:
        return 0
    e = v.numerator.bit_length() - v.denominator.bit_length()
    while Fraction(2) ** e > v: e -= 1
    while Fraction(2) ** (e + 1) <= v: e += 1
    e = max(e, 1 - bias)
    q = v / Fraction(2) ** (e - F)
    m = q.numerator // q.denominator
    r = q - m
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and m % 2 == 1): m += 1
    if m >= 1 << (F + 1): m //= 2; e += 1
    if e + bias >= (1 << E) - 1: return pack(n, 0, (1 << E) - 1, 0)
    if m < 1 << F: return pack(n, 0, 0, m)
    return pack(n, 0, e + bias, m - (1 << F))

def value(n, x):
    E, F = FMT[n]
    bias = (1 << (E - 1)) - 1
    e = (x >> F) & ((1 << E) - 1); f = x & ((1 << F) - 1)
    if e == 0: return Fraction(f) * Fraction(2) ** (1 - bias - F)
    return Fraction((1 << F) + f) * Fraction(2) ** (e - bias - F)

def operands(n):
    E, F = FMT[n]
    emax = (1 << E) - 1
    ops = []
    for _ in range(60): ops.append(pack(n, 0, random.randrange(1, emax), random.getrandbits(F)))
    for _ in range(25): ops.append(pack(n, 0, 0, random.randrange(1, 1 << F)))           # denormals
    ops += [pack(n, 0, 0, 1), pack(n, 0, 0, (1 << F) - 1), pack(n, 0, 1, 0), pack(n, 0, emax - 1, (1 << F) - 1)]
    for _ in range(25):                                                                   # exact squares
        k = random.randrange(1, 1 << ((F + 1) // 2))
        sh = random.randrange(-((1 << (E - 1)) // 2) + 2, (1 << (E - 1)) // 2 - 2)
        ops.append(enc_value(n, Fraction(k * k) * Fraction(4) ** sh))
    for _ in range(30):                                                                   # near midpoints
        r = value(n, pack(n, 0, random.randrange(2, emax - 2), random.getrandbits(F)))
        ulp = Fraction(2) ** ((r.numerator.bit_length() - r.denominator.bit_length()) - F - 1)
        x = enc_value(n, (r + ulp / 2) ** 2)
        ops += [x - 1, x, x + 1]
    ops += [pack(n, 0, 0, 0), pack(n, 1, 0, 0), pack(n, 0, emax, 0), pack(n, 1, emax, 0)]  # +-0, +-inf
    for _ in range(10): ops.append(pack(n, 1, random.randrange(1, emax), random.getrandbits(F)))  # negative
    for _ in range(4): ops.append(pack(n, 1, 0, random.randrange(1, 1 << F)))
    q = 1 << (F - 1)
    for _ in range(6):                                                                    # NaNs
        ops.append(pack(n, random.getrandbits(1), emax, q | random.getrandbits(F - 1)))
        ops.append(pack(n, random.getrandbits(1), emax, random.randrange(1, q)))
    return [x for x in ops if 0 <= x < 1 << n]

def main():
    # The integer state is irrelevant to FSQRT: zero registers, the oracle corpus' code address,
    # stack and DCZID.
    tmpl = {"pc": "0x1000000800", "x": ["0x0"] * 31, "sp": "0x10000403e0", "nzcv": 0, "seed": 1,
            "dczid": 7, "tpidr": "0x0"}
    cid = 0
    for n, word in ((32, 0x1E21C000 | (1 << 5)), (64, 0x1E61C000 | (1 << 5))):
        ops = operands(n)
        for rmode in range(4):
            for fz in (0, 1):
                for dn in (0, 1):
                    fpcr = (rmode << 22) | (fz << 24) | (dn << 25)
                    for x in ops:
                        cid += 1
                        c = dict(tmpl)
                        c["id"] = cid
                        c["class"] = f"rt-asl/fsqrt{n}"
                        c["word"] = hex(word)
                        v = ["0x0"] * 32
                        junk = random.getrandbits(128)
                        v[0] = hex(random.getrandbits(128))
                        v[1] = hex((junk >> n << n) | x)
                        c["v"] = v
                        c["fpcr"] = hex(fpcr)
                        c["fpsr"] = hex(random.choice([0, 0, 0x10, 0x1F]))
                        print(json.dumps(c))

main()

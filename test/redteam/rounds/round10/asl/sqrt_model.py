#!/usr/bin/env python3
"""Independent model: ASL FPSqrt = FPRound(exact sqrt) vs FPRound(sqrt_real') where sqrt_real' is
the JanusASL/sail/fakereal_sqrt.py replacement (round-to-odd at 2^-1100), transliterated from
the generated Lean (vendor/ArmASL.tar.gz @502cb93, ArmASL/FakeReal.lean, Part06.lean FPRoundBase__1).

(a) oracle: FPRoundBase on r = sqrt(s) with every decision made by exact integer/rational
    comparisons on s (r >= t  <=>  s >= t^2), never materialising r.
(b) subst : FPRoundBase transliterated on Fraction, fed sqrt_real'(s).
Usage: python3 -I sqrt_model.py [nrandom]
"""
import sys, random, math, struct
from fractions import Fraction as Q

K = 1100
def sqrt_real_subst(x):                      # FakeReal.lean sqrt_real, verbatim semantics
    if x <= 0: return Q(0)
    y = (x.numerator * 4**K) // x.denominator
    m = math.isqrt(y)                        # Nat.sqrt (proved floor sqrt in Lean core)
    if m * m * x.denominator == x.numerator * 4**K:
        return Q(m, 2**K)
    return Q(2*m + 1, 2**(K+1))

PREC = {16: (5, 10, -14), 32: (8, 23, -126), 64: (11, 52, -1022)}
HALF = Q(1, 2)

# ---- value interfaces -------------------------------------------------------------------
class Exact:       # r = sqrt(s), s > 0 rational
    def __init__(self, s): self.s = s
    def exponent(self):
        # ASL loops: while m<1: m*=2,e-=1 ; while m>=2: m/=2,e+=1  => 2^e <= r < 2^(e+1)
        s, e = self.s, 0
        while s < 1: s *= 4; e -= 1
        while s >= 4: s /= 4; e += 1
        return e
    def scaled(self, sh):  # r*2^sh -> (floor, errclass) with errclass in {0,'lt','eq','gt'} vs 1/2
        q = self.s * Q(4)**sh
        im = math.isqrt(q.numerator // q.denominator)
        if Q(im*im) == q: return im, 0
        h = Q(2*im + 1, 2)**2
        return im, ('lt' if q < h else 'eq' if q == h else 'gt')

class Rat:         # transliteration on a concrete rational (what the Lean code computes)
    def __init__(self, v): self.v = v
    def exponent(self):
        m, e = self.v, 0
        while m < 1: m *= 2; e -= 1
        while m >= 2: m /= 2; e += 1
        return e
    def scaled(self, sh):
        t = self.v * Q(2)**sh
        im = t.numerator // t.denominator
        err = t - im
        return im, (0 if err == 0 else 'lt' if err < HALF else 'eq' if err == HALF else 'gt')

# ---- FPRoundBase__1 (Part06.lean:402), positive op, fpexc=true, isbfloat16=false -----------
def fpround(val, N, rnd, FZ, FZ16, AH, UFE, have_altfp=True):
    E, F, minexp = PREC[N]
    flags = set()
    sign = 0
    exponent = val.exponent()
    altfp = have_altfp and AH
    fzon = (FZ and N != 16) or (FZ16 and N == 16)
    if (not altfp) and fzon and exponent < minexp:
        flags.add('UFC'); return 0, flags                          # FPZero
    be_u = exponent - minexp + 1
    im_u, err_u = val.scaled(F - exponent)
    be = max(exponent - minexp + 1, 0)
    sh = F - exponent if be != 0 else F - exponent - (minexp - exponent)
    # mantissa/2^(minexp-exponent) * 2^F  ==  val * 2^(F - exponent) / 2^(minexp-exponent)
    if be == 0: sh = F - minexp
    im, err = val.scaled(sh)
    trapped_UF = bool(UFE)
    if (not altfp) and be == 0 and (err != 0 or trapped_UF): flags.add('UFC')
    def ru(e, i):
        if rnd == 'RN': return e == 'gt' or (e == 'eq' and (i & 1))
        if rnd == 'RP': return e != 0 and sign == 0
        if rnd == 'RM': return e != 0 and sign == 1
        return False
    oti = {'RN': True, 'RP': sign == 0, 'RM': sign == 1, 'RZ': False, 'RO': False}[rnd]
    if altfp:
        if ru(err_u, im_u):
            im_u += 1
            if im_u == 2**(F+1): be_u += 1; im_u //= 2
        if be_u < 1 and im_u != 0:
            if fzon:
                flags |= {'UFC', 'IXC'}; return 0, frozenset(flags)
            elif err != 0 or trapped_UF: flags.add('UFC')
    if ru(err, im):
        im += 1
        if im == 2**F: be = 1
        if im == 2**(F+1): be += 1; im //= 2
    if err != 0 and rnd == 'RO': im |= 1
    if be >= 2**E - 1:
        res = ('INF' if oti else 'MAX'); flags.add('OFC'); flags.add('IXC')
        return res, frozenset(flags)
    res = (be << F) | (im & (2**F - 1))
    if err != 0: flags.add('IXC')
    return res, frozenset(flags)

def decode(bits, N):
    E, F, minexp = PREC[N]
    e = (bits >> F) & (2**E - 1); f = bits & (2**F - 1)
    if bits >> (N-1) or e == 2**E - 1 or (e == 0 and f == 0): return None
    if e == 0: return Q(f, 2**F) * Q(2)**minexp, True
    return (1 + Q(f, 2**F)) * Q(2)**(e - 2**(E-1) + 1), False

MODES = ['RN', 'RP', 'RM', 'RZ', 'RO']
CFGS = [(FZ, FZ16, AH, UFE) for FZ in (0, 1) for FZ16 in (0, 1) for AH in (0, 1) for UFE in (0, 1)]
stats = {}; bad = []
def check(bits, N, cfgs=CFGS, modes=MODES):
    d = decode(bits, N)
    if d is None: return
    x, sub = d
    ex, ap = Exact(x), Rat(sqrt_real_subst(x))
    exact_root = (ap.v * ap.v == x)
    for (FZ, FZ16, AH, UFE) in cfgs:
        fz_in = (FZ16 if N == 16 else FZ) and not AH   # non-AH input flush: sqrt never reached
        for rnd in modes:
            a = fpround(ex, N, rnd, FZ, FZ16, AH, UFE)
            b = fpround(ap, N, rnd, FZ, FZ16, AH, UFE)
            k = (N, 'sub' if sub else 'norm', 'exact' if exact_root else 'inexact')
            stats[k] = stats.get(k, 0) + 1
            if a != b:
                bad.append((N, hex(bits), (FZ, FZ16, AH, UFE), rnd, a, b))

def f2b64(f): return struct.unpack('<Q', struct.pack('<d', f))[0]
def b2f64(b): return struct.unpack('<d', struct.pack('<Q', b))[0]
def f2b32(f): return struct.unpack('<I', struct.pack('<f', f))[0]

def main():
    nrand = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(10)
    # half: exhaustive
    for b in range(1 << 16): check(b, 16)
    print('half exhaustive done', flush=True)
    # oracle sanity: double RN vs hardware math.sqrt, single RN vs float32 rounding of exact double sqrt
    hw = 0
    for _ in range(20000):
        b = rng.getrandbits(63)
        d = decode(b, 64)
        if d is None: continue
        r, fl = fpround(Exact(d[0]), 64, 'RN', 0, 0, 0, 0)
        assert r == f2b64(math.sqrt(b2f64(b))) & ((1 << 63) - 1), hex(b)
        hw += 1
    print('oracle vs hw sqrt (double RN):', hw, 'ok', flush=True)
    for N in (32, 64):
        E, F, minexp = PREC[N]
        samples = set()
        for _ in range(nrand): samples.add(rng.getrandbits(N - 1))
        for e in range(2**E - 1):                     # every exponent incl. subnormal, edge mantissas
            for f in (0, 1, 2, 3, 2**F - 1, 2**F - 2, 2**(F-1), 2**(F-1) + 1, rng.getrandbits(F)):
                samples.add((e << F) | f)
        for f in range(1, 4096): samples.add(f)       # tiny subnormals
        for _ in range(nrand // 4):                   # exact squares: (odd j)^2 at random exponent
            j = rng.getrandbits(F // 2) | 1
            v = Q(j * j) * Q(2)**(2 * rng.randint(-(2**(E-2)) // 2 + 2, (2**(E-2)) // 2 - 2) - F)
            d = v
            # encode v if representable
            e = 0; m = v
            while m < 1: m *= 2; e -= 1
            while m >= 2: m /= 2; e += 1
            be = e - minexp + 1
            if 1 <= be < 2**E - 1 and (m * 2**F).denominator == 1:
                samples.add((be << F) | (int(m * 2**F) - 2**F))
        for _ in range(nrand // 4):                   # near-ties: x ~= (midpoint)^2 +- few ulp
            mid = Q((2 * (2**F + rng.getrandbits(F)) + 1), 2**(F+1)) * Q(2)**rng.randint(-60, 60)
            sq = mid * mid
            e = 0; m = sq
            while m < 1: m *= 2; e -= 1
            while m >= 2: m /= 2; e += 1
            be = e - minexp + 1
            if 1 <= be < 2**E - 1:
                c = int(m * 2**F) - 2**F
                for dlt in range(-3, 4):
                    if 0 <= c + dlt < 2**F: samples.add((be << F) | (c + dlt))
        n0 = sum(stats.values())
        for b in samples: check(b, N)
        print(N, 'samples', len(samples), 'comparisons', sum(stats.values()) - n0, flush=True)
    for k in sorted(stats): print('  ', k, stats[k])
    print('TOTAL comparisons', sum(stats.values()), 'MISMATCHES', len(bad))
    for r in bad[:20]: print('  MISMATCH', r)

if __name__ == '__main__': main()

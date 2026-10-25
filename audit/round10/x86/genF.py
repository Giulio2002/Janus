# FMA scalar cases whose exact result sits at the underflow boundary (tiny before rounding but
# not after, and vice versa), at overflow boundary, and exact-cancellation zeros; all RC/FTZ/DAZ/mask combos
import sys, random, json
from fractions import Fraction as F
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from common import *
r = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); out = open(sys.argv[3],'w')
def val(bits, w):
    eb, mb = (8,23) if w==32 else (11,52)
    s = bits >> (w-1); e = (bits >> mb) & ((1<<eb)-1); m = bits & ((1<<mb)-1)
    bias = (1<<(eb-1))-1
    if e == (1<<eb)-1: return None
    v = F(m, 1<<mb) * F(2)**(1-bias) if e == 0 else F((1<<mb)+m, 1<<mb) * F(2)**(e-bias)
    return -v if s else v
def mk(w, s, e, m):
    eb, mb = (8,23) if w==32 else (11,52)
    return (s<<(w-1)) | (e<<mb) | m
def near(w, mb, frac_bias):
    # mantissa near all-ones or near zero
    k = r.choice([0,1,2,3])
    if r.random()<0.5: return (1<<mb)-1-r.randrange(1<<k)
    return r.randrange(1<<k)
ops = [(0x99,132),(0xA9,213),(0xB9,231),(0x9B,132),(0xAB,213),(0xBB,231),(0x9D,132),(0xAD,213),(0xBD,231),(0x9F,132),(0xAF,213),(0xBF,231)]
cnt = 0; i = 0
while cnt < N:
    i += 1
    w = r.choice([32,64]); eb, mb = (8,23) if w==32 else (11,52); bias=(1<<(eb-1))-1
    mode = r.choice(['uf','uf','of','cancel'])
    if mode == 'uf':
        # a in [1,2), b near 2^-bias+1 so product ~ min normal; c tiny
        a = mk(w, r.randrange(2), bias + r.choice([0,0,-1]), near(w,mb,0))
        b = mk(w, r.randrange(2), r.choice([1,1,2,0]), near(w,mb,0))
        c = mk(w, r.randrange(2), r.choice([0,0,1]), r.randrange(1<<mb) if r.random()<0.5 else r.randrange(8))
    elif mode == 'of':
        a = mk(w, r.randrange(2), (1<<eb)-2 - r.choice([0,1]), near(w,mb,0))
        b = mk(w, 0, bias + r.choice([0,1,0]), near(w,mb,0))
        c = mk(w, r.randrange(2), (1<<eb)-2 - r.choice([0,1,2,30]), near(w,mb,0))
    else:
        a = r.getrandbits(w) & ~(((1<<eb)-1)<<mb) | ((bias + r.randrange(-3,3))<<mb)
        b = r.getrandbits(w) & ~(((1<<eb)-1)<<mb) | ((bias + r.randrange(-3,3))<<mb)
        p = val(a,w)*val(b,w)
        # c = -round(p) so a*b+c is the tiny rounding error (or zero)
        import struct
        if w == 64: cb = struct.unpack('<Q', struct.pack('<d', -float(p)))[0]
        else: cb = struct.unpack('<I', struct.pack('<f', -float(p)))[0]
        c = cb
    op, form = r.choice(ops)
    # operand placement: x1 = dst, x2 = vvvv, x3 = rm; a*b+c mapping per form
    if form == 132: d, v, m = a, c, b
    elif form == 213: d, v, m = b, a, c
    else: d, v, m = c, a, b
    xmm = [rnd_xmm(r) for _ in range(16)]
    mask = (1<<w)-1
    xmm[1] = (xmm[1] & ~mask) | d; xmm[2] = (xmm[2] & ~mask) | v; xmm[3] = (xmm[3] & ~mask) | m
    W = 1 if w == 64 else 0
    bs = bytes([0xC4, 0xE2, (W<<7) | ((15-2)<<3) | 1, op, 0xCB])   # xmm1, xmm2, xmm3
    mx = r.choice([0x1f80,0x3f80,0x5f80,0x7f80,0x9f80,0x1780,0x1e80,0x1d80,0x0f80,0x9780,0xbf80,0xdf80,0xff80,0x1fc0,0x9fc0,0x1080,0x1b80])
    out.write(json.dumps(case(r, 50_000_000 + cnt, bs, "auditF/fma-"+mode, mxcsr=mx, xmm=xmm)) + "\n"); cnt += 1
print(cnt)

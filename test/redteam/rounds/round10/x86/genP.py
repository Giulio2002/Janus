# packed FP with per-lane boundary values (underflow/overflow/integer-range/halfway) and mixed-trap lanes
import sys, random, json
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from common import *
r = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); out = open(sys.argv[3],'w')
def lane(w):
    eb, mb = (8,23) if w==32 else (11,52); bias=(1<<(eb-1))-1
    k = r.random()
    s = r.randrange(2)
    def mant():
        q = r.random()
        if q<0.3: return (1<<mb)-1-r.randrange(4)
        if q<0.6: return r.randrange(4)
        if q<0.7: return 1<<(mb-1)
        return r.getrandbits(mb)
    if k < 0.3: e = r.choice([0,0,1,1,2,bias, bias-1, bias+1])
    elif k < 0.5: e = r.choice([(1<<eb)-2, (1<<eb)-3, bias+ (w-2)//2 , bias])
    elif k < 0.7: e = bias + r.choice([30,31,32,22,23,24,52,53,62,63,64,-1,0,1])   # integer-range edges
    elif k < 0.8: return rnd_lane(r, w)
    else: e = bias - r.choice([60,63,64,100,126,125,1020,1021,1022]) if True else 0
    e = max(0, min(e, (1<<eb)-1))
    if e == (1<<eb)-1 and r.random()<0.5: e -= 1
    return (s<<(w-1)) | (e<<mb) | mant()
def vec(w):
    v = 0
    for i in range(128//w): v |= lane(w) << (w*i)
    return v
OPS = []
for o in [0x51,0x58,0x59,0x5C,0x5D,0x5E,0x5F]:
    OPS += [([0x0F,o],32),([0x66,0x0F,o],64)]
OPS += [([0x0F,0xC2],32,'i8'),([0x66,0x0F,0xC2],64,'i8'),([0x0F,0x5B],32),([0x66,0x0F,0x5B],32),([0xF3,0x0F,0x5B],32),
        ([0xF3,0x0F,0xE6],32),([0xF2,0x0F,0xE6],64),([0x66,0x0F,0xE6],64),([0x0F,0x5A],32),([0x66,0x0F,0x5A],64),
        ([0xF2,0x0F,0x7C],32),([0xF2,0x0F,0x7D],32),([0x66,0x0F,0x7C],64),([0x66,0x0F,0x7D],64),([0xF2,0x0F,0xD0],32),([0x66,0x0F,0xD0],64),
        ([0x66,0x0F,0x3A,0x08],32,'r'),([0x66,0x0F,0x3A,0x09],64,'r')]
for i in range(N):
    spec = r.choice(OPS); op, w = spec[0], spec[1]
    xmm = [vec(w) if r.random()<0.9 else vec(32 if w==64 else 64) for _ in range(16)]
    bs = op + [0xC0 | (r.randrange(8)<<3) | r.randrange(8)]
    if len(spec)>2: bs.append(r.randrange(8) if spec[2]=='i8' else r.randrange(16))
    mx = r.choice([0x1f80,0x1f80,0x3f80,0x5f80,0x7f80,0x9f80,0x1fc0,0x9fc0,0x1780,0x1e80,0x1d80,0x1b80,0x0f80,0x1f00,0x9780,0x8040,0x0000,0x1f3f])
    out.write(json.dumps(case(r, 60_000_000+i, bytes(bs), "auditP/"+bytes(op).hex(), mxcsr=mx, xmm=xmm)) + "\n")

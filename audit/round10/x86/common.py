import json, random, struct
DATA = 0x10_0004_0000
SPECIAL32 = [0x00000000,0x80000000,0x3f800000,0xbf800000,0x7f800000,0xff800000,0x7fc00000,0xffc00000,
             0x7f800001,0xff800001,0x7fa00000,0x00000001,0x80000001,0x007fffff,0x00800000,0x80800000,
             0x7f7fffff,0xff7fffff,0x4f000000,0xcf000000,0x4effffff,0xcf000001,0x3f000000,0x3fc00000,
             0x40200000,0xc0200000,0x33800000,0x0000ffff,0x5f000000,0xdf000000,0x34000000,0x3effffff]
SPECIAL64 = [0,1<<63,0x3ff0000000000000,0xbff0000000000000,0x7ff0000000000000,0xfff0000000000000,
             0x7ff8000000000000,0xfff8000000000000,0x7ff0000000000001,0xfff0000000000001,0x7ff4000000000000,
             1,(1<<63)|1,0x000fffffffffffff,0x0010000000000000,0x7fefffffffffffff,0x41e0000000000000,
             0xc1e0000000000000,0x41dfffffffc00000,0xc1e0000000200000,0x41dfffffffe00000,0xc1e00000001fffff,
             0x3fe0000000000000,0x3ff8000000000000,0x4004000000000000,0x43e0000000000000,0x3ca0000000000000,
             0x3fdfffffffffffff,0x400c000000000000, 0xc00c000000000000]
MXCSRS = [0x1f80,0x1f80,0x1f80,0x9f80,0x1fc0,0x9fc0,0x3f80,0x5f80,0x7f80,0x1f00,0x1e80,0x1d80,0x1b80,0x1780,
          0x0f80,0x1f81,0x1fbf,0x0000,0x8040,0x1d00]
def rnd_lane(r, w):
    if r.random()<0.7:
        return r.choice(SPECIAL32 if w==32 else SPECIAL64)
    return r.getrandbits(w)
def rnd_xmm(r):
    k = r.random()
    if k < 0.35:
        v = 0
        for i in range(4): v |= rnd_lane(r,32) << (32*i)
        return v
    if k < 0.7:
        return rnd_lane(r,64) | (rnd_lane(r,64)<<64)
    return r.getrandbits(128)
def rnd_reg(r):
    k = r.random()
    if k < 0.5: return DATA + r.randrange(0, 2048, 16) + (r.choice([0,0,0,1,4,8]))
    if k < 0.65: return r.choice([0,1,2,0xff,0x7fffffff,0x80000000,0xffffffff,1<<63,(1<<64)-1,0x1f,0x20,0x3f,0x40,0x808,0x2010,0xff00,0x4020,0x0820])
    if k < 0.8: return r.getrandbits(16)
    return r.getrandbits(64)
def case(r, cid, bs, cls="audit", mxcsr=None, xmm=None, regs=None, flags=None):
    regs = regs or [rnd_reg(r) for _ in range(16)]
    xmm = xmm or [rnd_xmm(r) for _ in range(16)]
    c = {"id":cid,"class":cls,"bytes":bs.hex() if isinstance(bs,(bytes,bytearray)) else bs,
         "regs":["%016x"%x for x in regs],"rflags": (r.getrandbits(12) & 0x8d5) if flags is None else flags,
         "xmm":["%032x"%x for x in xmm],"seed":r.getrandbits(32)}
    if r.random()<0.5:
        c["ymmh"]=["%032x"%r.getrandbits(128) for _ in range(16)]
    c["mxcsr"]="%x"%(mxcsr if mxcsr is not None else r.choice(MXCSRS))
    return c
def modrm_tail(r, allow_reg=True, allow_mem=True):
    """random ModRM + SIB + disp, mostly hitting the buffer"""
    mods = ([3] if allow_reg else []) + ([0,1,1,2] if allow_mem else [])
    md = r.choice(mods)
    reg = r.randrange(8); rm = r.randrange(8)
    out = [md<<6 | reg<<3 | rm]
    if md != 3:
        if rm == 4:
            out.append(r.randrange(256))
        if md == 1: out.append(r.choice([0,0,16,32,0x10,0x40,0xf0]))
        elif md == 2: out += [r.choice([0,16,32]),0,0,0]
        elif md == 0 and rm == 5: out += [r.choice([0,16]),0,0,0]  # rip-rel
    return out

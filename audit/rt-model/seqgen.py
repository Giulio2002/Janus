import random, json, sys
# amd64 straight-line sequence generator for the Janus rt-model audit (axis 2).
# Emits layout.Case JSON lines with a "seq" of instruction encodings (hex), each accepted by
# the model, non-branching, position-independent (no RIP-relative). Buffer at DataBase.
DataBase=0x10_0004_0000
N=int(sys.argv[1]) if len(sys.argv)>1 else 20000
seed=int(sys.argv[2]) if len(sys.argv)>2 else 1
rng=random.Random(seed)
# low 3 bits register numbers; REX.B/R extend. We stick to the 16 regs.
# encoding-order index: 0 RAX 1 RCX 2 RDX 3 RBX 4 RSP 5 RBP 6 RSI 7 RDI 8..15 R8..R15
def modrm(mod,reg,rm): return bytes([(mod<<6)|((reg&7)<<3)|(rm&7)])
def rex(w,r,x,b): 
    v=0x40|(w<<3)|((r>>3)<<2)|((x>>3)<<1)|(b>>3)
    return bytes([v])
def h(b): return b.hex()

ALU=[0x00,0x08,0x10,0x18,0x20,0x28,0x30,0x38] # ADD OR ADC SBB AND SUB XOR CMP
ALUdig={0:0,8:1,0x10:2,0x18:3,0x20:4,0x28:5,0x30:6,0x38:7}

def pick_reg(): return rng.randrange(16)
def pick_reg_no_sp(): 
    r=rng.randrange(16)
    return r
def imm8(): return bytes([rng.randrange(256)])
def imm32(): return bytes([rng.randrange(256) for _ in range(4)])

def rr_alu(w64):
    op=rng.choice(ALU); 
    a=pick_reg(); b=pick_reg()
    pre=rex(1 if w64 else 0, b, 0, a) if (w64 or a>=8 or b>=8) else b''
    # form 01: r/m, reg  => dst=a (rm), src=b (reg)
    return pre+bytes([op|1])+modrm(3,b,a)
def rr_alu8(withrex):
    op=rng.choice(ALU)
    a=pick_reg() if withrex else rng.randrange(8)
    b=pick_reg() if withrex else rng.randrange(8)
    pre=rex(0,b,0,a) if (withrex or a>=8 or b>=8) else b''
    return pre+bytes([op|0])+modrm(3,b,a)   # byte form, r/m,reg (AH/BH when no rex and 4..7)
def rr_alu16():
    op=rng.choice(ALU); a=rng.randrange(8); b=rng.randrange(8)
    return b'\x66'+bytes([op|1])+modrm(3,b,a)
def ri_alu(w64):
    op=rng.choice(ALU); dig=ALUdig[op]; a=pick_reg()
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    if rng.random()<0.5:
        return pre+bytes([0x83])+modrm(3,dig,a)+imm8()
    return pre+bytes([0x81])+modrm(3,dig,a)+imm32()
def mov_rr(w64):
    a=pick_reg(); b=pick_reg()
    pre=rex(1 if w64 else 0,b,0,a) if (w64 or a>=8 or b>=8) else b''
    return pre+bytes([0x89])+modrm(3,b,a)
def mov_ri(w64):
    a=pick_reg()
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    return pre+bytes([0xC7])+modrm(3,0,a)+imm32()
def unary(w64):
    a=pick_reg(); dig=rng.choice([2,3]) # NOT, NEG
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    return pre+bytes([0xF7])+modrm(3,dig,a)
def incdec(w64):
    a=pick_reg(); dig=rng.choice([0,1])
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    return pre+bytes([0xFF])+modrm(3,dig,a)
def muldiv(w64):
    a=pick_reg(); dig=rng.choice([4,5,6,7])
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    return pre+bytes([0xF7])+modrm(3,dig,a)
def shift(w64):
    a=pick_reg(); dig=rng.choice([0,1,4,5,7]) # rol ror shl shr sar
    pre=rex(1 if w64 else 0,0,0,a) if (w64 or a>=8) else b''
    r=rng.random()
    if r<0.4: return pre+bytes([0xC1])+modrm(3,dig,a)+imm8()  # by imm8
    if r<0.7: return pre+bytes([0xD1])+modrm(3,dig,a)         # by 1
    return pre+bytes([0xD3])+modrm(3,dig,a)                   # by CL
def rcx_(w64):
    a=pick_reg(); dig=rng.choice([2,3])
    pre=rex(1 if w64 else 0,0,0,a) if True else b''
    r=rng.random()
    if r<0.5: return pre+bytes([0xC1])+modrm(3,dig,a)+imm8()
    if r<0.75: return pre+bytes([0xD1])+modrm(3,dig,a)
    return pre+bytes([0xD3])+modrm(3,dig,a)
def shd(w64):
    a=pick_reg(); b=pick_reg(); left=rng.random()<0.5
    op=0xA4 if left else 0xAC
    pre=rex(1 if w64 else 0,b,0,a)
    if rng.random()<0.5:
        return pre+bytes([0x0F,op])+modrm(3,b,a)+imm8()
    return pre+bytes([0x0F,op|1])+modrm(3,b,a)  # by CL
def setcc():
    a=rng.randrange(8); cc=rng.randrange(16)
    return bytes([0x0F,0x90|cc])+modrm(3,0,a)
def cmovcc(w64):
    a=pick_reg(); b=pick_reg(); cc=rng.randrange(16)
    pre=rex(1 if w64 else 0,a,0,b)
    return pre+bytes([0x0F,0x40|cc])+modrm(3,a,b)
def bitcnt(w64):
    a=pick_reg(); b=pick_reg(); op=rng.choice([0xBC,0xBD])
    pre=rex(1 if w64 else 0,a,0,b)
    if rng.random()<0.4: # tzcnt/lzcnt/popcnt need F3
        pfx=b'\xf3'
        op=rng.choice([0xBC,0xBD,0xB8])
        return pfx+pre+bytes([0x0F,op])+modrm(3,a,b)
    return pre+bytes([0x0F,op])+modrm(3,a,b)
def bt(w64):
    a=pick_reg(); dig=rng.choice([4,5,6,7])
    pre=rex(1 if w64 else 0,0,0,a)
    return pre+bytes([0x0F,0xBA])+modrm(3,dig,a)+imm8()
def btr(w64):
    a=pick_reg(); b=pick_reg(); op=rng.choice([0xA3,0xAB,0xB3,0xBB])
    pre=rex(1 if w64 else 0,b,0,a)
    return pre+bytes([0x0F,op])+modrm(3,b,a)
def bswap(w64):
    a=pick_reg()
    pre=rex(1 if w64 else 0,0,0,a)
    return pre+bytes([0x0F,0xC8|(a&7)])
def movzx():
    a=pick_reg(); b=pick_reg(); sign=rng.random()<0.5
    sw=rng.choice([8,16])
    op=(0xBE if sign else 0xB6) if sw==8 else (0xBF if sign else 0xB7)
    pre=rex(1,a,0,b)
    return pre+bytes([0x0F,op])+modrm(3,a,b)
def test_rr(w64):
    a=pick_reg(); b=pick_reg()
    pre=rex(1 if w64 else 0,b,0,a)
    return pre+bytes([0x85])+modrm(3,b,a)
def xchg_rr(w64):
    a=pick_reg(); b=pick_reg()
    pre=rex(1 if w64 else 0,b,0,a)
    return pre+bytes([0x87])+modrm(3,b,a)
def cbw():
    pre=rng.choice([b'\x48',b'\x66',b''])
    return pre+bytes([rng.choice([0x98,0x99])])
def flagop():
    return bytes([rng.choice([0xF8,0xF9,0xF5])]) # clc stc cmc
def lea():
    a=pick_reg(); base=rng.choice([0,1,2,3,5,6,7]) # avoid RSP sib complexity; base reg
    disp=rng.randrange(-64,64)
    pre=rex(1,a,0,base)
    return pre+bytes([0x8D])+modrm(1,a,base)+bytes([disp&0xff])

POOL=[rr_alu,ri_alu,mov_rr,mov_ri,unary,incdec,muldiv,shift,rcx_,shd,
      cmovcc,bitcnt,bt,btr,bswap,test_rr,xchg_rr,cbw,flagop,lea]
POOL8=[rr_alu8,rr_alu16,setcc,movzx]

def gen_instr():
    r=rng.random()
    if r<0.18:
        f=rng.choice(POOL8)
        if f in (rr_alu8,): return f(rng.random()<0.5)
        return f()
    f=rng.choice(POOL)
    try:
        return f(rng.random()<0.6)
    except TypeError:
        return f()

out=open(sys.argv[3] if len(sys.argv)>3 else '/dev/stdout','w')
for cid in range(N):
    k=rng.randrange(5,21)
    seq=[]
    for _ in range(k):
        seq.append(h(gen_instr()))
    # random state; keep RSP and some regs pointing into the buffer so memory forms (lea/div edge) stay sane
    regs=[]
    for i in range(16):
        c=rng.random()
        if c<0.15: regs.append(hex(DataBase+rng.randrange(0,3900)))
        elif c<0.3: regs.append(hex(rng.choice([0,1,2,0xffffffffffffffff,0x8000000000000000,0x7fffffffffffffff,0xffffffff,0x80000000])))
        else: regs.append(hex(rng.getrandbits(64)))
    regs[4]=hex(DataBase+0x800)  # RSP aligned in buffer
    xmm=[hex(rng.getrandbits(128)) for _ in range(16)]
    rflags=rng.randrange(0,1<<12) & ((1<<0)|(1<<2)|(1<<4)|(1<<6)|(1<<7)|(1<<11))  # DF left 0
    case={"id":cid,"class":"seq","bytes":"","regs":regs,"rflags":rflags,
          "xmm":xmm,"seed":rng.randrange(1<<32),"seq":seq}
    out.write(json.dumps(case)+"\n")
out.close()

import random,json,sys,struct
# arm64 straight-line block generator for the rt-model audit (axis 2).
DataBase=0x10_0000_0000+0x4_0000
N=int(sys.argv[1]); seed=int(sys.argv[2]); outp=sys.argv[3]; dczid=int(sys.argv[4]) if len(sys.argv)>4 else 7
rng=random.Random(seed)
def reg(nosp=True): return rng.randrange(0,31)  # x0..x30, avoid 31 (sp/zr) mostly
def imm(bits): return rng.randrange(0,1<<bits)
# instruction builders returning a 32-bit int. Only non-branch, register/immediate data-proc and
# a few buffer loads/stores. Avoid: branches, loads/stores with wild addresses (use buffer regs),
# system, SIMD (keep simpler; vectors add state but fine). Include some SIMD data-proc too.
def addsub_imm():
    sf=rng.randrange(2); op=rng.randrange(2); S=rng.randrange(2); sh=rng.randrange(2)
    imm12=imm(12); rn=reg(); rd=reg()
    return (sf<<31)|(op<<30)|(S<<29)|(0b100010<<23)|(sh<<22)|(imm12<<10)|(rn<<5)|rd
def addsub_shift():
    sf=rng.randrange(2); op=rng.randrange(2); S=rng.randrange(2); sh=rng.randrange(3)
    rm=reg(); imm6=rng.randrange(0,64 if sf else 32); rn=reg(); rd=reg()
    return (sf<<31)|(op<<30)|(S<<29)|(0b01011<<24)|(sh<<22)|(0<<21)|(rm<<16)|(imm6<<10)|(rn<<5)|rd
def logical_shift():
    sf=rng.randrange(2); opc=rng.randrange(4); sh=rng.randrange(4); Nb=rng.randrange(2)
    rm=reg(); imm6=rng.randrange(0,64 if sf else 32); rn=reg(); rd=reg()
    return (sf<<31)|(opc<<29)|(0b01010<<24)|(sh<<22)|(Nb<<21)|(rm<<16)|(imm6<<10)|(rn<<5)|rd
def movewide():
    sf=rng.randrange(2); opc=rng.choice([0,2,3]); hw=rng.randrange(2 if not sf else 4); 
    imm16=imm(16); rd=reg()
    return (sf<<31)|(opc<<29)|(0b100101<<23)|(hw<<21)|(imm16<<5)|rd
def addsub_carry():
    sf=rng.randrange(2); op=rng.randrange(2); S=rng.randrange(2); rm=reg(); rn=reg(); rd=reg()
    return (sf<<31)|(op<<30)|(S<<29)|(0b11010000<<21)|(rm<<16)|(0<<10)|(rn<<5)|rd
def condsel():
    sf=rng.randrange(2); op=rng.randrange(2); rm=reg(); cond=rng.randrange(16); o2=rng.randrange(2); rn=reg(); rd=reg()
    return (sf<<31)|(op<<30)|(0<<29)|(0b11010100<<21)|(rm<<16)|(cond<<12)|(o2<<10)|(rn<<5)|rd
def condcmp():
    sf=rng.randrange(2); op=rng.randrange(2); imm=rng.randrange(2); rm=reg() if not imm else rng.randrange(32)
    cond=rng.randrange(16); rn=reg(); nzcv=rng.randrange(16)
    return (sf<<31)|(op<<30)|(1<<29)|(0b11010010<<21)|(rm<<16)|(cond<<12)|(imm<<11)|(0<<10)|(rn<<5)|(0<<4)|nzcv
def dp2():
    sf=rng.randrange(2); rm=reg(); opc=rng.choice([0b000010,0b000011,0b001000,0b001001,0b001010,0b001011]); rn=reg(); rd=reg()
    return (sf<<31)|(0<<30)|(0<<29)|(0b11010110<<21)|(rm<<16)|(opc<<10)|(rn<<5)|rd
def dp1():
    sf=rng.randrange(2); opc=rng.choice([0,1,2,4,5]); rn=reg(); rd=reg()
    if opc==3 and not sf: opc=2
    return (sf<<31)|(1<<30)|(0<<29)|(0b11010110<<21)|(0<<16)|(opc<<10)|(rn<<5)|rd
def dp3():
    sf=rng.randrange(2); op31=rng.choice([0,0,0]); o0=rng.randrange(2); rm=reg(); ra=reg(); rn=reg(); rd=reg()
    return (sf<<31)|(0<<29)|(0b11011<<24)|(op31<<21)|(rm<<16)|(o0<<15)|(ra<<10)|(rn<<5)|rd
def bitfield():
    sf=rng.randrange(2); opc=rng.choice([0,1,2]); Nb=sf; 
    immr=rng.randrange(0,64 if sf else 32); imms=rng.randrange(0,64 if sf else 32); rn=reg(); rd=reg()
    return (sf<<31)|(opc<<29)|(0b100110<<23)|(Nb<<22)|(immr<<16)|(imms<<10)|(rn<<5)|rd
def extr():
    sf=rng.randrange(2); Nb=sf; rm=reg(); imms=rng.randrange(0,64 if sf else 32); rn=reg(); rd=reg()
    return (sf<<31)|(0<<29)|(0b100111<<23)|(Nb<<22)|(0<<21)|(rm<<16)|(imms<<10)|(rn<<5)|rd
def logimm():
    # pick a valid bitmask by using N,immr,imms from a small vetted set
    sf=rng.randrange(2); opc=rng.randrange(4)
    # use common encodable patterns: N=sf, imms with not-all-ones
    Nb=sf if sf else 0
    immr=rng.randrange(0,64 if sf else 32); imms=rng.randrange(0,62 if sf else 30)
    rn=reg(); rd=reg()
    return (sf<<31)|(opc<<29)|(0b100100<<23)|(Nb<<22)|(immr<<16)|(imms<<10)|(rn<<5)|rd
def ldst_buf():
    # LDR/STR Xt, [Xn, #imm] with Xn pointing into buffer. unsigned-offset form.
    size=3; opc=rng.randrange(2) # 0 store 1 load (64-bit)
    base=rng.choice([20,21,22,23])  # regs we set into buffer
    imm12=rng.randrange(0,64)
    rt=reg()
    return (size<<30)|(0b111<<27)|(0<<26)|(0b01<<24)|(opc<<22)|(imm12<<10)|(base<<5)|rt

def fpdp2():
    # FADD/FSUB/FMUL/FDIV/FMAX/FMIN/FNMUL on S(00)/D(01)
    ftype=rng.choice([0,1]); rm=rng.randrange(32); opc=rng.choice([0b0000,0b0001,0b0010,0b0011,0b0100,0b0101,0b1000]); rn=rng.randrange(32); rd=rng.randrange(32)
    return (0b00011110<<24)|(ftype<<22)|(1<<21)|(rm<<16)|(opc<<12)|(0b10<<10)|(rn<<5)|rd
def fpdp1():
    ftype=rng.choice([0,1]); opc=rng.choice([0b000000,0b000001,0b000010,0b000011]); rn=rng.randrange(32); rd=rng.randrange(32)
    return (0b00011110<<24)|(ftype<<22)|(1<<21)|(opc<<15)|(0b10000<<10)|(rn<<5)|rd
def fpcmp():
    ftype=rng.choice([0,1]); rm=rng.randrange(32); rn=rng.randrange(32); opc=rng.choice([0,1,2,3])<<3
    return (0b00011110<<24)|(ftype<<22)|(1<<21)|(rm<<16)|(0b1000<<10)|(rn<<5)|opc
def vthreesame():
    Q=rng.randrange(2); U=rng.randrange(2); size=rng.randrange(4); rm=rng.randrange(32)
    opcode=rng.choice([0b10000,0b10001,0b00011]); rn=rng.randrange(32); rd=rng.randrange(32)
    return (0<<31)|(Q<<30)|(U<<29)|(0b01110<<24)|(size<<22)|(1<<21)|(rm<<16)|(opcode<<11)|(1<<10)|(rn<<5)|rd
def fmovgen():
    # FMOV W/X <-> S/D (fmovGen)
    sf=rng.choice([0,1]); ftype=1 if sf else 0; rmode=0; opcode=rng.choice([6,7]); rn=rng.randrange(32); rd=rng.randrange(32)
    return (sf<<31)|(0b0011110<<24)|(ftype<<22)|(1<<21)|(rmode<<19)|(opcode<<16)|(rn<<5)|rd
FPPOOL=[fpdp2,fpdp1,fpcmp,vthreesame,fmovgen,fmovgen]
POOL=[addsub_imm,addsub_shift,logical_shift,movewide,addsub_carry,condsel,condcmp,dp2,dp1,dp3,bitfield,extr,logimm,ldst_buf]
FPMODE = len(sys.argv)>5 and sys.argv[5]=='fp'
def gen_instr():
    pool = (POOL+FPPOOL) if FPMODE else POOL
    return rng.choice(pool)() & 0xffffffff

out=open(outp,'w')
for cid in range(N):
    k=rng.randrange(5,21)
    words=[("0x%08x"%gen_instr()) for _ in range(k)]
    X=[]
    for i in range(31):
        c=rng.random()
        if i in (20,21,22,23): X.append(hex(DataBase+rng.randrange(0,3900)&~7))
        elif c<0.3: X.append(hex(rng.choice([0,1,2,0xffffffffffffffff,0x8000000000000000,0x7fffffffffffffff])))
        else: X.append(hex(rng.getrandbits(64)))
    sp=hex((DataBase+0x800)&~15)
    V=[hex(rng.getrandbits(128)) for _ in range(32)]
    case={"id":cid,"class":"a64seq","word":"0x0","pc":hex(0x10_0000_0800),
          "x":X,"sp":sp,"nzcv":rng.randrange(16),"seed":rng.randrange(1<<32),
          "dczid":dczid,"v":V,"words":words}
    out.write(json.dumps(case)+"\n")
out.close()

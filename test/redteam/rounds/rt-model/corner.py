import random,json,sys
DataBase=0x10_0004_0000
mode=sys.argv[1]; N=int(sys.argv[2]); seed=int(sys.argv[3]); outp=sys.argv[4]
rng=random.Random(seed)
def modrm(mod,reg,rm): return bytes([(mod<<6)|((reg&7)<<3)|(rm&7)])
def rex(w,r,b): return bytes([0x40|(w<<3)|((r>>3)<<2)|(b>>3)])
def h(b): return b.hex()
def imm8(): return bytes([rng.randrange(256)])
def imm32(): return bytes([rng.randrange(256) for _ in range(4)])

def adc_chain():
    # define CF deterministically, then a chain keeping CF defined: ADD/ADC/SUB/SBB/INC/DEC/NEG/MOV
    seq=[]
    seq.append(rng.choice([b'\xf8',b'\xf9']).hex())  # CLC/STC: CF defined
    k=rng.randrange(6,18)
    w=rng.random()<0.6
    for _ in range(k):
        c=rng.random()
        a=rng.randrange(16); b=rng.randrange(16)
        if c<0.45:  # ADC/SBB reg,reg  (reads+writes CF)
            op=rng.choice([0x11,0x19])  # ADC r/m,reg ; SBB r/m,reg
            seq.append(h(rex(1 if w else 0,b,a)+bytes([op])+modrm(3,b,a)))
        elif c<0.7:  # ADD/SUB reg,reg (writes CF)
            op=rng.choice([0x01,0x29])
            seq.append(h(rex(1 if w else 0,b,a)+bytes([op])+modrm(3,b,a)))
        elif c<0.82:  # ADC/SBB reg,imm8
            op=rng.choice([2,3]); 
            seq.append(h(rex(1 if w else 0,0,a)+bytes([0x83])+modrm(3,op,a)+imm8()))
        elif c<0.92:  # MOV reg,reg (no flags)
            seq.append(h(rex(1 if w else 0,b,a)+bytes([0x89])+modrm(3,b,a)))
        else:  # NEG (writes CF)
            seq.append(h(rex(1 if w else 0,0,a)+bytes([0xF7])+modrm(3,3,a)))
    return seq

def partial():
    # partial-register writes (8/16-bit, AH/BH) interleaved with wide reads
    seq=[]
    k=rng.randrange(6,20)
    for _ in range(k):
        c=rng.random()
        a=rng.randrange(8); b=rng.randrange(8)
        if c<0.3: # 8-bit ALU r/m8,r8 no rex -> AH/CH/DH/BH when 4..7
            op=rng.choice([0x00,0x08,0x20,0x28,0x30])
            seq.append(h(bytes([op])+modrm(3,b,a)))
        elif c<0.45: # 8-bit MOV r/m8,r8 no rex
            seq.append(h(bytes([0x88])+modrm(3,b,a)))
        elif c<0.55: # MOV r8, imm8 (B0+r) no rex -> AH..BH for 4..7
            r=rng.randrange(8); seq.append(h(bytes([0xB0+r])+imm8()))
        elif c<0.68: # 16-bit op (66) r/m16,r16
            op=rng.choice([0x01,0x29,0x31,0x21,0x09])
            seq.append(h(b'\x66'+bytes([op])+modrm(3,b,a)))
        elif c<0.78: # 8-bit with REX -> SPL/BPL/SIL/DIL
            a2=rng.randrange(16); b2=rng.randrange(16)
            seq.append(h(rex(0,b2,a2)+bytes([0x00])+modrm(3,b2,a2)))
        elif c<0.9: # wide read: ADD r64, r/m64 using the partially-written regs
            a2=rng.randrange(8); b2=rng.randrange(8)
            seq.append(h(rex(1,a2,b2)+bytes([0x03])+modrm(3,a2,b2)))
        else: # MOVZX/MOVSX r64, r/m8 (reads AH/BH)
            a2=rng.randrange(8); b2=rng.randrange(8); op=rng.choice([0xB6,0xBE])
            seq.append(h(bytes([0x0F,op])+modrm(3,a2,b2)))  # no rex: r/m8 4..7 = AH..BH
    return seq

def shiftzero():
    # shifts by 0 or >=width and by CL set to 0/width, then read flags via setcc
    seq=[]
    k=rng.randrange(5,16)
    w=rng.random()<0.5
    for _ in range(k):
        c=rng.random(); a=rng.randrange(16)
        if c<0.5:
            dig=rng.choice([0,1,4,5,7]); 
            cnt=rng.choice([0,1,8,16,31,32,63])&0xff
            seq.append(h(rex(1 if w else 0,0,a)+bytes([0xC1])+modrm(3,dig,a)+bytes([cnt])))
        elif c<0.7:
            dig=rng.choice([0,1,4,5,7])
            seq.append(h(rex(1 if w else 0,0,a)+bytes([0xD3])+modrm(3,dig,a)))  # by CL
        elif c<0.85: # SHLD/SHRD by imm
            b=rng.randrange(16); op=rng.choice([0xA4,0xAC]); cnt=rng.choice([0,1,15,16,31,32,63])&0xff
            seq.append(h(rex(1 if w else 0,b,a)+bytes([0x0F,op])+modrm(3,b,a)+bytes([cnt])))
        else: # set CL to a chosen value via MOV CL,imm8
            seq.append(h(bytes([0xB1])+bytes([rng.choice([0,1,8,16,31,32,63,64])&0xff])))
    return seq

gens={'adc':adc_chain,'partial':partial,'shiftzero':shiftzero}
g=gens[mode]
out=open(outp,'w')
for cid in range(N):
    seq=g()
    regs=[hex(rng.getrandbits(64)) for _ in range(16)]
    regs[4]=hex(DataBase+0x800)
    xmm=[hex(rng.getrandbits(128)) for _ in range(16)]
    rflags=rng.randrange(0,1<<12)&((1<<0)|(1<<2)|(1<<4)|(1<<6)|(1<<7)|(1<<11))
    out.write(json.dumps({"id":cid,"class":mode,"bytes":"","regs":regs,"rflags":rflags,"xmm":xmm,"seed":rng.randrange(1<<32),"seq":seq})+"\n")
out.close()

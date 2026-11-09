# hand-picked boundary encodings (prefix rules, VEX field rules, #UD neighbours, reserved imm bits)
import sys, random, json
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from common import *
r = random.Random(11); K = int(sys.argv[1]); out = open(sys.argv[2],'w')
H = lambda s: bytes.fromhex(s.replace(' ',''))
L = """
0f38f0c1 ; MOVBE reg form #UD
0f38f003 ; MOVBE eax,[rbx]
660f38f003 ; MOVBE ax,[rbx]
66480f38f003 ; MOVBE rax,[rbx] (66+W)
480f38f103 ; MOVBE [rbx],rax
f30f38f003 ; F3 MOVBE reserved
f20f38f003 ; CRC32 r32,m8
66f20f38f003 ; CRC32 with 66 on 8-bit
f2660f38f103 ; CRC32 16 (F2 66 order)
66f20f38f103 ; CRC32 16
66f2480f38f103 ; CRC32 16 + REX.W
f2480f38f0c3 ; CRC32 r64, bl
f20f38f0c4 ; CRC32 eax, ah
f2400f38f0c4 ; CRC32 eax, spl
f3f20f38f103 ; F3 F2 duplicate group1
f2f30f1001 ; F2 F3 dup MOVSx
660f380003 ; PSHUFB
0f380003 ; MMX PSHUFB
660f3808c1 ; PSIGNB
f3660f3800c1 ; F3 66 PSHUFB
48660f5801 ; REX before 66 (ignored by hw)
66480f5801 ; ADDPD + REX.W
f0660f5801 ; LOCK ADDPD #UD
2e660f5801 ; CS ADDPD
640f5801 ; FS ADDPS
660f5803 ; ADDPD
66f30f58c1 ; 66 F3 ADDSS
f3660f58c1 ; F3 66 ADDSS
0fc2c108 ; CMPPS imm 8
0fc2c107 ; CMPPS imm 7
660f3a08c110 ; ROUNDPS imm 16
660f3a08c10f ; ROUNDPS imm 15
660f3a09c10c ; ROUNDPD imm 12
660f3a63c180 ; PCMPISTRI imm 0x80
660f3a63c17f ; PCMPISTRI imm 0x7f
66480f3a61c10c ; PCMPESTRI REX.W
660f3a61c10c ; PCMPESTRI
660f3a60c1 46 ; PCMPESTRM
0f3a0fc108 ; MMX PALIGNR
660f3a0fc111 ; PALIGNR 17
660f73e101 ; PSRAQ reserved /4
660f71d103 ; PSRLW imm
660f711103 ; PSRLW imm mem form
660f73f904 ; PSLLDQ
660f73d914 ; PSRLDQ 20
660fc50301 ; PEXTRW mem
660fc5c109 ; PEXTRW reg imm 9
66480fc5c109 ; PEXTRW REX.W
660fc4c10a ; PINSRW imm 10
66480f3a16c103 ; PEXTRQ imm 3
660f3a16c107 ; PEXTRD imm 7
660f3a14c11f ; PEXTRB imm 31
66480f3a14c11f ; PEXTRB W
660f3a17c107 ; EXTRACTPS imm 7
66480f3a17c103 ; EXTRACTPS W
660f3a20c4 13 ; PINSRB ah? (r32 spl)
660f3a2003 13 ; PINSRB mem
66480f3a22c103 ; PINSRQ imm 3
660f3a21c1ff ; INSERTPS reg
660f3a2103ff ; INSERTPS mem
660f3a40c1ff ; DPPS (rejected)
0f53c1 ; RCPPS rejected
0fc3c1 ; MOVNTI reg #UD
0fc303 ; MOVNTI
660fc303 ; 66 MOVNTI
480fc303 ; MOVNTI 64
f20ff0c1 ; LDDQU reg #UD
f20ff003 ; LDDQU
660f382a03 ; MOVNTDQA
660f382ac1 ; MOVNTDQA reg
0f12c1 ; MOVHLPS
0f1203 ; MOVLPS load
0f13c1 ; MOVLPS store reg #UD
660f12c1 ; MOVLPD reg #UD
0f50c1 ; MOVMSKPS
0f5003 ; MOVMSKPS mem #UD
660fd7c1 ; PMOVMSKB
660fd703 ; PMOVMSKB mem
660f3817c1 ; PTEST
660f3810c1 ; PBLENDVB
660f3841c1 ; PHMINPOSUW
f30f5bc1 ; CVTTPS2DQ
660f5bc1 ; CVTPS2DQ
f20fe6c1 ; CVTPD2DQ
660fe6c1 ; CVTTPD2DQ
f30fe6c1 ; CVTDQ2PD
f30fe603 ; CVTDQ2PD m64
0f5ac1 ; CVTPS2PD
660f5ac1 ; CVTPD2PS
0f5d c1 ; MINPS
0f5f c1 ; MAXPS
660f5dc1 ; MINPD
660fc2c101 ; CMPPD LT
0f51c1 ; SQRTPS
f20f7cc1 ; HADDPS
660fd0c1 ; ADDSUBPD
f20f12c1 ; MOVDDUP
c4e278f2c3 ; ANDN eax,eax,ebx
c4e27cf2c3 ; ANDN L=1
c4e279f2c3 ; ANDN pp=1
c4e2f8f2c3 ; ANDN W1
c4e278f3cb ; BLSR
c4e278f3c3 ; BLS /0 #UD
c4e278f3e3 ; BLS /4 #UD
c4e260f3d3 ; BLSMSK vvvv
c4e278f5c3 ; BZHI
c4e27bf6c3 ; MULX
c4e27af6c3 ; MULX pp=F3 (#UD)
c4e278f6c3 ; MULX pp=0
c4e3fbf0c105 ; RORX 64
c4e37bf0c125 ; RORX 32 imm 37
c4e373f0c105 ; RORX vvvv!=1111 #UD
c4e37ff0c105 ; RORX L1
c4e279f7c3 ; SHLX
c4e27af7c3 ; SARX
c4e27bf7c3 ; SHRX
c4e278f7c3 ; BEXTR
c4e2f8f7c3 ; BEXTR64
c4e271a9c2 ; VFMADD213SS
c4e2f1a9c2 ; VFMADD213SD
c4e275a9c2 ; VFMADD213SS L1
c4e271aac2 ; VFMSUB213PS? (aa packed)
c4e271bfc2 ; VFNMSUB231SS
66c4e271a9c2 ; 66 VEX
f0c4e271a9c2 ; LOCK VEX
48c4e271a9c2 ; REX VEX
2ec4e271a9c2 ; CS VEX
c5f877 ; VZEROUPPER
c5f077 ; VZEROUPPER vvvv
c5fc77 ; VZEROALL
c4e17877 ; VZEROUPPER C4
c4c17877 ; VZEROUPPER C4 B
c5f9d7c1 ; VPMOVMSKB
c5f9d703 ; VPMOVMSKB mem
c4e27978c1 ; VPBROADCASTB
c4e2f978c1 ; VPBROADCASTB W1
c4e27917c1 ; VPTEST
c4e27117c1 ; VPTEST vvvv
c5f9efc1 ; VPXOR
c5fdefc1 ; VPXOR 256
c4e27900c1 ; VPSHUFB (rejected?)
c4e078f2c3 ; map 0
c4e478f2c3 ; map 4
"""
i = 0
for line in L.strip().splitlines():
    hx, name = line.split(';'); bs = H(hx)
    for k in range(K):
        regs = [rnd_reg(r) for _ in range(16)]
        regs[3] = DATA + 0x100 + r.choice([0,0,0,8,1])   # rbx -> buffer
        out.write(json.dumps(case(r, 40_000_000 + i, bs, "auditC/" + name.strip())) + "\n"); i += 1
print(i)

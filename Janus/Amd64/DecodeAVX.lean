import Janus.Amd64.Instr
import Janus.Amd64.DecodeSSE

/-!
# Decoder for the AVX / AVX2 / FMA3 instructions (WP-F)

`DecodeAVX.vex` is consulted by `Janus.Amd64.decode` for a VEX instruction (`C4`/`C5` at the very
start of the instruction, no other prefix) that `Decode.vexOp` (the moves and compares of
`memmove`/`bytealg`, BMI1/BMI2, scalar FMA3) does not accept. It re-reads the VEX prefix (SDM
Vol. 2 §2.3.5–2.3.6: `C5 R̄ v̄v̄v̄v̄ L pp`, `C4 R̄ X̄ B̄ m-mmmm, W v̄v̄v̄v̄ L pp`) and decodes the
opcode of the selected map (1 `0F`, 2 `0F38`, 3 `0F3A`) with the implied prefix `pp` (0 none,
1 `66`, 2 `F3`, 3 `F2`), using the main decoder's ModRM parser (`mrm`, as for `DecodeSSE`). The
opcodes accepted here and by `vexOp` are disjoint (the only shared opcode, `0F 77`, is
`VZEROUPPER` at `VEX.L0` there and `VZEROALL` at `VEX.L1` here), so the combination is a plain
`Option.orElse`.

Every field the SDM fixes for an instruction is checked and anything else is rejected
(`#UD` on hardware, or a different instruction):

* `VEX.vvvv` must be `1111` where the instruction has no such operand (two-operand forms, the
  moves, the extracts and broadcasts);
* `VEX.L`: the 128-bit-only instructions (`VMOVD/Q`, `VPINSR*`, `VPEXTR*`, `VINSERTPS`,
  `VEXTRACTPS`, `VMOVLPS`..., `VMOVHLPS`/`VMOVLHPS`, `VPHMINPOSUW`, `VPCMPxSTRx`) need `L0`, the
  256-bit-only ones (`VPERMD/PS/Q/PD`, `VPERM2I128/F128`, `VINSERTI128/F128`, `VEXTRACTI128/F128`,
  `VBROADCASTSD`, `VBROADCASTI128/F128`) `L1`; the scalar forms are `LIG` and only `L0` (what
  compilers emit) is accepted;
* `VEX.W`: where the SDM lists `W0` or `W1` only that value is accepted (`VPERMD W0`, `VPERMQ W1`,
  the broadcasts, masked moves, blends with a register mask, `VPBLENDD`, the 128-bit inserts and
  extracts, `VPEXTRB/W/D`, `VPINSRB/W/D` `W0`, ...); where it selects the operand size
  (`VMOVD`/`VMOVQ`, `VPINSRD/Q`, `VPEXTRD/Q`, `VCVTSI2SD`, `VCVTTSD2SI`, `VPCMPESTRx`, the
  variable shifts, gathers, masked integer moves, packed FMA `PS`/`PD`) it does; elsewhere (`WIG`)
  it is ignored, as by hardware;
* register-only and memory-only forms (`VMOVMSKPS`, `VPEXTRW` `C5`, the shift groups,
  `VMOVHLPS`; the masked moves, `VMOVNTPS/PD`, `VLDDQU`, `VMOVNTDQA`, `VBROADCASTI128/F128`,
  `VMOVLPS m`...); reserved immediates (`VCMPPS imm8 ≥ 32`, `VROUNDPS imm8 ≥ 16`,
  `VPCMPxSTRx imm8<7>`) and reserved group members;
* the gathers: a VSIB memory operand (`mod ≠ 11`, `r/m = 100`, the SIB index a vector register)
  and destination, index and mask registers that are pairwise different.

Not decoded (rejected): `VRCPPS/SS`, `VRSQRTPS/SS` (implementation-specific results), `VDPPS`,
`VDPPD`, `VMASKMOVDQU`, `VLDMXCSR`/`VSTMXCSR`, the AES-NI and
`VPCLMULQDQ` VEX forms (WP-E), and everything EVEX (WP-G).
-/

namespace Janus.Amd64.DecodeAVX

open DecodeSSE (MRM pint66 pint38 pfop shiftGroup imm8)

abbrev I := AvxI XLoc Loc Addr

/-- The `r/m` operand of a VEX instruction as a general register or memory location. -/
def gpr : XLoc → Loc
  | .xmm n => .reg n
  | .mem a => .mem a

/-- Little-endian `k`-byte value. -/
def le : Nat → List Nat → Option (Nat × List Nat)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    match le k bs with
    | some (v, r) => some (b + 256 * v, r)
    | none => none

/-- A VSIB memory operand (SDM Vol. 2 §2.3.12): ModRM with `mod ≠ 11` and `r/m = 100`, then SIB,
whose index (with `VEX.X`) is a **vector** register (index `100` included), then `disp8`/`disp32`.
Returns `(reg, operand, rest, bytes)`; `a.index` is the vector index register. -/
def vsib (rex : Nat) : List Nat → Option (Nat × Addr × List Nat × Nat)
  | m :: sib :: rest =>
    let md := m / 64
    let reg := (m / 8) % 8 + 8 * ((rex / 4) % 2)
    if md = 3 ∨ m % 8 ≠ 4 then none else
    let idx := (sib / 8) % 8 + 8 * ((rex / 2) % 2)
    let sc := sib / 64
    let b := sib % 8
    let base : Option Nat := if b = 5 ∧ md = 0 then none else some (b + 8 * (rex % 2))
    let dk := if md = 1 then 1 else if md = 2 ∨ (md = 0 ∧ b = 5) then 4 else 0
    match le dk rest with
    | some (d, r) =>
      let disp := if dk = 1 then (if d ≥ 128 then d + 2 ^ 64 - 256 else d)
        else if dk = 4 then (if d ≥ 2 ^ 31 then d + 2 ^ 64 - 2 ^ 32 else d) else 0
      some (reg, ⟨base, some idx, sc, disp, false, false⟩, r, 2 + dk)
    | none => none
  | _ => none

/-- The packed integer operation of a VEX `66 0F xx` opcode: WP-D's table plus `VPUNPCKLBW`. -/
def pintV1 (op : Nat) : Option PIntOp :=
  if op = 0x60 then some (.unpckl 8) else pint66 op

/-- The packed FMA operation of `0F38 96..BF` (`op % 16 ∈ {6, 7, 8, A, C, E}`): `(form, negP,
negC, alt)`. -/
def fmaPacked (op : Nat) : Option (Nat × Bool × Bool × Nat) :=
  let form := if op / 16 = 9 then 132 else if op / 16 = 10 then 213 else 231
  if op / 16 < 9 ∨ op / 16 > 11 then none else
  match op % 16 with
  | 6 => some (form, false, false, 1)
  | 7 => some (form, false, false, 2)
  | 8 => some (form, false, false, 0)
  | 10 => some (form, false, true, 0)
  | 12 => some (form, true, false, 0)
  | 14 => some (form, true, true, 0)
  | _ => none

/-- Decode the VEX instruction with the fields of the prefix: `rex = W R X B` (un-inverted),
`v` the un-inverted `VEX.vvvv`, `l` 128/256, `pp`, the map `mp`, the opcode `op`, the bytes `bs`
after it and the number `n` of bytes before it. -/
def decodeOp (mrm : MRM) (rex v l pp mp op : Nat) (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let w1 := rex / 8 = 1
  let fin (i : Instr) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (i, len)
  let avx (i : I) (len : Nat) : Option (Instr × Nat) := fin (.avx i) len
  -- ModRM (`k` gets reg, ext, rm, rest and the length so far)
  let m (k : Nat → Nat → XLoc → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match mrm bs with
    | some (reg, ext, rm, rest, c) => k reg ext rm rest (n + 1 + c)
    | none => none
  -- ModRM, then `imm8`
  let mi (k : Nat → Nat → XLoc → Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    m fun reg ext rm rest len =>
      match imm8 rest with
      | some i => k reg ext rm i (len + 1)
      | none => none
  -- a register-only / memory-only `r/m`
  let rr (rm : XLoc) (k : Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match rm with
    | .xmm r => k r
    | .mem _ => none
  let mm (rm : XLoc) (k : Addr → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match rm with
    | .mem a => k a
    | .xmm _ => none
  let l0 := l = 128
  let l1 := l = 256
  let nv := v = 0
  -- floating-point width of the `PS` (no prefix) / `PD` (`66`) forms
  let fw := if pp = 0 then 32 else 64
  -- scalar width of the `SS` (`F3`) / `SD` (`F2`) forms
  let sw := if pp = 2 then 32 else 64
  if mp = 1 then
    match pfop op with
    | some o =>
      -- VADDPS ... VSQRTSD (0F 51 58 59 5C 5D 5E 5F)
      if pp ≤ 1 then
        if o = .sqrt ∧ ¬ nv then none else
        m fun reg _ rm _ len => avx (.fpArith o fw l reg v rm) len
      else if l0 then
        m fun reg _ rm _ len => avx (.sArith o sw reg v rm) len
      else none
    | none =>
    if pp = 1 ∧ (pintV1 op).isSome then
      match pintV1 op with
      | some o =>
        -- VEX `66 0F` packed integer (VPUNPCK*, VPACK*, VPADD*, ..., VUNPCKLPD/HPD)
        m fun reg _ rm _ len => avx (.pint o l reg v rm) len
      | none => none
    else if (op = 0x10 ∨ op = 0x11) ∧ pp ≤ 1 then
      -- VMOVUPS/VMOVUPD load and store
      if ¬ nv then none else
      m fun reg _ rm _ len =>
        if op = 0x10 then fin (.vmov false l (.xmm reg) rm) len else fin (.vmov false l rm (.xmm reg)) len
    else if (op = 0x28 ∨ op = 0x29) ∧ pp ≤ 1 then
      -- VMOVAPS/VMOVAPD (aligned)
      if ¬ nv then none else
      m fun reg _ rm _ len =>
        if op = 0x28 then fin (.vmov true l (.xmm reg) rm) len else fin (.vmov true l rm (.xmm reg)) len
    else if op = 0x2B ∧ pp ≤ 1 then
      -- VMOVNTPS/VMOVNTPD m, xmm/ymm (memory only, aligned)
      if ¬ nv then none else
      m fun reg _ rm _ len => mm rm fun a => fin (.vmov true l (.mem a) (.xmm reg)) len
    else if (op = 0x10 ∨ op = 0x11) ∧ pp ≥ 2 then
      -- VMOVSS/VMOVSD: memory load (zero-extending), store, register merge (3 operands)
      if ¬ l0 then none else
      m fun reg _ rm _ len =>
        match rm with
        | .mem a =>
          if ¬ nv then none
          else if op = 0x10 then avx (.vload (sw / 8) reg (.mem a)) len
          else fin (.movsd sw (.mem a) (.xmm reg)) len
        | .xmm r =>
          if op = 0x10 then avx (.movsRR sw reg v r) len else avx (.movsRR sw r v reg) len
    else if (op = 0x12 ∨ op = 0x16) ∧ pp ≤ 1 then
      -- VMOVLPS/VMOVLPD/VMOVHPS/VMOVHPD xmm, xmm, m64; VMOVHLPS/VMOVLHPS xmm, xmm, xmm (no prefix)
      if ¬ l0 then none else
      m fun reg _ rm _ len =>
        match rm with
        | .mem a => avx (.movHalfL (op = 0x16) reg v a) len
        | .xmm r =>
          if pp = 1 then none
          else avx (.pint (if op = 0x12 then .movhl else .unpckl 64) 128 reg v (.xmm r)) len
    else if (op = 0x13 ∨ op = 0x17) ∧ pp ≤ 1 then
      -- VMOVLPS/VMOVLPD/VMOVHPS/VMOVHPD m64, xmm (memory only): the legacy store
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => mm rm fun a => fin (.sse (.movHalf (op = 0x17) false reg a)) len
    else if (op = 0x12 ∨ op = 0x16) ∧ pp = 2 then
      -- VMOVSLDUP / VMOVSHDUP
      if ¬ nv then none else
      m fun reg _ rm _ len => avx (.movdup (if op = 0x12 then .sldup else .shdup) l reg rm) len
    else if op = 0x12 ∧ pp = 3 then
      -- VMOVDDUP
      if ¬ nv then none else
      m fun reg _ rm _ len => avx (.movdup .ddup l reg rm) len
    else if (op = 0x14 ∨ op = 0x15) ∧ pp = 0 then
      -- VUNPCKLPS / VUNPCKHPS
      m fun reg _ rm _ len => avx (.pint (if op = 0x14 then .unpckl 32 else .unpckh 32) l reg v rm) len
    else if op = 0x2A ∧ pp ≥ 2 then
      -- VCVTSI2SS / VCVTSI2SD xmm, xmm, r/m32/64
      if ¬ l0 then none else
      m fun reg _ rm _ len => avx (.cvtsi2f sw (if w1 then 64 else 32) reg v (gpr rm)) len
    else if (op = 0x2C ∨ op = 0x2D) ∧ pp ≥ 2 then
      -- VCVTTSS2SI / VCVTSS2SI / VCVTTSD2SI / VCVTSD2SI r32/64, xmm/m (the legacy instruction)
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => fin (.cvtf2si (op = 0x2C) sw (if w1 then 64 else 32) reg rm) len
    else if (op = 0x2E ∨ op = 0x2F) ∧ pp ≤ 1 then
      -- VUCOMISS/SD, VCOMISS/SD (the legacy instruction: flags only)
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => fin (.sseComi (op = 0x2F) fw reg rm) len
    else if op = 0x50 ∧ pp ≤ 1 then
      -- VMOVMSKPS / VMOVMSKPD r, xmm/ymm (register source only)
      if ¬ nv then none else
      m fun reg _ rm _ len => rr rm fun r => avx (.movmsk fw l reg r) len
    else if (op = 0x54 ∨ op = 0x56 ∨ op = 0x57) ∧ pp ≤ 1 then
      -- VANDPS/PD, VORPS/PD, VXORPS/PD (as VPAND, VPOR, VPXOR)
      let o := if op = 0x54 then SseOp.and else if op = 0x56 then .or else .xor
      m fun reg _ rm _ len => fin (.vop o l reg v rm) len
    else if op = 0x55 ∧ pp ≤ 1 then
      -- VANDNPS / VANDNPD
      m fun reg _ rm _ len => avx (.pint .andn l reg v rm) len
    else if op = 0x5A then
      -- VCVTPS2PD, VCVTPD2PS, VCVTSS2SD, VCVTSD2SS
      if pp ≤ 1 then
        if ¬ nv then none else
        m fun reg _ rm _ len => avx (.cvt (if pp = 0 then .ps2pd else .pd2ps) l reg rm) len
      else if l0 then m fun reg _ rm _ len => avx (.cvtff sw reg v rm) len
      else none
    else if op = 0x5B then
      -- VCVTDQ2PS (none), VCVTPS2DQ (66), VCVTTPS2DQ (F3)
      if ¬ nv ∨ pp = 3 then none else
      let o : CvtOp := if pp = 0 then .dq2ps else if pp = 1 then .ps2dq false else .ps2dq true
      m fun reg _ rm _ len => avx (.cvt o l reg rm) len
    else if op = 0xE6 ∧ pp ≥ 1 then
      -- VCVTTPD2DQ (66), VCVTDQ2PD (F3), VCVTPD2DQ (F2)
      if ¬ nv then none else
      let o : CvtOp := if pp = 1 then .pd2dq true else if pp = 2 then .dq2pd else .pd2dq false
      m fun reg _ rm _ len => avx (.cvt o l reg rm) len
    else if op = 0x6E ∧ pp = 1 then
      -- VMOVD / VMOVQ xmm, r/m32/64
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => avx (.movdG (if w1 then 64 else 32) reg (gpr rm)) len
    else if op = 0x7E ∧ pp = 1 then
      -- VMOVD / VMOVQ r/m32/64, xmm (the legacy instruction)
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => fin (.movdq (if w1 then 64 else 32) false reg (gpr rm)) len
    else if op = 0x7E ∧ pp = 2 then
      -- VMOVQ xmm, xmm/m64 (zero-extending)
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => avx (.vload 8 reg rm) len
    else if op = 0xD6 ∧ pp = 1 then
      -- VMOVQ xmm/m64, xmm
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len =>
        match rm with
        | .mem a => fin (.movq (.mem a) (.xmm reg)) len
        | .xmm r => avx (.vload 8 r (.xmm reg)) len
    else if op = 0x70 ∧ pp ≥ 1 then
      -- VPSHUFD (66), VPSHUFHW (F3), VPSHUFLW (F2)
      if ¬ nv then none else
      let o : VShufOp := if pp = 1 then .pshufd else if pp = 2 then .pshufhw else .pshuflw
      mi fun reg _ rm i len => avx (.shuf o l reg rm i) len
    else if (op = 0x71 ∨ op = 0x72 ∨ op = 0x73) ∧ pp = 1 then
      -- the shift groups: VPSRLW/D/Q, VPSRAW/D, VPSLLW/D/Q, VPSRLDQ, VPSLLDQ vvvv, r, imm8
      mi fun _ ext rm i len =>
        match rm, shiftGroup op ext with
        | .xmm r, some (o, e) => avx (.pshift o e l v r i) len
        | _, _ => none
    else if (op = 0x7C ∨ op = 0x7D) ∧ (pp = 1 ∨ pp = 3) then
      -- VHADDPD/VHSUBPD (66), VHADDPS/VHSUBPS (F2)
      m fun reg _ rm _ len => avx (.fpHorz (op = 0x7D) (if pp = 1 then 64 else 32) l reg v rm) len
    else if op = 0xD0 ∧ (pp = 1 ∨ pp = 3) then
      -- VADDSUBPD (66), VADDSUBPS (F2)
      m fun reg _ rm _ len => avx (.fpAddsub (if pp = 1 then 64 else 32) l reg v rm) len
    else if op = 0xC2 then
      -- VCMPPS/PD/SS/SD with the 32 predicates
      mi fun reg _ rm i len =>
        if i ≥ 32 then none
        else if pp ≤ 1 then avx (.fpCmp fw l reg v rm i) len
        else if l0 then avx (.sCmp sw reg v rm i) len
        else none
    else if op = 0xC6 ∧ pp ≤ 1 then
      -- VSHUFPS / VSHUFPD
      mi fun reg _ rm i len => avx (.pimm (if pp = 0 then .shufps else .shufpd) l reg v rm i) len
    else if op = 0xC4 ∧ pp = 1 then
      -- VPINSRW xmm, xmm, r32/m16, imm8 (W0)
      if ¬ l0 ∨ w1 then none else
      mi fun reg _ rm i len => avx (.pinsr 16 reg v (gpr rm) i) len
    else if op = 0xC5 ∧ pp = 1 then
      -- VPEXTRW r32, xmm, imm8 (register source only, W0): the legacy instruction
      if ¬ l0 ∨ ¬ nv ∨ w1 then none else
      mi fun reg _ rm i len => rr rm fun r => fin (.sse (.pextr 16 (.reg reg) r i)) len
    else if op = 0xF0 ∧ pp = 3 then
      -- VLDDQU xmm/ymm, m (memory only)
      if ¬ nv then none else
      m fun reg _ rm _ len => mm rm fun a => fin (.vmov false l (.xmm reg) (.mem a)) len
    else if op = 0x77 ∧ pp = 0 ∧ l1 ∧ nv then
      -- VZEROALL (no ModRM)
      fin (.avx .vzeroall) (n + 1)
    else none
  else if mp = 2 ∧ pp = 1 then
    match pint38 op with
    | some o =>
      -- VEX `66 0F38` packed integer (VPABS* have no `vvvv` operand)
      if (op = 0x1C ∨ op = 0x1D ∨ op = 0x1E) ∧ ¬ nv then none else
      m fun reg _ rm _ len => avx (.pint o l reg v rm) len
    | none =>
    if op = 0x00 ∨ op = 0x08 then
      -- VPSHUFB / VPSIGNB (in-lane at 256 bits)
      m fun reg _ rm _ len => fin (.vop (if op = 0 then .pshufb else .psignb) l reg v rm) len
    else if (0x20 ≤ op ∧ op ≤ 0x25) ∨ (0x30 ≤ op ∧ op ≤ 0x35) then
      -- VPMOVSX / VPMOVZX
      if ¬ nv then none else
      let k := op % 16
      let ft : Nat × Nat := if k = 0 then (8, 16) else if k = 1 then (8, 32)
        else if k = 2 then (8, 64) else if k = 3 then (16, 32) else if k = 4 then (16, 64)
        else (32, 64)
      m fun reg _ rm _ len => avx (.pmovx (op < 0x30) ft.1 ft.2 l reg rm) len
    else if op = 0x2A then
      -- VMOVNTDQA xmm/ymm, m (aligned load, memory only)
      if ¬ nv then none else
      m fun reg _ rm _ len => mm rm fun a => fin (.vmov true l (.xmm reg) (.mem a)) len
    else if op = 0x13 then
      -- VCVTPH2PS xmm/ymm, xmm/m64/m128 (F16C, W0)
      if w1 ∨ ¬ nv then none else
      m fun reg _ rm _ len => avx (.cvtph2ps l reg rm) len
    else if op = 0x41 then
      -- VPHMINPOSUW
      if ¬ l0 ∨ ¬ nv then none else
      m fun reg _ rm _ len => avx (.phminposuw reg rm) len
    else if op = 0x0C ∨ op = 0x0D then
      -- VPERMILPS / VPERMILPD (variable control, W0)
      if w1 then none else
      m fun reg _ rm _ len => avx (.permilv (if op = 0x0C then 32 else 64) l reg v rm) len
    else if op = 0x0E ∨ op = 0x0F then
      -- VTESTPS / VTESTPD (W0)
      if w1 ∨ ¬ nv then none else
      m fun reg _ rm _ len => avx (.vtest (if op = 0x0E then 32 else 64) l reg rm) len
    else if op = 0x16 ∨ op = 0x36 then
      -- VPERMPS / VPERMD ymm, ymm(idx), ymm/m256 (L1, W0)
      if ¬ l1 ∨ w1 then none else
      m fun reg _ rm _ len => avx (.permd reg v rm) len
    else if op = 0x18 ∨ op = 0x19 ∨ op = 0x58 ∨ op = 0x59 ∨ op = 0x79 then
      -- VBROADCASTSS, VBROADCASTSD (L1), VPBROADCASTD, VPBROADCASTQ, VPBROADCASTW (W0)
      if w1 ∨ ¬ nv ∨ (op = 0x19 ∧ ¬ l1) then none else
      let e := if op = 0x18 ∨ op = 0x58 then 32 else if op = 0x79 then 16 else 64
      m fun reg _ rm _ len => avx (.bcast e l reg rm) len
    else if op = 0x1A ∨ op = 0x5A then
      -- VBROADCASTF128 / VBROADCASTI128 ymm, m128 (L1, W0, memory only)
      if w1 ∨ ¬ nv ∨ ¬ l1 then none else
      m fun reg _ rm _ len => mm rm fun a => avx (.bcast 128 256 reg (.mem a)) len
    else if 0x2C ≤ op ∧ op ≤ 0x2F then
      -- VMASKMOVPS/PD load (2C 2D) and store (2E 2F) (W0, memory only)
      if w1 then none else
      let e := if op % 2 = 0 then 32 else 64
      m fun reg _ rm _ len =>
        mm rm fun a =>
          if op < 0x2E then avx (.maskmov e l true reg v a) len else avx (.maskmov e l false reg v a) len
    else if op = 0x8C ∨ op = 0x8E then
      -- VPMASKMOVD (W0) / VPMASKMOVQ (W1) load (8C) and store (8E) (memory only)
      let e := if w1 then 64 else 32
      m fun reg _ rm _ len =>
        mm rm fun a => avx (.maskmov e l (op = 0x8C) reg v a) len
    else if op = 0x45 ∨ op = 0x46 ∨ op = 0x47 then
      -- VPSRLVD/Q, VPSRAVD (W0 only), VPSLLVD/Q
      if op = 0x46 ∧ w1 then none else
      let o : VShiftOp := if op = 0x45 then .srl else if op = 0x46 then .sra else .sll
      m fun reg _ rm _ len => avx (.shiftv o (if w1 then 64 else 32) l reg v rm) len
    else if 0x90 ≤ op ∧ op ≤ 0x93 then
      -- VPGATHERDD/DQ (90), VPGATHERQD/QQ (91), VGATHERDPS/DPD (92), VGATHERQPS/QPD (93)
      let e := if w1 then 64 else 32
      let ie := if op % 2 = 0 then 32 else 64
      match vsib rex bs with
      | some (reg, a, _, c) =>
        let idx := a.index.getD 0
        if reg = v ∨ reg = idx ∨ v = idx then none
        else avx (.gather e ie l reg v a) (n + 1 + c)
      | none => none
    else
      match fmaPacked op with
      | some (form, np, nc, alt) =>
        -- packed FMA3 (W0 = PS, W1 = PD)
        m fun reg _ rm _ len => avx (.fma form np nc alt (if w1 then 64 else 32) l reg v rm) len
      | none => none
  else if mp = 3 ∧ pp = 1 then
    if op = 0x00 ∨ op = 0x01 then
      -- VPERMQ / VPERMPD ymm, ymm/m256, imm8 (L1, W1)
      if ¬ l1 ∨ ¬ w1 ∨ ¬ nv then none else
      mi fun reg _ rm i len => avx (.permq reg rm i) len
    else if op = 0x02 then
      -- VPBLENDD (W0)
      if w1 then none else
      mi fun reg _ rm i len => avx (.pimm .blendps l reg v rm i) len
    else if op = 0x04 ∨ op = 0x05 then
      -- VPERMILPS / VPERMILPD ..., imm8 (W0)
      if w1 ∨ ¬ nv then none else
      mi fun reg _ rm i len => avx (.shuf (if op = 0x04 then .permilps else .permilpd) l reg rm i) len
    else if op = 0x06 ∨ op = 0x46 then
      -- VPERM2F128 / VPERM2I128 (L1, W0)
      if ¬ l1 ∨ w1 then none else
      mi fun reg _ rm i len => avx (.perm2 reg v rm i) len
    else if op = 0x08 ∨ op = 0x09 then
      -- VROUNDPS / VROUNDPD
      if ¬ nv then none else
      mi fun reg _ rm i len =>
        if i ≥ 16 then none else avx (.fpRound (if op = 0x08 then 32 else 64) l reg rm i) len
    else if op = 0x0A ∨ op = 0x0B then
      -- VROUNDSS / VROUNDSD xmm, xmm, xmm/m, imm8
      if ¬ l0 then none else
      mi fun reg _ rm i len =>
        if i ≥ 16 then none else avx (.sRound (if op = 0x0A then 32 else 64) reg v rm i) len
    else if op = 0x0C ∨ op = 0x0D ∨ op = 0x0E ∨ op = 0x0F ∨ op = 0x42 then
      -- VBLENDPS, VBLENDPD, VPBLENDW, VPALIGNR, VMPSADBW
      let o := if op = 0x0C then PImmOp.blendps else if op = 0x0D then .blendpd
        else if op = 0x0E then .pblendw else if op = 0x0F then .palignr else .mpsadbw
      mi fun reg _ rm i len => avx (.pimm o l reg v rm i) len
    else if op = 0x14 ∨ op = 0x15 ∨ op = 0x16 ∨ op = 0x17 then
      -- VPEXTRB (W0), VPEXTRW (W0), VPEXTRD/Q (W0/W1), VEXTRACTPS (WIG): the legacy instruction
      if ¬ l0 ∨ ¬ nv ∨ ((op = 0x14 ∨ op = 0x15) ∧ w1) then none else
      let e := if op = 0x14 then 8 else if op = 0x15 then 16 else if op = 0x16 ∧ w1 then 64 else 32
      mi fun reg _ rm i len => fin (.sse (.pextr e (gpr rm) reg i)) len
    else if op = 0x18 ∨ op = 0x38 then
      -- VINSERTF128 / VINSERTI128 (L1, W0)
      if ¬ l1 ∨ w1 then none else
      mi fun reg _ rm i len => avx (.insert128 reg v rm i) len
    else if op = 0x19 ∨ op = 0x39 then
      -- VEXTRACTF128 / VEXTRACTI128 xmm/m128, ymm, imm8 (L1, W0)
      if ¬ l1 ∨ w1 ∨ ¬ nv then none else
      mi fun reg _ rm i len => avx (.extract128 rm reg i) len
    else if op = 0x1D then
      -- VCVTPS2PH xmm/m64/m128, xmm/ymm, imm8 (F16C, W0)
      if w1 ∨ ¬ nv then none else
      mi fun reg _ rm i len => avx (.cvtps2ph l rm reg i) len
    else if op = 0x20 ∨ op = 0x22 then
      -- VPINSRB (W0), VPINSRD/Q (W0/W1)
      if ¬ l0 ∨ (op = 0x20 ∧ w1) then none else
      let e := if op = 0x20 then 8 else if w1 then 64 else 32
      mi fun reg _ rm i len => avx (.pinsr e reg v (gpr rm) i) len
    else if op = 0x21 then
      -- VINSERTPS
      if ¬ l0 then none else
      mi fun reg _ rm i len =>
        match rm with
        | .xmm r => avx (.pimm .insertps 128 reg v (.xmm r) i) len
        | .mem a => avx (.insertpsM reg v a i) len
    else if op = 0x4A ∨ op = 0x4B ∨ op = 0x4C then
      -- VBLENDVPS, VBLENDVPD, VPBLENDVB dst, src1, src2, mask (`imm8<7:4>`, W0)
      if w1 then none else
      let e := if op = 0x4A then 32 else if op = 0x4B then 64 else 8
      mi fun reg _ rm i len => avx (.blendv e l reg v rm (i / 16)) len
    else if 0x60 ≤ op ∧ op ≤ 0x63 then
      -- VPCMPESTRM/I (60 61), VPCMPISTRM/I (62 63)
      if ¬ l0 ∨ ¬ nv then none else
      mi fun reg _ rm i len =>
        if i ≥ 128 then none
        else if op % 2 = 1 then fin (.sse (.pcmpstr (op < 0x62) true (w1 ∧ op < 0x62) reg rm i)) len
        else avx (.pcmpstrm (op < 0x62) (w1 ∧ op < 0x62) reg rm i) len
    else none
  else none

/-- Decode a VEX instruction at the start of `bytes` (no prefix before it): `b0 = C5` or `C4`.
`modrmOf rex` is the main decoder's ModRM parser for the REX bits `rex = W R X B`. -/
def vex (modrmOf : Nat → MRM) (b0 : Nat) (bs : List Nat) : Option (Instr × Nat) :=
  if b0 = 0xC5 then
    match bs with
    | b1 :: op :: rest =>
      let r := 1 - b1 / 128
      decodeOp (modrmOf (4 * r)) (4 * r) (15 - (b1 / 8) % 16) (if (b1 / 4) % 2 = 1 then 256 else 128)
        (b1 % 4) 1 op rest 2
    | _ => none
  else if b0 = 0xC4 then
    match bs with
    | b1 :: b2 :: op :: rest =>
      let rex := 8 * (b2 / 128) + 4 * (1 - b1 / 128) + 2 * (1 - (b1 / 64) % 2) + (1 - (b1 / 32) % 2)
      decodeOp (modrmOf rex) rex (15 - (b2 / 8) % 16) (if (b2 / 4) % 2 = 1 then 256 else 128)
        (b2 % 4) (b1 % 32) op rest 3
    | _ => none
  else none

end Janus.Amd64.DecodeAVX

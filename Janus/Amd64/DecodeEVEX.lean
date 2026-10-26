import Janus.Amd64.Instr
import Janus.Amd64.DecodeSSE

/-!
# Decoder for the AVX-512 instructions (WP-G)

`DecodeEVEX.evex` decodes an EVEX instruction (`62` at the very start of the instruction, no
other prefix); `DecodeEVEX.vex` the VEX-encoded opmask instructions (`KMOV*`, `KAND*`, `KOR*`,
`KXOR*`, `KXNOR*`, `KANDN*`, `KADD*`, `KNOT*`, `KSHIFTL/R*`, `KORTEST*`, `KTEST*`, `KUNPCK*`)
and the VEX forms of `VPCLMULQDQ` and GFNI (`VGF2P8AFFINEQB`, `VGF2P8AFFINEINVQB`,
`VGF2P8MULB`), which `Janus.Amd64.decode` consults after `Decode.vexOp` and `DecodeAVX.vex` (the
opcodes are disjoint). Both use the main decoder's ModRM parser (`modrmOf`, as `DecodeAVX`).

**The EVEX prefix** (SDM Vol. 2 §2.7): `62 P0 P1 P2` with `P0 = R̄ X̄ B̄ R̄' 0 m m m`,
`P1 = W v̄v̄v̄v̄ 1 p p`, `P2 = z L'L b V̄' a a a`. The decoder rejects `P0<3> = 1`, `P1<2> = 0`
(`EVEX.U`), maps other than 1–3. Register operands are 5 bits: `ModRM.reg` with `R` and `R'`,
`ModRM.r/m` (register form) with `B` and `X`, `vvvv` with `V'`. A memory operand is the ModRM/SIB
operand of the legacy encoding (`X` extends the SIB index, `B` the base) with the **compressed
displacement**: a `disp8` is scaled by `N`, the tuple size (SDM §2.7.5): the full vector `l/8`
(`FV` without broadcast, `FVM`), the broadcast element (`FV` with `EVEX.b`), the element for the
scalar tuples (`T1S`: broadcasts, `VPCOMPRESS`/`VPEXPAND`), the chunk for `T2`/`T4`/`T8`
(`VBROADCASTI32X4` ..., inserts, extracts), 16 for `M128` (shift counts) and `l·f/(8t)` for
`VPMOVSX/ZX` (`HVM`/`QVM`/`OVM`).

Every field the SDM fixes is checked and anything else is rejected (`#UD` on hardware or another
instruction, or an encoding this model does not cover):

* `EVEX.L'L = 11` is rejected; `EVEX.b` with a register operand is embedded rounding (`{er}`, the
  `L'L` bits are the rounding control and the length is 512) for `VADDPS/PD`, `VSUBPS/PD`,
  `VMULPS/PD`, `VDIVPS/PD`, `VSQRTPS/PD`, and `{sae}` (length 512) for `VMINPS/PD`, `VMAXPS/PD`,
  `VCMPPS/PD`; elsewhere it is rejected. `EVEX.b` with a memory operand is a broadcast and only
  accepted where the SDM allows `m32bcst`/`m64bcst`;
* `EVEX.W` where the SDM lists `W0` or `W1` (the element width of the `D`/`Q` forms, `VPERMB`
  vs `VPERMW`, ...); `WIG` forms accept both;
* `EVEX.vvvv = 1111` and `EVEX.V' = 1` (inverted) where there is no such operand;
* the write mask: `{z}` without a mask register, `{z}` with a memory destination, and any mask
  on the instructions that take none (`VPCLMULQDQ`, `VPSADBW`, `VPSLLDQ`/`VPSRLDQ`) are rejected;
  a compare into a mask takes a mask but not `{z}`;
* a mask register in `ModRM.reg` (the compares) needs `EVEX.R = EVEX.R' = 0` (the opcode
  extensions of `71`/`72`/`73` ignore them, as hardware does); a general register in `r/m` (`VPBROADCASTB/W/D/Q r`) needs
  `EVEX.X = 0`;
* register-only and memory-only forms (`VBROADCASTI32X4` ... memory only, the general-register
  broadcasts register only);
* nothing about the `VPCMP*` and `VCMPPS/PD` immediates: the predicate is `imm8<2:0>` resp.
  `imm8<4:0>`, the other bits are ignored (as by hardware).

The VEX opmask instructions check `VEX.L` (`L1` for the two-source ones, `L0` otherwise),
`VEX.W`/`pp` (the width), `VEX.vvvv = 1111` where unused, `VEX.R` and `vvvv<3>` clear for mask
registers (`VEX.B` is ignored for a mask register in `r/m`, as by hardware), and register-only
forms (everything except `KMOV k, m` and `KMOV m, k`).
-/

namespace Janus.Amd64.DecodeEVEX



abbrev I := EvexI XLoc Loc Addr

/-- The main decoder's ModRM parser: `(mod, reg, ext, r/m, rest, bytes)`. -/
abbrev MRM := List Nat → Option (Nat × Nat × Nat × XLoc × List Nat × Nat)

/-- The decoded EVEX fields and ModRM operand. -/
structure Ctx where
  /-- `EVEX.W`. -/
  w : Bool
  /-- `vvvv` with `V'` (un-inverted, 0..31). -/
  v : Nat
  z : Bool
  /-- `EVEX.L'L`. -/
  ll : Nat
  /-- `EVEX.b`. -/
  b : Bool
  /-- `EVEX.aaa`. -/
  k : Nat
  /-- `ModRM.mod`. -/
  md : Nat
  /-- `ModRM.reg` with `R` and `R'` (0..31). -/
  reg : Nat
  /-- The raw `ModRM.reg` field. -/
  ext : Nat
  /-- `EVEX.R` or `EVEX.R'` set (a 4th/5th register bit in `ModRM.reg`). -/
  regHi : Bool
  /-- `EVEX.X` (un-inverted). -/
  xx : Nat
  /-- The `r/m` operand (register with `B` and `X`; memory with the unscaled displacement). -/
  rm : XLoc
  /-- Bytes after ModRM/SIB/displacement. -/
  rest : List Nat
  /-- Instruction length up to and including the ModRM operand. -/
  n : Nat

def fin (i : I) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (.evex i, len)

/-- `disp8 * N`: the compressed displacement of a `mod = 01` memory operand. -/
def scaleX (md N : Nat) : XLoc → XLoc
  | .mem a => if md = 1 then .mem { a with disp := a.disp * N % 2 ^ 64 } else .mem a
  | x => x

/-- The vector length of an instruction without embedded rounding: `128 · 2^L'L`; `none` for
`L'L = 11` or `EVEX.b` with a register operand. -/
def vl (c : Ctx) : Option Nat :=
  if c.ll = 3 then none else
  match c.rm with
  | .xmm _ => if c.b then none else some (128 * 2 ^ c.ll)
  | .mem _ => some (128 * 2 ^ c.ll)

/-- A full-vector `r/m` source of `l` bits (tuple `FV` with broadcast width `bcw`, or `FVM` for
`bcw = 0`): the operand with its scaled displacement and the broadcast width (0 = none). -/
def src (c : Ctx) (l bcw : Nat) : Option (XLoc × Nat) :=
  match c.rm with
  | .xmm r => some (.xmm r, 0)
  | .mem a =>
    if c.b then (if bcw = 0 then none else some (scaleX c.md (bcw / 8) (.mem a), bcw))
    else some (scaleX c.md (l / 8) (.mem a), 0)

/-- `{z}` needs a mask register. -/
def zOK (c : Ctx) : Bool := !(c.z && c.k == 0)

/-- No write mask at all. -/
def noMask (c : Ctx) : Bool := c.k == 0 && !c.z

/-- The first byte after the operand: `imm8`. -/
def imm (c : Ctx) : Option Nat :=
  match c.rest with
  | i :: _ => some i
  | [] => none

/-- `dst ← op(dst, vvvv, r/m)`, masked at `e` bits (`bcw`: broadcast width, 0 = none; `nds`:
whether `vvvv` is an operand; `msk`: whether a write mask is allowed). -/
def vop (c : Ctx) (o : EOp) (e bcw : Nat) (nds msk : Bool) (len : Nat) : Option (Instr × Nat) :=
  match vl c with
  | none => none
  | some l =>
    if !zOK c || (!nds && c.v != 0) || (!msk && !noMask c) then none else
    match src c l bcw with
    | some (s, bc) => fin (.op o e l c.reg c.v s bc c.k c.z) len
    | none => none

/-- `vop` with an `imm8` (`o` built from it). -/
def vopI (c : Ctx) (o : Nat → EOp) (e bcw : Nat) (nds msk : Bool) : Option (Instr × Nat) :=
  match imm c with
  | some i => vop c (o i) e bcw nds msk (c.n + 1)
  | none => none

/-- The shifts by an `xmm/m128` count (`M128`: `disp8 × 16`, no broadcast). -/
def vcount (c : Ctx) (o : EOp) (e : Nat) : Option (Instr × Nat) :=
  match vl c with
  | none => none
  | some l =>
    if !zOK c || c.b then none else
    fin (.op o e l c.reg c.v (scaleX c.md 16 c.rm) 0 c.k c.z) c.n

/-- A compare into the mask register `ModRM.reg` (`K[aaa]` the write mask, no `{z}`). -/
def vcmp (c : Ctx) (cm : ECmp) (e bcw : Nat) (len : Nat) : Option (Instr × Nat) :=
  match vl c with
  | none => none
  | some l =>
    if c.z || c.regHi then none else
    match src c l bcw with
    | some (s, bc) => fin (.cmp cm e l c.ext c.v s bc c.k) len
    | none => none

/-- `dst(vvvv) ← op(r/m, imm8)`: the immediate shift and rotate groups `71`/`72`/`73`. -/
def vgrp (c : Ctx) (o : EUOp) (e bcw : Nat) (msk : Bool) : Option (Instr × Nat) :=
  match vl c, imm c with
  | some l, some i =>
    if !zOK c || (!msk && !noMask c) then none else
    match src c l bcw with
    | some (s, bc) => fin (.uop o e l c.v s bc i c.k c.z) (c.n + 1)
    | none => none
  | _, _ => none

/-- `dst(reg) ← op(r/m, imm8)` (`VPSHUFD`, `VPERMQ ..., imm8`). -/
def vuop (c : Ctx) (o : EUOp) (e bcw : Nat) : Option (Instr × Nat) :=
  match vl c, imm c with
  | some l, some i =>
    if !zOK c || c.v != 0 then none else
    match src c l bcw with
    | some (s, bc) => fin (.uop o e l c.reg s bc i c.k c.z) (c.n + 1)
    | none => none
  | _, _ => none

/-- The vector moves: load/register form (`toReg`, `dst = reg`) or store form (`dst = r/m`). -/
def vmov (c : Ctx) (e : Nat) (al toReg : Bool) : Option (Instr × Nat) :=
  match vl c with
  | none => none
  | some l =>
    if !zOK c || c.v != 0 || c.b then none else
    let rm := scaleX c.md (l / 8) c.rm
    if toReg then fin (.mov e l al (.xmm c.reg) rm c.k c.z) c.n
    else
      match rm with
      | .mem _ => if c.z then none else fin (.mov e l al rm (.xmm c.reg) c.k c.z) c.n
      | .xmm _ => fin (.mov e l al rm (.xmm c.reg) c.k c.z) c.n

/-- Packed floating point (`VADDPS`...): `{er}` (`er`) or `{sae}` with a register operand and
`EVEX.b`; `nds = false` for `VSQRTPS/PD`. -/
def vfp (c : Ctx) (op : PFOp) (wd : Nat) (er nds : Bool) : Option (Instr × Nat) :=
  if !zOK c || (!nds && c.v != 0) then none else
  match c.rm with
  | .xmm r =>
    if c.b then fin (.fp op wd 512 c.reg c.v (.xmm r) 0 (if er then c.ll + 1 else 5) c.k c.z) c.n
    else if c.ll = 3 then none
    else fin (.fp op wd (128 * 2 ^ c.ll) c.reg c.v (.xmm r) 0 0 c.k c.z) c.n
  | .mem _ =>
    if c.ll = 3 then none else
    let l := 128 * 2 ^ c.ll
    match src c l wd with
    | some (s, bc) => fin (.fp op wd l c.reg c.v s bc 0 c.k c.z) c.n
    | none => none

/-- `VCMPPS/PD k, vvvv, r/m, imm8` (`{sae}` with a register operand and `EVEX.b`). -/
def vfcmp (c : Ctx) (wd : Nat) : Option (Instr × Nat) :=
  match imm c with
  | none => none
  | some i =>
    if c.z || c.regHi then none else
    match c.rm with
    | .xmm r =>
      if c.b then fin (.cmp (.fp i true) wd 512 c.ext c.v (.xmm r) 0 c.k) (c.n + 1)
      else if c.ll = 3 then none
      else fin (.cmp (.fp i false) wd (128 * 2 ^ c.ll) c.ext c.v (.xmm r) 0 c.k) (c.n + 1)
    | .mem _ =>
      if c.ll = 3 then none else
      let l := 128 * 2 ^ c.ll
      match src c l wd with
      | some (s, bc) => fin (.cmp (.fp i false) wd l c.ext c.v s bc c.k) (c.n + 1)
      | none => none

/-- The packed integer operation of an EVEX `66 0F xx` opcode: `(op, mask width, broadcast width,
required W)` (`W` = `none`: `WIG`). The shifts by a count are separate (`vcount`). -/
def pint1 (op : Nat) : Option (PIntOp × Nat × Nat × Option Bool) :=
  if op = 0xFC then some (.add 8, 8, 0, none)
  else if op = 0xFD then some (.add 16, 16, 0, none)
  else if op = 0xFE then some (.add 32, 32, 32, some false)
  else if op = 0xD4 then some (.add 64, 64, 64, some true)
  else if op = 0xF8 then some (.sub 8, 8, 0, none)
  else if op = 0xF9 then some (.sub 16, 16, 0, none)
  else if op = 0xFA then some (.sub 32, 32, 32, some false)
  else if op = 0xFB then some (.sub 64, 64, 64, some true)
  else if op = 0xEC then some (.adds 8, 8, 0, none)
  else if op = 0xED then some (.adds 16, 16, 0, none)
  else if op = 0xDC then some (.addus 8, 8, 0, none)
  else if op = 0xDD then some (.addus 16, 16, 0, none)
  else if op = 0xE8 then some (.subs 8, 8, 0, none)
  else if op = 0xE9 then some (.subs 16, 16, 0, none)
  else if op = 0xD8 then some (.subus 8, 8, 0, none)
  else if op = 0xD9 then some (.subus 16, 16, 0, none)
  else if op = 0xE0 then some (.avg 8, 8, 0, none)
  else if op = 0xE3 then some (.avg 16, 16, 0, none)
  else if op = 0xD5 then some (.mull 16, 16, 0, none)
  else if op = 0xE5 then some (.mulh false, 16, 0, none)
  else if op = 0xE4 then some (.mulh true, 16, 0, none)
  else if op = 0xF4 then some (.muldq false, 64, 64, some true)
  else if op = 0xF5 then some (.maddwd, 32, 0, none)
  else if op = 0xDA then some (.minu 8, 8, 0, none)
  else if op = 0xDE then some (.maxu 8, 8, 0, none)
  else if op = 0xEA then some (.mins 16, 16, 0, none)
  else if op = 0xEE then some (.maxs 16, 16, 0, none)
  else if op = 0x60 then some (.unpckl 8, 8, 0, none)
  else if op = 0x61 then some (.unpckl 16, 16, 0, none)
  else if op = 0x62 then some (.unpckl 32, 32, 32, some false)
  else if op = 0x6C then some (.unpckl 64, 64, 64, some true)
  else if op = 0x68 then some (.unpckh 8, 8, 0, none)
  else if op = 0x69 then some (.unpckh 16, 16, 0, none)
  else if op = 0x6A then some (.unpckh 32, 32, 32, some false)
  else if op = 0x6D then some (.unpckh 64, 64, 64, some true)
  else if op = 0x63 then some (.packss 16, 8, 0, none)
  else if op = 0x6B then some (.packss 32, 16, 32, some false)
  else if op = 0x67 then some (.packus 16, 8, 0, none)
  else none

/-- The packed integer operation of an EVEX `66 0F38 xx` opcode (`W` selecting `D`/`Q` where the
SDM has both; `VPABS*` have no `vvvv` operand). -/
def pint2 (op : Nat) (w : Bool) : Option (PIntOp × Nat × Nat × Option Bool) :=
  let e := if w then 64 else 32
  if op = 0x04 then some (.maddubsw, 16, 0, none)
  else if op = 0x0B then some (.mulhrsw, 16, 0, none)
  else if op = 0x1C then some (.abs 8, 8, 0, none)
  else if op = 0x1D then some (.abs 16, 16, 0, none)
  else if op = 0x1E then some (.abs 32, 32, 32, some false)
  else if op = 0x1F then some (.abs 64, 64, 64, some true)
  else if op = 0x28 then some (.muldq true, 64, 64, some true)
  else if op = 0x2B then some (.packus 32, 16, 32, some false)
  else if op = 0x38 then some (.mins 8, 8, 0, none)
  else if op = 0x39 then some (.mins e, e, e, some w)
  else if op = 0x3A then some (.minu 16, 16, 0, none)
  else if op = 0x3B then some (.minu e, e, e, some w)
  else if op = 0x3C then some (.maxs 8, 8, 0, none)
  else if op = 0x3D then some (.maxs e, e, e, some w)
  else if op = 0x3E then some (.maxu 16, 16, 0, none)
  else if op = 0x3F then some (.maxu e, e, e, some w)
  else if op = 0x40 then some (.mull e, e, e, some w)
  else none

/-- Decode the EVEX instruction of map `mp`, implied prefix `pp`, opcode `op`. -/
def decodeOp (c : Ctx) (mp pp op : Nat) : Option (Instr × Nat) :=
  let ed : Nat := if c.w then 64 else 32
  let wOK (r : Option Bool) : Bool := match r with | none => true | some x => x == c.w
  let isMem : Bool := match c.rm with | .mem _ => true | .xmm _ => false
  if mp = 1 then
    if pp = 0 ∨ pp = 1 then
      -- the PS (no prefix, W0) and PD (66, W1) forms
      let fpw : Nat := if pp = 0 then 32 else 64
      let fpW : Bool := (pp = 0 && !c.w) || (pp = 1 && c.w)
      if op = 0x10 ∨ op = 0x11 then (if fpW then vmov c fpw false (op = 0x10) else none)
      else if op = 0x28 ∨ op = 0x29 then (if fpW then vmov c fpw true (op = 0x28) else none)
      else if op = 0x51 then (if fpW then vfp c .sqrt fpw true false else none)
      else if op = 0x58 then (if fpW then vfp c .add fpw true true else none)
      else if op = 0x59 then (if fpW then vfp c .mul fpw true true else none)
      else if op = 0x5C then (if fpW then vfp c .sub fpw true true else none)
      else if op = 0x5D then (if fpW then vfp c .min fpw false true else none)
      else if op = 0x5E then (if fpW then vfp c .div fpw true true else none)
      else if op = 0x5F then (if fpW then vfp c .max fpw false true else none)
      else if op = 0x54 then (if fpW then vop c (.logic .and) fpw fpw true true c.n else none)
      else if op = 0x55 then (if fpW then vop c (.logic .andn) fpw fpw true true c.n else none)
      else if op = 0x56 then (if fpW then vop c (.logic .or) fpw fpw true true c.n else none)
      else if op = 0x57 then (if fpW then vop c (.logic .xor) fpw fpw true true c.n else none)
      else if op = 0xC2 then (if fpW then vfcmp c fpw else none)
      else if pp = 0 then none
      -- 66 0F
      else if op = 0x6F ∨ op = 0x7F then vmov c ed true (op = 0x6F)
      else if op = 0xDB then vop c (.logic .and) ed ed true true c.n
      else if op = 0xDF then vop c (.logic .andn) ed ed true true c.n
      else if op = 0xEB then vop c (.logic .or) ed ed true true c.n
      else if op = 0xEF then vop c (.logic .xor) ed ed true true c.n
      else if op = 0x74 then vcmp c (.int false 0) 8 0 c.n
      else if op = 0x75 then vcmp c (.int false 0) 16 0 c.n
      else if op = 0x76 then (if c.w then none else vcmp c (.int false 0) 32 32 c.n)
      else if op = 0x64 then vcmp c (.int true 6) 8 0 c.n
      else if op = 0x65 then vcmp c (.int true 6) 16 0 c.n
      else if op = 0x66 then (if c.w then none else vcmp c (.int true 6) 32 32 c.n)
      else if op = 0xF6 then vop c (.pint .sadbw) 64 0 true false c.n
      else if op = 0xD1 then vcount c (.pint (.srl 16)) 16
      else if op = 0xD2 then (if c.w then none else vcount c (.pint (.srl 32)) 32)
      else if op = 0xD3 then (if c.w then vcount c (.pint (.srl 64)) 64 else none)
      else if op = 0xE1 then vcount c (.pint (.sra 16)) 16
      else if op = 0xE2 then vcount c (.pint (.sra ed)) ed
      else if op = 0xF1 then vcount c (.pint (.sll 16)) 16
      else if op = 0xF2 then (if c.w then none else vcount c (.pint (.sll 32)) 32)
      else if op = 0xF3 then (if c.w then vcount c (.pint (.sll 64)) 64 else none)
      else if op = 0x70 then (if c.w then none else vuop c (.shuf .pshufd) 32 32)
      else if op = 0x71 then
        -- VPSRLW /2, VPSRAW /4, VPSLLW /6 (WIG, FVM)
        if c.ext = 2 then vgrp c (.shift .srl) 16 0 true
        else if c.ext = 4 then vgrp c (.shift .sra) 16 0 true
        else if c.ext = 6 then vgrp c (.shift .sll) 16 0 true
        else none
      else if op = 0x72 then
        -- VPRORD/Q /0, VPROLD/Q /1, VPSRLD /2 (W0), VPSRAD/Q /4, VPSLLD /6 (W0)
        if c.ext = 0 then vgrp c (.rot false) ed ed true
        else if c.ext = 1 then vgrp c (.rot true) ed ed true
        else if c.ext = 2 then (if c.w then none else vgrp c (.shift .srl) 32 32 true)
        else if c.ext = 4 then vgrp c (.shift .sra) ed ed true
        else if c.ext = 6 then (if c.w then none else vgrp c (.shift .sll) 32 32 true)
        else none
      else if op = 0x73 then
        -- VPSRLQ /2 (W1), VPSRLDQ /3 (no mask), VPSLLQ /6 (W1), VPSLLDQ /7 (no mask)
        if c.ext = 2 then (if c.w then vgrp c (.shift .srl) 64 64 true else none)
        else if c.ext = 3 then vgrp c (.shift .srldq) 128 0 false
        else if c.ext = 6 then (if c.w then vgrp c (.shift .sll) 64 64 true else none)
        else if c.ext = 7 then vgrp c (.shift .slldq) 128 0 false
        else none
      else
        match pint1 op with
        | some (o, e, bcw, wr) => if wOK wr then vop c (.pint o) e bcw true true c.n else none
        | none => none
    else if pp = 2 then
      -- F3 0F: VMOVDQU32/64, VPSHUFHW
      if op = 0x6F ∨ op = 0x7F then vmov c ed false (op = 0x6F)
      else if op = 0x70 then vuop c (.shuf .pshufhw) 16 0
      else none
    else
      -- F2 0F: VMOVDQU8/16, VPSHUFLW
      if op = 0x6F ∨ op = 0x7F then vmov c (if c.w then 16 else 8) false (op = 0x6F)
      else if op = 0x70 then vuop c (.shuf .pshuflw) 16 0
      else none
  else if mp = 2 then
    if pp = 2 then
      -- F3 0F38: VPTESTNMB/W (26), VPTESTNMD/Q (27)
      if op = 0x26 then vcmp c (.test true) (if c.w then 16 else 8) 0 c.n
      else if op = 0x27 then vcmp c (.test true) ed ed c.n
      else none
    else if pp ≠ 1 then none
    else if op = 0x00 then vop c .shufb 8 0 true true c.n
    else if op = 0x1C ∨ op = 0x1D ∨ op = 0x1E ∨ op = 0x1F then
      match pint2 op c.w with
      | some (o, e, bcw, wr) => if wOK wr then vop c (.pint o) e bcw false true c.n else none
      | none => none
    else if op = 0x10 then (if c.w then vop c (.shiftv .srl) 16 0 true true c.n else none)
    else if op = 0x11 then (if c.w then vop c (.shiftv .sra) 16 0 true true c.n else none)
    else if op = 0x12 then (if c.w then vop c (.shiftv .sll) 16 0 true true c.n else none)
    else if op = 0x45 then vop c (.shiftv .srl) ed ed true true c.n
    else if op = 0x46 then vop c (.shiftv .sra) ed ed true true c.n
    else if op = 0x47 then vop c (.shiftv .sll) ed ed true true c.n
    else if op = 0x14 then vop c (.rotv false) ed ed true true c.n
    else if op = 0x15 then vop c (.rotv true) ed ed true true c.n
    else if op = 0x26 then vcmp c (.test false) (if c.w then 16 else 8) 0 c.n
    else if op = 0x27 then vcmp c (.test false) ed ed c.n
    else if op = 0x29 then (if c.w then vcmp c (.int false 0) 64 64 c.n else none)
    else if op = 0x37 then (if c.w then vcmp c (.int true 6) 64 64 c.n else none)
    else if op = 0x16 ∨ op = 0x36 then
      -- VPERMPS/PD, VPERMD/Q (L ≠ 128)
      if c.ll = 0 then none else vop c .perm ed ed true true c.n
    else if op = 0x8D then vop c .perm (if c.w then 16 else 8) 0 true true c.n
    else if op = 0x75 then vop c .permi2 (if c.w then 16 else 8) 0 true true c.n
    else if op = 0x76 ∨ op = 0x77 then vop c .permi2 ed ed true true c.n
    else if op = 0x7D then vop c .permt2 (if c.w then 16 else 8) 0 true true c.n
    else if op = 0x7E ∨ op = 0x7F then vop c .permt2 ed ed true true c.n
    else if op = 0x54 then vop c .popcnt (if c.w then 16 else 8) 0 false true c.n
    else if op = 0x55 then vop c .popcnt ed ed false true c.n
    else if op = 0xCF then (if c.w then none else vop c .gfmul 8 0 true true c.n)
    else if op = 0x64 ∨ op = 0x65 ∨ op = 0x66 then
      -- VPBLENDMD/Q (64), VBLENDMPS/PD (65), VPBLENDMB/W (66)
      let e := if op = 0x66 then (if c.w then 16 else 8) else ed
      match vl c with
      | none => none
      | some l =>
        if !zOK c then none else
        match src c l (if op = 0x66 then 0 else e) with
        | some (s, bc) => fin (.blendm e l c.reg c.v s bc c.k c.z) c.n
        | none => none
    else if op = 0x62 ∨ op = 0x63 ∨ op = 0x89 ∨ op = 0x8B then
      -- VPEXPANDB/W (62), VPCOMPRESSB/W (63), VPEXPANDD/Q (89), VPCOMPRESSD/Q (8B): T1S
      let e := if op = 0x62 ∨ op = 0x63 then (if c.w then 16 else 8) else ed
      match vl c with
      | none => none
      | some l =>
        if !zOK c || c.v != 0 || c.b then none else
        let rm := scaleX c.md (e / 8) c.rm
        if op = 0x62 ∨ op = 0x89 then fin (.expand e l c.reg rm c.k c.z) c.n
        else if isMem && c.z then none
        else fin (.compress e l rm c.reg c.k c.z) c.n
    else if op = 0x18 ∨ op = 0x19 ∨ op = 0x58 ∨ op = 0x59 ∨ op = 0x78 ∨ op = 0x79 then
      -- VBROADCASTSS (W0), VBROADCASTSD (W1, L ≠ 128), VPBROADCASTD (W0), VPBROADCASTQ (W1),
      -- VPBROADCASTB/W (W0): T1S
      let e : Nat := if op = 0x18 ∨ op = 0x58 then 32 else if op = 0x78 then 8 else if op = 0x79 then 16 else 64
      let needW : Bool := op = 0x19 ∨ op = 0x59
      if (op = 0x19 ∨ op = 0x59) && !c.w then
        -- VBROADCASTF32X2 (L ≠ 128) / VBROADCASTI32X2 (W0): the low 64 bits, masked at 32 (T2)
        if op = 0x19 && c.ll = 0 then none else
        match vl c with
        | none => none
        | some l =>
          if !zOK c || c.v != 0 || c.b then none else
          fin (.bcast 32 64 l c.reg (scaleX c.md 8 c.rm) c.k c.z) c.n
      else
      if c.w != needW || (op = 0x19 && c.ll = 0) then none else
      match vl c with
      | none => none
      | some l =>
        if !zOK c || c.v != 0 || c.b then none else
        fin (.bcast e e l c.reg (scaleX c.md (e / 8) c.rm) c.k c.z) c.n
    else if op = 0x1A ∨ op = 0x1B ∨ op = 0x5A ∨ op = 0x5B then
      -- VBROADCASTF/I32X4 (W0) / 64X2 (W1) (L ≠ 128), F/I32X8 (W0) / 64X4 (W1) (L = 512): memory only
      let cb : Nat := if op = 0x1A ∨ op = 0x5A then 128 else 256
      match vl c with
      | none => none
      | some l =>
        if !zOK c || c.v != 0 || c.b || !isMem || l ≤ cb then none else
        fin (.bcast ed cb l c.reg (scaleX c.md (cb / 8) c.rm) c.k c.z) c.n
    else if op = 0x7A ∨ op = 0x7B ∨ op = 0x7C then
      -- VPBROADCASTB/W/D r32 (W0), VPBROADCASTQ r64 (W1): register only
      let e : Nat := if op = 0x7A then 8 else if op = 0x7B then 16 else ed
      if (op ≠ 0x7C && c.w) then none else
      match vl c, c.rm with
      | some l, .xmm r =>
        if !zOK c || c.v != 0 || c.xx != 0 then none else fin (.bcastG e l c.reg r c.k c.z) c.n
      | _, _ => none
    else if (0x20 ≤ op ∧ op ≤ 0x25) ∨ (0x30 ≤ op ∧ op ≤ 0x35) then
      -- VPMOVSX / VPMOVZX (VPMOVSXDQ/ZXDQ W0)
      let q := op % 16
      let ft : Nat × Nat := if q = 0 then (8, 16) else if q = 1 then (8, 32)
        else if q = 2 then (8, 64) else if q = 3 then (16, 32) else if q = 4 then (16, 64)
        else (32, 64)
      if q = 5 && c.w then none else
      match vl c with
      | none => none
      | some l =>
        if !zOK c || c.v != 0 || c.b then none else
        fin (.pmovx (op < 0x30) ft.1 ft.2 l c.reg (scaleX c.md (l * ft.1 / ft.2 / 8) c.rm) c.k c.z) c.n
    else
      match pint2 op c.w with
      | some (o, e, bcw, wr) => if wOK wr then vop c (.pint o) e bcw true true c.n else none
      | none => none
  else if mp = 3 then
    if pp ≠ 1 then none
    else if op = 0x00 ∨ op = 0x01 then
      -- VPERMQ / VPERMPD ..., imm8 (W1, L ≠ 128)
      if !c.w || c.ll = 0 then none else vuop c .permq 64 64
    else if op = 0x03 then vopI c .align ed ed true true
    else if op = 0x0F then vopI c .alignr 8 0 true true
    else if op = 0x25 then vopI c .ternlog ed ed true true
    else if op = 0x23 ∨ op = 0x43 then
      if c.ll = 0 then none else vopI c .shuf128 ed ed true true
    else if op = 0x44 then vopI c .clmul 64 0 true false
    else if op = 0xCE then (if c.w then vopI c (.gfaffine false) 8 64 true true else none)
    else if op = 0xCF then (if c.w then vopI c (.gfaffine true) 8 64 true true else none)
    else if op = 0x1E ∨ op = 0x1F then
      match imm c with
      | some i => vcmp c (.int (op = 0x1F) i) ed ed (c.n + 1)
      | none => none
    else if op = 0x3E ∨ op = 0x3F then
      match imm c with
      | some i => vcmp c (.int (op = 0x3F) i) (if c.w then 16 else 8) 0 (c.n + 1)
      | none => none
    else if op = 0x18 ∨ op = 0x1A ∨ op = 0x38 ∨ op = 0x3A then
      -- VINSERTF/I32X4, 64X2 (L ≠ 128); VINSERTF/I32X8, 64X4 (L = 512)
      let cb : Nat := if op = 0x18 ∨ op = 0x38 then 128 else 256
      match vl c, imm c with
      | some l, some i =>
        if !zOK c || c.b || l ≤ cb then none else
        fin (.insert ed l cb c.reg c.v (scaleX c.md (cb / 8) c.rm) i c.k c.z) (c.n + 1)
      | _, _ => none
    else if op = 0x19 ∨ op = 0x1B ∨ op = 0x39 ∨ op = 0x3B then
      -- VEXTRACTF/I32X4, 64X2 (L ≠ 128); VEXTRACTF/I32X8, 64X4 (L = 512)
      let cb : Nat := if op = 0x19 ∨ op = 0x39 then 128 else 256
      match vl c, imm c with
      | some l, some i =>
        if !zOK c || c.b || c.v != 0 || l ≤ cb || (isMem && c.z) then none else
        fin (.extract ed l cb (scaleX c.md (cb / 8) c.rm) c.reg i c.k c.z) (c.n + 1)
      | _, _ => none
    else none
  else none

/-- Decode an EVEX instruction: `bs` are the bytes after the `62`. -/
def evex (modrmOf : Nat → MRM) : List Nat → Option (Instr × Nat)
  | p0 :: p1 :: p2 :: op :: rest =>
    if p0 / 8 % 2 = 1 ∨ p1 / 4 % 2 = 0 then none else
    let mp := p0 % 8
    if mp = 0 ∨ mp > 3 then none else
    let rr := 1 - p0 / 128
    let xx := 1 - p0 / 64 % 2
    let bb := 1 - p0 / 32 % 2
    let r' := 1 - p0 / 16 % 2
    let w := p1 / 128
    match modrmOf (8 * w + 4 * rr + 2 * xx + bb) rest with
    | none => none
    | some (md, reg0, ext, rm0, rest', cnt) =>
      let rm : XLoc := match rm0 with
        | .xmm r => .xmm (r + 16 * xx)
        | .mem a => .mem a
      let c : Ctx :=
        { w := w = 1, v := (15 - p1 / 8 % 16) + 16 * (1 - p2 / 8 % 2), z := p2 / 128 = 1,
          ll := p2 / 32 % 4, b := p2 / 16 % 2 = 1, k := p2 % 8, md := md, reg := reg0 + 16 * r',
          ext := ext, regHi := rr = 1 ∨ r' = 1, xx := xx, rm := rm, rest := rest', n := 5 + cnt }
      decodeOp c mp (p1 % 4) op
  | _ => none

/-! ## The VEX-encoded AVX-512 opmask instructions, `VPCLMULQDQ` and GFNI -/

/-- The opmask width of a VEX `0F` mask instruction from `pp`/`W`: `66 W0` = B, none `W0` = W,
`66 W1` = D, none `W1` = Q. -/
def kw (pp : Nat) (w1 : Bool) : Option Nat :=
  if pp = 1 then some (if w1 then 32 else 8)
  else if pp = 0 then some (if w1 then 64 else 16)
  else none

/-- Decode a VEX instruction of WP-G with the fields of the prefix (`rex = W R X B` un-inverted,
`v` the un-inverted `VEX.vvvv`, `l` 128/256, `pp`, map `mp`, opcode `op`, the bytes `bs` after it,
`n` the bytes before it). -/
def vexOp (modrmOf : Nat → MRM) (rex v l pp mp op : Nat) (bs : List Nat) (n : Nat) :
    Option (Instr × Nat) :=
  let w1 := rex / 8 = 1
  let rR := rex / 4 % 2
  let fin' (i : I) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (.evex i, len)
  match modrmOf rex bs with
  | none => none
  | some (_, reg, ext, rm, rest, cnt) =>
    let len := n + 1 + cnt
    let i8 : Option Nat := match rest with | i :: _ => some i | [] => none
    -- a mask register in `r/m` (register form only, `VEX.B` clear)
    let kr : Option Nat := match rm with | .xmm r => some (r % 8) | .mem _ => none
    if mp = 1 then
      if op = 0x90 ∨ op = 0x91 then
        -- KMOV k, k/m (90) and KMOV m, k (91): VEX.L0, vvvv = 1111
        match kw pp w1 with
        | none => none
        | some w =>
          if l ≠ 128 ∨ v ≠ 0 ∨ rR = 1 then none else
          if op = 0x90 then
            match rm with
            | .xmm r => fin' (.kmov w (.k ext) (.k (r % 8))) len
            | .mem a => fin' (.kmov w (.k ext) (.mem a)) len
          else
            match rm with
            | .mem a => fin' (.kmov w (.mem a) (.k ext)) len
            | .xmm _ => none
      else if op = 0x92 ∨ op = 0x93 then
        -- KMOV k, r32/r64 (92) and KMOV r32/r64, k (93): 66 W0 = B, none W0 = W, F2 W0 = D,
        -- F2 W1 = Q; register only
        let w : Option Nat :=
          if pp = 1 ∧ ¬ w1 then some 8 else if pp = 0 ∧ ¬ w1 then some 16
          else if pp = 3 then some (if w1 then 64 else 32) else none
        match w, rm with
        | some w, .xmm r =>
          if l ≠ 128 ∨ v ≠ 0 then none
          else if op = 0x92 then (if rR = 1 then none else fin' (.kmov w (.k ext) (.gpr r)) len)
          else fin' (.kmov w (.gpr reg) (.k (r % 8))) len
        | _, _ => none
      else if op = 0x41 ∨ op = 0x42 ∨ op = 0x45 ∨ op = 0x46 ∨ op = 0x47 ∨ op = 0x4A then
        -- KAND, KANDN, KOR, KXNOR, KXOR, KADD kd, k1 (vvvv), k2 (r/m): VEX.L1
        let o : KOp := if op = 0x41 then .and else if op = 0x42 then .andn else if op = 0x45 then .or
          else if op = 0x46 then .xnor else if op = 0x47 then .xor else .add
        match kw pp w1, kr with
        | some w, some r => if l ≠ 256 ∨ v ≥ 8 ∨ rR = 1 then none else fin' (.klogic o w ext v r) len
        | _, _ => none
      else if op = 0x44 then
        -- KNOT kd, ks: VEX.L0, vvvv = 1111
        match kw pp w1, kr with
        | some w, some r => if l ≠ 128 ∨ v ≠ 0 ∨ rR = 1 then none else fin' (.knot w ext r) len
        | _, _ => none
      else if op = 0x4B then
        -- KUNPCKBW (66 W0), KUNPCKWD (none W0), KUNPCKDQ (none W1): VEX.L1
        let w : Option Nat := if pp = 1 ∧ ¬ w1 then some 8 else if pp = 0 then some (if w1 then 32 else 16) else none
        match w, kr with
        | some w, some r => if l ≠ 256 ∨ v ≥ 8 ∨ rR = 1 then none else fin' (.kunpck w ext v r) len
        | _, _ => none
      else if op = 0x98 ∨ op = 0x99 then
        -- KORTEST (98), KTEST (99) k1 (reg), k2 (r/m): VEX.L0, vvvv = 1111
        match kw pp w1, kr with
        | some w, some r =>
          if l ≠ 128 ∨ v ≠ 0 ∨ rR = 1 then none
          else if op = 0x98 then fin' (.kortest w ext r) len else fin' (.ktest w ext r) len
        | _, _ => none
      else none
    else if mp = 3 ∧ pp = 1 then
      if 0x30 ≤ op ∧ op ≤ 0x33 then
        -- KSHIFTRB/W (30 W0/W1), KSHIFTRD/Q (31), KSHIFTLB/W (32), KSHIFTLD/Q (33): VEX.L0
        let w : Nat := if op % 2 = 0 then (if w1 then 16 else 8) else (if w1 then 64 else 32)
        match kr, i8 with
        | some r, some i =>
          if l ≠ 128 ∨ v ≠ 0 ∨ rR = 1 then none else fin' (.kshift (op ≥ 0x32) w ext r i) (len + 1)
        | _, _ => none
      else if op = 0x44 ∨ op = 0xCE ∨ op = 0xCF then
        -- VPCLMULQDQ (WIG), VGF2P8AFFINEQB / VGF2P8AFFINEINVQB (W1) xmm/ymm, vvvv, r/m, imm8
        match i8 with
        | none => none
        | some i =>
          if op ≠ 0x44 ∧ ¬ w1 then none else
          let o : EOp := if op = 0x44 then .clmul i else .gfaffine (op = 0xCF) i
          fin' (.op o (if op = 0x44 then 64 else 8) l reg v rm 0 0 false) (len + 1)
      else none
    else if mp = 2 ∧ pp = 1 ∧ op = 0xCF then
      -- VGF2P8MULB (W0)
      if w1 then none else fin' (.op .gfmul 8 l reg v rm 0 0 false) len
    else none

/-- Decode a VEX instruction of WP-G at the start of `bytes` (no prefix before it): `b0 = C5` or
`C4`, `bs` the bytes after it. -/
def vex (modrmOf : Nat → MRM) (b0 : Nat) (bs : List Nat) : Option (Instr × Nat) :=
  if b0 = 0xC5 then
    match bs with
    | b1 :: op :: rest =>
      let r := 1 - b1 / 128
      vexOp modrmOf (4 * r) (15 - (b1 / 8) % 16) (if (b1 / 4) % 2 = 1 then 256 else 128) (b1 % 4) 1 op rest 2
    | _ => none
  else if b0 = 0xC4 then
    match bs with
    | b1 :: b2 :: op :: rest =>
      let rex := 8 * (b2 / 128) + 4 * (1 - b1 / 128) + 2 * (1 - (b1 / 64) % 2) + (1 - (b1 / 32) % 2)
      vexOp modrmOf rex (15 - (b2 / 8) % 16) (if (b2 / 4) % 2 = 1 then 256 else 128) (b2 % 4) (b1 % 32) op rest 3
    | _ => none
  else none

end Janus.Amd64.DecodeEVEX

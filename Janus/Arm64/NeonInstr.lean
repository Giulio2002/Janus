/-!
# Advanced SIMD (NEON) instruction classes beyond `Instr`'s original subset

`Instr.neon` (see `Janus.Arm64.Instr`) carries one value of this type. As in `Instr`, there is one
constructor per *encoding class* of the A64 "Data Processing -- Scalar Floating-Point and
Advanced SIMD" and "Loads and Stores" tables (ARM ARM C4.1.95, C4.1.88), with the raw encoding
fields and no interpretation: the operation an encoding selects is computed in
`Janus.Arm64.Neon` / `Janus.Arm64.NeonFP`, and `Janus.Arm64.decodeNeon` (`DecodeNeon.lean`)
only produces values that are valid, allocated encodings of the supported subset.

`decodeNeon` is consulted only for words the original decoder rejects (`Janus.Arm64.decodeAll` falls back to it when `decode` fails),
so a class here may also contain opcodes that `Instr` already covers (vector `ADD`, `CMEQ`, ...);
`execNeon` implements every opcode the class accepts, whichever decoder produced it.

Field naming follows the encoding diagrams: `Q` (128-bit vector), `U`, `size` (bits 23:22),
`opcode`, `immh:immb`, `L:M:H` (element index), register numbers `rd`, `rn`, `rm` (SIMD&FP
registers, `0..31`), and for loads and stores `rt`, `rt2` (SIMD&FP) and `rn`/`rm` (general
registers: `rn` is SP for 31, `rm` is the post-index register, 31 meaning "by the transfer
size").
-/

namespace Janus.Arm64

inductive NeonInstr where
  /-- Advanced SIMD three same (vector): `0 Q U 01110 size 1 Rm opcode 1 Rn Rd`. -/
  | threeSame (Q U : Bool) (size rm opcode rn rd : Nat)
  /-- Advanced SIMD scalar three same: `01 U 11110 size 1 Rm opcode 1 Rn Rd`. -/
  | sThreeSame (U : Bool) (size rm opcode rn rd : Nat)
  /-- Advanced SIMD three different (vector): `0 Q U 01110 size 1 Rm opcode 00 Rn Rd`. -/
  | threeDiff (Q U : Bool) (size rm opcode rn rd : Nat)
  /-- Advanced SIMD scalar three different: `01 U 11110 size 1 Rm opcode 00 Rn Rd`. -/
  | sThreeDiff (U : Bool) (size rm opcode rn rd : Nat)
  /-- Advanced SIMD two-register miscellaneous (vector): `0 Q U 01110 size 10000 opcode 10 Rn Rd`. -/
  | twoMisc (Q U : Bool) (size opcode rn rd : Nat)
  /-- Advanced SIMD scalar two-register miscellaneous: `01 U 11110 size 10000 opcode 10 Rn Rd`. -/
  | sTwoMisc (U : Bool) (size opcode rn rd : Nat)
  /-- Advanced SIMD across lanes: `0 Q U 01110 size 11000 opcode 10 Rn Rd`. -/
  | across (Q U : Bool) (size opcode rn rd : Nat)
  /-- Advanced SIMD scalar pairwise: `01 U 11110 size 11000 opcode 10 Rn Rd`. -/
  | sPairwise (U : Bool) (size opcode rn rd : Nat)
  /-- Advanced SIMD permute: `0 Q 001110 size 0 Rm 0 opcode 10 Rn Rd` (UZP1/TRN1/ZIP1/UZP2/TRN2/ZIP2). -/
  | perm (Q : Bool) (size rm opcode rn rd : Nat)
  /-- Advanced SIMD shift by immediate (vector): `0 Q U 011110 immh immb opcode 1 Rn Rd`, `immh ≠ 0`. -/
  | shiftImm (Q U : Bool) (immh immb opcode rn rd : Nat)
  /-- Advanced SIMD scalar shift by immediate: `01 U 111110 immh immb opcode 1 Rn Rd`, `immh ≠ 0`. -/
  | sShiftImm (U : Bool) (immh immb opcode rn rd : Nat)
  /-- Advanced SIMD vector x indexed element: `0 Q U 01111 size L M Rm opcode H 0 Rn Rd`
  (`rm` is the 4-bit `Rm` field; `M` is bit 20). -/
  | byElem (Q U : Bool) (size : Nat) (L M : Bool) (rm opcode : Nat) (H : Bool) (rn rd : Nat)
  /-- Advanced SIMD scalar x indexed element: `01 U 11111 size L M Rm opcode H 0 Rn Rd`. -/
  | sByElem (U : Bool) (size : Nat) (L M : Bool) (rm opcode : Nat) (H : Bool) (rn rd : Nat)
  /-- Advanced SIMD scalar copy, DUP (element): `01 0 11110000 imm5 0 0000 1 Rn Rd`. -/
  | sDup (imm5 rn rd : Nat)
  /-- LD2/LD3/LD4 and ST2/ST3/ST4 (multiple structures, `L` = load): `opcode` 1000 (2 registers),
  0100 (3), 0000 (4); `post`: post-index by `X[m]`, or by the transfer size for `rm = 31`.
  `rn`: SP. -/
  | ldstStruct (Q L : Bool) (opcode size : Nat) (post : Bool) (rm rn rt : Nat)
  /-- LDNP/STNP of S/D/Q registers (`opc` 00/01/10): a pair access without writeback; the
  non-temporal hint has no architectural effect. `rn`: SP. -/
  | ldstNP (opc : Nat) (L : Bool) (imm7 rt2 rn rt : Nat)
  /-- Conversion between floating point and fixed point: SCVTF/UCVTF (`rmode = 00`,
  `opcode = 01u`) and FCVTZS/FCVTZU (`rmode = 11`, `opcode = 00u`) with `fbits = 64 - scale`:
  `sf 0 0 11110 ftype 0 rmode opcode scale Rn Rd`. General register: ZR. -/
  | fpCvtFixed (sf : Bool) (ftype rmode opcode scale rn rd : Nat)
deriving Repr, DecidableEq, Inhabited

end Janus.Arm64

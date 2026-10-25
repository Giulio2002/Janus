/-!
# AArch64 instruction AST: cryptographic extension, CRC32, permutes

The constructors of `CryptoInstr` are the encoding classes decoded by
`Janus.Arm64.decodeCrypto` / `decodeCrc32` (`Janus/Arm64/DecodeCrypto.lean`) and executed by
`Janus.Arm64.execCrypto` (`Janus/Arm64/ExecCrypto.lean`). `Instr.crypto` embeds them in the
main instruction type, so the base decoder and executor each have one dispatch point.

As in `Janus.Arm64.Instr`, every constructor carries the raw encoding fields; the operation
they select is computed in `Janus.Arm64.Crypto`. SIMD&FP register fields are `0..31` (no zero
register or SP among them); the general registers of CRC32 are documented as `ZR`.

The feature each class needs (all optional in Armv8.0; the decoder assumes they are
implemented, like FEAT_AES and FEAT_LSE elsewhere in the model; Go only executes these
instructions behind `internal/cpu` checks): FEAT_SHA1 (`sha3Reg` opcodes 000–011, `sha2Reg`
00000–00001), FEAT_SHA256 (`sha3Reg` 100–110, `sha2Reg` 00010), FEAT_SHA512 (`sha512Reg`
opcodes 00–10, `sha512Su0`), FEAT_SHA3 (`sha512Reg` 11 = RAX1, `sha4Reg`, `xar`), FEAT_PMULL
(`pmull` with `size = 11`), FEAT_CRC32 (`crc32`). `pmull` with `size = 00`, `permute` and
`dupScalar` are base Advanced SIMD.
-/

namespace Janus.Arm64

inductive CryptoInstr where
  /-- Cryptographic three-register SHA (`01011110 00 0 Rm 0 opcode 00 Rn Rd`, `opcode = w<14:12>`):
  SHA1C (000), SHA1P (001), SHA1M (010), SHA1SU0 (011), SHA256H (100), SHA256H2 (101),
  SHA256SU1 (110). -/
  | sha3Reg (opcode rm rn rd : Nat)
  /-- Cryptographic two-register SHA (`01011110 00 10100 opcode 10 Rn Rd`, `opcode = w<16:12>`):
  SHA1H (00000), SHA1SU1 (00001), SHA256SU0 (00010). -/
  | sha2Reg (opcode rn rd : Nat)
  /-- Cryptographic three-register SHA512 (`11001110 011 Rm 1 0 00 opcode Rn Rd`,
  `opcode = w<11:10>`): SHA512H (00), SHA512H2 (01), SHA512SU1 (10), RAX1 (11). -/
  | sha512Reg (opcode rm rn rd : Nat)
  /-- SHA512SU0 (`11001110 11000000 100000 Rn Rd`). -/
  | sha512Su0 (rn rd : Nat)
  /-- Cryptographic four-register (`11001110 0 Op0 Rm 0 Ra Rn Rd`, `Op0 = w<22:21>`):
  EOR3 (00), BCAX (01). -/
  | sha4Reg (op0 rm ra rn rd : Nat)
  /-- XAR (`11001110 100 Rm imm6 Rn Rd`). -/
  | xar (rm imm6 rn rd : Nat)
  /-- PMULL/PMULL2 (`0 Q 0 01110 size 1 Rm 1110 00 Rn Rd`): `size = 00` (8B to 8H) or `11`
  (1D to 1Q); `Q` selects the upper halves (PMULL2). -/
  | pmull (Q : Bool) (size rm rn rd : Nat)
  /-- CRC32B/H/W/X (`C = false`) and CRC32CB/H/W/X (`C = true`):
  `sf 0 0 11010110 Rm 010 C sz Rn Rd`, `size = 8 << sz`. All registers: ZR. -/
  | crc32 (sf : Bool) (rm : Nat) (C : Bool) (sz rn rd : Nat)
  /-- Advanced SIMD permute (`0 Q 001110 size 0 Rm 0 opcode 10 Rn Rd`, `opcode = w<14:12>`):
  UZP1 (001), TRN1 (010), ZIP1 (011), UZP2 (101), TRN2 (110), ZIP2 (111). -/
  | permute (Q : Bool) (size rm opcode rn rd : Nat)
  /-- DUP (element), scalar form, alias MOV (scalar) (`01 0 11110000 imm5 0 0000 1 Rn Rd`). -/
  | dupScalar (imm5 rn rd : Nat)
deriving Repr, DecidableEq, Inhabited

end Janus.Arm64

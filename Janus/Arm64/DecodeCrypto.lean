import Janus.Arm64.InstrCrypto
import Janus.Arm64.Bits

/-!
# A64 decoder: cryptographic extension, CRC32, permutes

Two entry points, each called from one place of `Janus.Arm64.decode`:

* `decodeCrc32 w` from the data-processing (2 source) branch of `decodeDPReg`, for the words
  whose `opcode` field it does not claim (`sf 0 0 11010110 Rm opcode Rn Rd` is matched by the
  caller);
* `decodeCrypto w` from `decodeSimdDP` (`op0 = x111`), for the words none of its Advanced SIMD
  classes claims, before the scalar floating-point classes. Every encoding it accepts is
  disjoint from those of the other `decodeSimdDP` branches and of `decodeFloat` (each class
  below fixes bits those branches require to differ).

The encodings are those of the ARM ARM tables (C4.1.95 "Data Processing -- Scalar Floating-Point
and Advanced SIMD", C4.1.93 "Data-processing (2 source)"), cross-checked against the decode
clauses of the Sail translation of the ASL (sail-arm `f5bf6c3`, `instrs64.sail`). Accepted:

| class | encoding | instructions |
|---|---|---|
| crypto three-register SHA | `01011110 00 0 Rm 0 opc 00 Rn Rd`, `opc ≠ 111` | SHA1C SHA1P SHA1M SHA1SU0 SHA256H SHA256H2 SHA256SU1 |
| crypto two-register SHA | `01011110 00 10100 opc 10 Rn Rd`, `opc ∈ {00000, 00001, 00010}` | SHA1H SHA1SU1 SHA256SU0 |
| crypto three-register SHA512 | `11001110 011 Rm 1 0 00 opc Rn Rd` | SHA512H SHA512H2 SHA512SU1 RAX1 |
| crypto two-register SHA512 | `11001110 11000000 100000 Rn Rd` | SHA512SU0 |
| crypto four-register | `11001110 0 Op0 Rm 0 Ra Rn Rd`, `Op0 ∈ {00, 01}` | EOR3 BCAX |
| XAR | `11001110 100 Rm imm6 Rn Rd` | XAR |
| three different, PMULL | `0 Q 0 01110 size 1 Rm 1110 00 Rn Rd`, `size ∈ {00, 11}` | PMULL PMULL2 |
| permute | `0 Q 001110 size 0 Rm 0 opc 10 Rn Rd`, `opc ∉ {000, 100}`, `size:Q ≠ 110` | UZP1 TRN1 ZIP1 UZP2 TRN2 ZIP2 |
| scalar copy | `01 0 11110000 imm5 0 0000 1 Rn Rd`, `imm5 ∉ {x0000}` | DUP (element, scalar) |
| data-processing (2 source) | `sf 0 0 11010110 Rm 010 C sz Rn Rd`, `sf = 1 ⇔ sz = 11` | CRC32B/H/W/X CRC32CB/H/W/X |

Rejected (`none`): the other opcodes of each class (SM3, SM4, SHA1/SHA256/SHA512 unallocated
opcodes, the `O = 1` SHA512 group, `Op0 = 1x` four-register), the reserved sizes (PMULL `size`
01/10: UNDEFINED; permute `size:Q = 110`: UNDEFINED; scalar DUP `LowestSetBit(imm5) > 3`:
UNDEFINED), the scalar copy group with `op = 1` or `imm4 ≠ 0000` (unallocated), and the CRC32
combinations `sf = 1, sz ≠ 11` / `sf = 0, sz = 11` (UNDEFINED).
-/

namespace Janus.Arm64

/-- CRC32 (`sf 0 0 11010110 Rm 010 C sz Rn Rd`): `opcode = w<15:10> = 010 C sz`, with
`if sf == '1' && sz != '11' then UNDEFINED; if sf == '0' && sz == '11' then UNDEFINED`.
Every other word (including the other data-processing (2 source) opcodes) is rejected. -/
def decodeCrc32 (w : Nat) : Option CryptoInstr :=
  if w ≥ 2 ^ 32 then none else
  if w &&& 0x7FE0E000 ≠ 0x1AC04000 then none else
  let sf := bit w 31
  let sz := bits w 11 10
  if sf != (sz == 3) then none else
  some (.crc32 sf (bits w 20 16) (bit w 12) sz (bits w 9 5) (bits w 4 0))

/-- The cryptographic-extension, PMULL, permute and scalar-DUP classes of the SIMD&FP
data-processing group (table above); `none` for every other word. -/
def decodeCrypto (w : Nat) : Option CryptoInstr :=
  if w ≥ 2 ^ 32 then none else
  let rd := bits w 4 0
  let rn := bits w 9 5
  let rm := bits w 20 16
  if w &&& 0xFFE08C00 = 0x5E000000 then
    -- Crypto three-register SHA: 01011110 size=00 0 Rm 0 opcode 00 Rn Rd; opcode 111 unallocated
    let opc := bits w 14 12
    if opc = 7 then none else some (.sha3Reg opc rm rn rd)
  else if w &&& 0xFFFE0C00 = 0x5E280800 then
    -- Crypto two-register SHA: 01011110 size=00 10100 opcode 10 Rn Rd
    let opc := bits w 16 12
    if opc ≤ 2 then some (.sha2Reg opc rn rd) else none
  else if w &&& 0xFFE0F000 = 0xCE608000 then
    -- Crypto three-register SHA512: 11001110 011 Rm 1 O=0 00 opcode Rn Rd
    some (.sha512Reg (bits w 11 10) rm rn rd)
  else if w &&& 0xFFFFFC00 = 0xCEC08000 then
    -- Crypto two-register SHA512: 11001110 11000000 1000 opcode=00 Rn Rd (SHA512SU0)
    some (.sha512Su0 rn rd)
  else if w &&& 0xFF808000 = 0xCE000000 then
    -- Crypto four-register: 11001110 0 Op0 Rm 0 Ra Rn Rd; Op0 = 00 EOR3, 01 BCAX, 1x SM3SS1/unallocated
    let op0 := bits w 22 21
    if op0 ≤ 1 then some (.sha4Reg op0 rm (bits w 14 10) rn rd) else none
  else if w &&& 0xFFE00000 = 0xCE800000 then
    -- XAR: 11001110 100 Rm imm6 Rn Rd
    some (.xar rm (bits w 15 10) rn rd)
  else if w &&& 0xBF20FC00 = 0x0E20E000 then
    -- Three different, PMULL{2}: 0 Q U=0 01110 size 1 Rm opcode=1110 00 Rn Rd;
    -- `if size == '01' || size == '10' then UNDEFINED` (size = 11 needs FEAT_PMULL)
    let size := bits w 23 22
    if size = 1 || size = 2 then none else some (.pmull (bit w 30) size rm rn rd)
  else if w &&& 0xBF208C00 = 0x0E000800 then
    -- Permute: 0 Q 001110 size 0 Rm 0 opcode 10 Rn Rd; opcode x00 unallocated;
    -- `if size:Q == '110' then UNDEFINED`
    let opc := bits w 14 12
    let size := bits w 23 22
    if opc % 4 = 0 then none else
    if size = 3 && !bit w 30 then none else
    some (.permute (bit w 30) size rm opc rn rd)
  else if w &&& 0xFFE0FC00 = 0x5E000400 then
    -- Advanced SIMD scalar copy: 01 op=0 11110000 imm5 0 imm4=0000 1 Rn Rd (DUP (element));
    -- `size = LowestSetBit(imm5); if size > 3 then UNDEFINED`
    let imm5 := bits w 20 16
    if imm5 % 16 = 0 then none else some (.dupScalar imm5 rn rd)
  else none

end Janus.Arm64

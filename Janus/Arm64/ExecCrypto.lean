import Janus.Arm64.Crypto
import Janus.Arm64.InstrCrypto

/-!
# Cryptographic extension, CRC32 and permute instructions (trusted)

The operand reads and result writes of the `CryptoInstr` classes, as in their ASL `Operation`
(the operations themselves are in `Janus.Arm64.Crypto`). `Janus.Arm64.exec` dispatches
`Instr.crypto` here and then advances `pc`; none of these instructions can fault once decoded
(`AArch64.CheckFPAdvSIMDEnabled()` passes at EL0 under Linux, which enables FP/SIMD for every
process).

* `V[n, w]` is `State.getV n w`; `V[d, w] = r` is `State.setV d w r`, which zero-extends to
  128 bits (and, with SVE, would zero the upper `Z` bits, invisible here). Every class writes
  `V[d, 128]` except SHA1H (`V[d, 32]`), the 64-bit permutes (`V[d, 64]`) and scalar DUP
  (`V[d, esize]`).
* CRC32 reads `X[n, 32]` and `X[m, size]` (`ZR` for register 31) and writes `X[d, 32]`
  (zero-extended to 64 bits; `XZR` discards).
-/

namespace Janus.Arm64

/-- Execute a decoded `CryptoInstr` (without the `pc` update). -/
def execCrypto (s : State) : CryptoInstr → State
  | .sha3Reg opc rm rn rd =>
    if opc = 0 then s.setV rd 128 (sha1HashOp shaChoose (s.getV rd 128) (s.getV rn 32) (s.getV rm 128))
    else if opc = 1 then s.setV rd 128 (sha1HashOp shaParity (s.getV rd 128) (s.getV rn 32) (s.getV rm 128))
    else if opc = 2 then s.setV rd 128 (sha1HashOp shaMajority (s.getV rd 128) (s.getV rn 32) (s.getV rm 128))
    else if opc = 3 then s.setV rd 128 (sha1Su0Op (s.getV rd 128) (s.getV rn 128) (s.getV rm 128))
    -- SHA256H: `SHA256hash(V[d], V[n], V[m], TRUE)`; SHA256H2: `SHA256hash(V[n], V[d], V[m], FALSE)`
    else if opc = 4 then s.setV rd 128 (sha256Hash (s.getV rd 128) (s.getV rn 128) (s.getV rm 128) true)
    else if opc = 5 then s.setV rd 128 (sha256Hash (s.getV rn 128) (s.getV rd 128) (s.getV rm 128) false)
    else s.setV rd 128 (sha256Su1Op (s.getV rd 128) (s.getV rn 128) (s.getV rm 128))
  | .sha2Reg opc rn rd =>
    if opc = 0 then s.setV rd 32 (sha1HOp (s.getV rn 32))
    else if opc = 1 then s.setV rd 128 (sha1Su1Op (s.getV rd 128) (s.getV rn 128))
    else s.setV rd 128 (sha256Su0Op (s.getV rd 128) (s.getV rn 128))
  | .sha512Reg opc rm rn rd =>
    if opc = 0 then s.setV rd 128 (sha512HOp (s.getV rn 128) (s.getV rm 128) (s.getV rd 128))
    else if opc = 1 then s.setV rd 128 (sha512H2Op (s.getV rn 128) (s.getV rm 128) (s.getV rd 128))
    else if opc = 2 then s.setV rd 128 (sha512Su1Op (s.getV rn 128) (s.getV rm 128) (s.getV rd 128))
    else s.setV rd 128 (rax1Op (s.getV rn 128) (s.getV rm 128))
  | .sha512Su0 rn rd => s.setV rd 128 (sha512Su0Op (s.getV rn 128) (s.getV rd 128))
  | .sha4Reg op0 rm ra rn rd =>
    if op0 = 0 then s.setV rd 128 (eor3Op (s.getV rn 128) (s.getV rm 128) (s.getV ra 128))
    else s.setV rd 128 (bcaxOp (s.getV rn 128) (s.getV rm 128) (s.getV ra 128))
  | .xar rm imm6 rn rd => s.setV rd 128 (xarOp (s.getV rn 128) (s.getV rm 128) imm6)
  | .pmull Q size rm rn rd =>
    s.setV rd 128 (pmullOp (8 * 2 ^ size) Q (s.getV rn 128) (s.getV rm 128))
  | .crc32 _ rm C sz rn rd =>
    let size := 8 * 2 ^ sz
    let acc := (s.readZR rn).toNat % 2 ^ 32
    let val := (s.readZR rm).toNat % 2 ^ size
    s.writeZR rd (BitVec.ofNat 64 (crc32Op C size acc val))
  | .permute Q size rm opc rn rd =>
    let ds := if Q then 128 else 64
    s.setV rd ds (permuteOp size opc ds (s.getV rn ds) (s.getV rm ds))
  | .dupScalar imm5 rn rd =>
    -- size = LowestSetBit(imm5); index = UInt(imm5<4:size+1>);
    -- idxdsize = if imm5<4> == '1' then 128 else 64; esize = 8 << size
    let size := if imm5 % 2 = 1 then 0 else if imm5 / 2 % 2 = 1 then 1 else if imm5 / 4 % 2 = 1 then 2 else 3
    let esize := 8 * 2 ^ size
    let index := imm5 / 2 ^ (size + 1)
    let idxdsize := if imm5 / 16 % 2 = 1 then 128 else 64
    s.setV rd esize (elem (s.getV rn idxdsize) esize index)

end Janus.Arm64

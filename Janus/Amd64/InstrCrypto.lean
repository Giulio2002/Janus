/-!
# x86-64 crypto extensions: the AST (WP-E)

The legacy-encoded AES-NI, `PCLMULQDQ`, SHA-NI and ADX instructions that
`Janus.Amd64.DecodeCrypto` decodes and `Janus.Amd64.ExecCrypto` executes, as one constructor of
`Janus.Amd64.Instr` (`Instr.crypto`).

Conventions are those of `Janus.Amd64.InstrSSE`: `XMMn` is register `n ∈ 0..15`, a vector
source is an `XLoc` (register or memory operand), vector values are naturals `< 2^128` with
dword `i` at bits `32*(i+1)-1 : 32*i`. Every vector instruction here is legacy SSE: it writes
bits 127:0 of its `XMM` destination and preserves bits 255:128. A 128-bit memory operand must
be 16-byte aligned (SDM exception class 4: `#GP` otherwise, `Fault.misaligned`).

`ADCX`/`ADOX` are general-register instructions: `dst` is a register, the source a register or
`w/8` bytes of memory, `w ∈ {32, 64}`.
-/

namespace Janus.Amd64

/-- The four AES round instructions. -/
inductive AesOp where
  /-- `AESENC`: `ShiftRows`, `SubBytes`, `MixColumns`, then `XOR` the round key. -/
  | enc
  /-- `AESENCLAST`: `ShiftRows`, `SubBytes`, `XOR` the round key. -/
  | encLast
  /-- `AESDEC`: `InvShiftRows`, `InvSubBytes`, `InvMixColumns`, `XOR` the round key. -/
  | dec
  /-- `AESDECLAST`: `InvShiftRows`, `InvSubBytes`, `XOR` the round key. -/
  | decLast
deriving Repr, DecidableEq, Inhabited

/-- The two-operand SHA-NI instructions without an immediate. -/
inductive ShaOp where
  /-- `SHA1NEXTE` (`0F 38 C8`). -/
  | sha1nexte
  /-- `SHA1MSG1` (`0F 38 C9`). -/
  | sha1msg1
  /-- `SHA1MSG2` (`0F 38 CA`). -/
  | sha1msg2
  /-- `SHA256RNDS2` (`0F 38 CB`), with the implicit operand `XMM0`. -/
  | sha256rnds2
  /-- `SHA256MSG1` (`0F 38 CC`). -/
  | sha256msg1
  /-- `SHA256MSG2` (`0F 38 CD`). -/
  | sha256msg2
deriving Repr, DecidableEq, Inhabited

/-- The crypto-extension instructions of WP-E, over the operand types of `Instr` (`X = XLoc`,
`L = Loc`; the parameters only break the import cycle with `Janus.Amd64.Instr`). -/
inductive CryptoI (X L : Type) where
  /-- `AESENC`/`AESENCLAST`/`AESDEC`/`AESDECLAST xmm1, xmm2/m128` (`66 0F 38 DC..DF`):
  `XMM[dst] ← round(XMM[dst], src)`, the source being the round key. -/
  | aes (op : AesOp) (dst : Nat) (src : X)
  /-- `AESIMC xmm1, xmm2/m128` (`66 0F 38 DB`): `InvMixColumns` of the source. -/
  | aesimc (dst : Nat) (src : X)
  /-- `AESKEYGENASSIST xmm1, xmm2/m128, imm8` (`66 0F 3A DF`). -/
  | aeskeygenassist (dst : Nat) (src : X) (imm : Nat)
  /-- `PCLMULQDQ xmm1, xmm2/m128, imm8` (`66 0F 3A 44`): the carry-less product of quadword
  `imm8<0>` of `XMM[dst]` and quadword `imm8<4>` of the source (the other bits are ignored). -/
  | pclmulqdq (dst : Nat) (src : X) (imm : Nat)
  /-- `SHA1RNDS4 xmm1, xmm2/m128, imm8` (`0F 3A CC`): four SHA-1 rounds with the function and
  constant of `imm8<1:0>` (the other bits are ignored). -/
  | sha1rnds4 (dst : Nat) (src : X) (imm : Nat)
  /-- The other SHA-NI instructions, `XMM[dst] ← op(XMM[dst], src)`. -/
  | sha (op : ShaOp) (dst : Nat) (src : X)
  /-- `ADCX` (`ovf = false`, `66 0F 38 F6`) / `ADOX` (`ovf`, `F3 0F 38 F6`) `r32/r64, r/m32/64`:
  `dst ← dst + src + CF` (`OF` for `ADOX`), the carry out written to `CF` (`OF`) only; the other
  five status flags are unchanged. The 32-bit form zero-extends the destination. -/
  | adx (ovf : Bool) (w : Nat) (dst : Nat) (src : L)
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64

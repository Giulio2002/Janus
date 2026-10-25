import Janus.Amd64.DecodeSSE

/-!
# Decoder for the x86 crypto extensions (WP-E)

`DecodeCrypto.decode` is consulted by `Janus.Amd64.Decode.decodeLegacy` after
`Janus.Amd64.DecodeSSE.decode`, for a two-byte-map instruction that both the main decoder and the
SSE decoder reject. It takes the same arguments as `DecodeSSE.decode` (the prefixes already
parsed, the opcode byte after `0F`, the bytes after it, the number of bytes before it, and the
main decoder's ModRM parser `mrm`). `LOCK` and `FS` are rejected by `decodeLegacy` for
everything decoded here (`Decode.lockable`, `Decode.withFS` accept none of these forms).

The encodings (SDM Vol. 2, and appendix A for the mandatory prefixes):

| encoding | instruction |
|---|---|
| `66 0F 38 DB /r` | `AESIMC xmm1, xmm2/m128` |
| `66 0F 38 DC /r` .. `66 0F 38 DF /r` | `AESENC`, `AESENCLAST`, `AESDEC`, `AESDECLAST xmm1, xmm2/m128` |
| `66 0F 3A DF /r ib` | `AESKEYGENASSIST xmm1, xmm2/m128, imm8` |
| `66 0F 3A 44 /r ib` | `PCLMULQDQ xmm1, xmm2/m128, imm8` |
| `NP 0F 3A CC /r ib` | `SHA1RNDS4 xmm1, xmm2/m128, imm8` |
| `NP 0F 38 C8 /r` .. `NP 0F 38 CD /r` | `SHA1NEXTE`, `SHA1MSG1`, `SHA1MSG2`, `SHA256RNDS2`, `SHA256MSG1`, `SHA256MSG2 xmm1, xmm2/m128` |
| `66 (REX.W) 0F 38 F6 /r` | `ADCX r32/r64, r/m32/64` |
| `F3 (REX.W) 0F 38 F6 /r` | `ADOX r32/r64, r/m32/64` |

The mandatory prefix must be exactly the one listed (`NP`: none of `66`/`F2`/`F3`); any other
combination (`66` together with `F2`/`F3` in particular) is rejected. `REX.W` selects nothing on
the vector forms (ignored by hardware) and is accepted there; on `ADCX`/`ADOX` it selects the
64-bit form.
-/

namespace Janus.Amd64.DecodeCrypto

open Janus.Amd64.DecodeSSE (MRM gpr imm8)

abbrev I := CryptoI XLoc Loc

/-- Decode a crypto-extension instruction of the `0F` map (see the module doc). `n` counts the
bytes before `op` (prefixes and `0F`). -/
def decode (opsize : Bool) (rep : Nat) (rex : Option Nat) (mrm : MRM) (op : Nat)
    (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let rexP := rex.isSome
  let rexW := rex.getD 0 / 8 = 1
  -- the mandatory prefix: 0 none, 1 = 66, 2 = F3, 3 = F2, 4 = 66 with F2/F3
  let sel := if opsize ∧ rep ≠ 0 then 4 else if opsize then 1 else if rep = 0xF3 then 2
    else if rep = 0xF2 then 3 else 0
  let fin (i : I) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (.crypto i, len)
  if op = 0x38 ∨ op = 0x3A then
    match bs with
    | [] => none
    | op3 :: rest3 =>
      -- ModRM after the third opcode byte
      let m3 (k : Nat → XLoc → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
        match mrm rest3 with
        | some (reg, _, rm, rest, c) => k reg rm rest (n + 2 + c)
        | none => none
      -- ModRM then `imm8`
      let m3i (k : Nat → XLoc → Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
        m3 fun reg rm rest len =>
          match imm8 rest with
          | some v => k reg rm v (len + 1)
          | none => none
      if op = 0x38 then
        if op3 = 0xDB then
          if sel ≠ 1 then none else m3 fun reg rm _ len => fin (.aesimc reg rm) len
        else if 0xDC ≤ op3 ∧ op3 ≤ 0xDF then
          if sel ≠ 1 then none else
          let o := if op3 = 0xDC then AesOp.enc else if op3 = 0xDD then .encLast
            else if op3 = 0xDE then .dec else .decLast
          m3 fun reg rm _ len => fin (.aes o reg rm) len
        else if 0xC8 ≤ op3 ∧ op3 ≤ 0xCD then
          if sel ≠ 0 then none else
          let o := if op3 = 0xC8 then ShaOp.sha1nexte else if op3 = 0xC9 then .sha1msg1
            else if op3 = 0xCA then .sha1msg2 else if op3 = 0xCB then .sha256rnds2
            else if op3 = 0xCC then .sha256msg1 else .sha256msg2
          m3 fun reg rm _ len => fin (.sha o reg rm) len
        else if op3 = 0xF6 then
          if sel = 1 ∨ sel = 2 then
            let w := if rexW then 64 else 32
            m3 fun reg rm _ len => fin (.adx (sel = 2) w reg (gpr rexP w rm)) len
          else none
        else none
      else
        if op3 = 0xDF then
          if sel ≠ 1 then none else m3i fun reg rm v len => fin (.aeskeygenassist reg rm v) len
        else if op3 = 0x44 then
          if sel ≠ 1 then none else m3i fun reg rm v len => fin (.pclmulqdq reg rm v) len
        else if op3 = 0xCC then
          if sel ≠ 0 then none else m3i fun reg rm v len => fin (.sha1rnds4 reg rm v) len
        else none
  else none

end Janus.Amd64.DecodeCrypto

import Janus.Amd64.ExecSSE
import Janus.Arm64.Crypto

/-!
# Semantics of the x86 crypto extensions (WP-E, trusted)

`ExecCrypto.exec` executes a `CryptoI` (decoded by `Janus.Amd64.DecodeCrypto`);
`Janus.Amd64.exec` dispatches `Instr.crypto` here, passing the linear address of each memory
operand (`ea`). Each operation is the `Operation` section of the Intel SDM Vol. 2 (Intel 64 and
IA-32 Architectures Software Developer's Manual, order no. 325383) for the instruction,
transcribed over dwords and bytes:

* **AES-NI.** The AES transformations are shared with the arm64 model (`Janus.Arm64.Vector`:
  `aesShiftRows`, `aesSubBytes`, `aesMixColumns` and their inverses, transcribed there from the
  Arm ASL). Both architectures hold the AES state in a 128-bit register with byte `i` the
  FIPS-197 state byte `in[i]` (`s[i mod 4, i / 4]`), so the helpers apply unchanged; the round
  instructions differ only in how they compose them (`AESENC = MixColumns ∘ SubBytes ∘
  ShiftRows` then `XOR` the key, against arm64's `AESE = SubBytes ∘ ShiftRows ∘ XOR`).
  `Janus.Spec.AES` proves every instruction equal to the FIPS-197 transformations written
  independently (S-box from the GF(2^8) inverse and the affine map).
* **PCLMULQDQ.** The carry-less product is the polynomial multiplication `polyMult` of
  `Janus.Arm64.Crypto` (arm64 `PMULL`).
* **SHA-NI.** The SHA-1 / SHA-256 functions `Ch`, `Parity`, `Maj`, `Σ0`, `Σ1` are the ones of
  `Janus.Arm64.Crypto` (`shaChoose`, `shaParity`, `shaMajority`, `shaHashSigma0/1`; the SDM's
  `f0 = (B AND C) XOR ((NOT B) AND D)` is `shaChoose B C D`, its `f2` is `shaMajority`); the
  message schedule `σ0`/`σ1` are written out. Additions are modulo `2^32` (`add32`).
* **ADX.** `ADCX`/`ADOX` add with the carry flag (overflow flag) as carry in and out and leave
  the other five status flags unchanged. Reading `CF` (`OF`) when the model has it undefined
  faults with `undefinedFlag`, as every other flag reader does.

Memory operands of the vector instructions are 16 bytes and must be 16-byte aligned
(`misaligned`, SDM exception class 4); the `ADCX`/`ADOX` source is `w/8` bytes, never checked.
-/

namespace Janus.Amd64.ExecCrypto

open Janus.Arm64 (elem ofElems rorNat rolNat add32 shaChoose shaParity shaMajority
  shaHashSigma0 shaHashSigma1 polyMult aesShiftRows aesSubBytes aesMixColumns aesSbox)
open Janus.Amd64.ExecSSE (readN readG doneX setReg)

/-! ## AES-NI -/

/-- `AESENC`/`AESENCLAST`/`AESDEC`/`AESDECLAST` of the state `a` (`SRC1 = XMM[dst]`) and the
round key `k` (`SRC2`). -/
def aesRound (op : AesOp) (a k : Nat) : Nat :=
  match op with
  | .enc => aesMixColumns false (aesSubBytes false (aesShiftRows false a)) ^^^ k
  | .encLast => aesSubBytes false (aesShiftRows false a) ^^^ k
  | .dec => aesMixColumns true (aesSubBytes true (aesShiftRows true a)) ^^^ k
  | .decLast => aesSubBytes true (aesShiftRows true a) ^^^ k

/-- `SubWord` of a dword: the S-box applied to each byte. -/
def subWord (x : Nat) : Nat := ofElems 8 4 fun i => aesSbox.getD (elem x 8 i) 0

/-- `RotWord(x) = x[7:0] << 24 | x[31:8]` (`ROR(x, 8)`: byte 0 moves to byte 3). -/
def rotWord (x : Nat) : Nat := x % 2 ^ 8 * 2 ^ 24 + x / 2 ^ 8

/-- `AESKEYGENASSIST` of the source `b` with `RCON = imm8`:
`DEST[31:0] ← SubWord(X1)`, `DEST[63:32] ← RotWord(SubWord(X1)) XOR RCON`,
`DEST[95:64] ← SubWord(X3)`, `DEST[127:96] ← RotWord(SubWord(X3)) XOR RCON`, with `X1 =
SRC[63:32]`, `X3 = SRC[127:96]`. -/
def keygenAssist (b imm : Nat) : Nat :=
  let x1 := subWord (elem b 32 1)
  let x3 := subWord (elem b 32 3)
  ofElems 32 4 fun i =>
    if i = 0 then x1 else if i = 1 then rotWord x1 ^^^ imm
    else if i = 2 then x3 else rotWord x3 ^^^ imm

/-! ## PCLMULQDQ -/

/-- `PCLMULQDQ`: `TEMP1 ← SRC1[imm8<0> ? 127:64 : 63:0]`, `TEMP2 ← SRC2[imm8<4> ? 127:64 : 63:0]`,
`DEST ← TEMP1 ⊗ TEMP2` (carry-less, 127 bits). -/
def clmul (a b imm : Nat) : Nat :=
  let x := elem a 64 (imm % 2)
  let y := elem b 64 (imm / 16 % 2)
  polyMult 64 x y

/-! ## SHA-NI -/

/-- `ROL` on dwords. -/
@[reducible] def rol32 (x k : Nat) : Nat := rolNat 32 x k

/-- SHA-256 `σ0(W) = ROR(W, 7) XOR ROR(W, 18) XOR SHR(W, 3)`. -/
def sigma0 (x : Nat) : Nat := (rorNat 32 x 7 ^^^ rorNat 32 x 18) ^^^ x / 2 ^ 3

/-- SHA-256 `σ1(W) = ROR(W, 17) XOR ROR(W, 19) XOR SHR(W, 10)`. -/
def sigma1 (x : Nat) : Nat := (rorNat 32 x 17 ^^^ rorNat 32 x 19) ^^^ x / 2 ^ 10

/-- The SHA-1 round function `f_j` of `SHA1RNDS4` (`j = imm8<1:0>`). -/
def sha1F (j b c d : Nat) : Nat :=
  if j = 0 then shaChoose b c d else if j = 2 then shaMajority b c d else shaParity b c d

/-- The SHA-1 round constant `K_j`. -/
def sha1K (j : Nat) : Nat :=
  if j = 0 then 0x5A827999 else if j = 1 then 0x6ED9EBA1 else if j = 2 then 0x8F1BBCDC
  else 0xCA62C1D6

/-- One `SHA1RNDS4` round on `(A, B, C, D, E)` with the message word `w` (already including `E`
for the first round): `A' = f(B, C, D) + ROL(A, 5) + w + E + K`, `B' = A`, `C' = ROL(B, 30)`,
`D' = C`, `E' = D`. -/
def sha1Round (j : Nat) (st : Nat × Nat × Nat × Nat × Nat) (w : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let (a, b, c, d, e) := st
  (add32 (add32 (add32 (add32 (sha1F j b c d) (rol32 a 5)) w) e) (sha1K j), a, rol32 b 30, c, d)

/-- `SHA1RNDS4 xmm1, xmm2/m128, imm8`: `A = SRC1[127:96]`, `B = SRC1[95:64]`, `C = SRC1[63:32]`,
`D = SRC1[31:0]`, `W0E = SRC2[127:96]`, `W1 = SRC2[95:64]`, `W2 = SRC2[63:32]`, `W3 =
SRC2[31:0]`; round 0 adds `W0E` (with no `E`), rounds 1–3 add `W_i + E_i`; the result is
`A4 : B4 : C4 : D4` (high to low). -/
def sha1rnds4 (a b imm : Nat) : Nat :=
  let j := imm % 4
  let r0 := sha1Round j (elem a 32 3, elem a 32 2, elem a 32 1, elem a 32 0, 0) (elem b 32 3)
  let r1 := sha1Round j r0 (elem b 32 2)
  let r2 := sha1Round j r1 (elem b 32 1)
  let r3 := sha1Round j r2 (elem b 32 0)
  let (a4, b4, c4, d4, _) := r3
  ofElems 32 4 fun i => if i = 0 then d4 else if i = 1 then c4 else if i = 2 then b4 else a4

/-- `SHA1NEXTE`: `DEST[127:96] ← SRC2[127:96] + ROL(SRC1[127:96], 30)`, `DEST[95:0] ←
SRC2[95:0]`. -/
def sha1nexte (a b : Nat) : Nat :=
  ofElems 32 4 fun i => if i = 3 then add32 (elem b 32 3) (rol32 (elem a 32 3) 30) else elem b 32 i

/-- `SHA1MSG1`: with `W0..W3 = SRC1[127:96] .. SRC1[31:0]`, `W4 = SRC2[127:96]`, `W5 =
SRC2[95:64]`: `DEST ← (W2 XOR W0) : (W3 XOR W1) : (W4 XOR W2) : (W5 XOR W3)`. -/
def sha1msg1 (a b : Nat) : Nat :=
  let w0 := elem a 32 3; let w1 := elem a 32 2; let w2 := elem a 32 1; let w3 := elem a 32 0
  let w4 := elem b 32 3; let w5 := elem b 32 2
  ofElems 32 4 fun i =>
    if i = 3 then w2 ^^^ w0 else if i = 2 then w3 ^^^ w1 else if i = 1 then w4 ^^^ w2 else w5 ^^^ w3

/-- `SHA1MSG2`: `W13 = SRC2[95:64]`, `W14 = SRC2[63:32]`, `W15 = SRC2[31:0]`,
`W16 = ROL(SRC1[127:96] XOR W13, 1)`, `W17 = ROL(SRC1[95:64] XOR W14, 1)`,
`W18 = ROL(SRC1[63:32] XOR W15, 1)`, `W19 = ROL(SRC1[31:0] XOR W16, 1)`;
`DEST ← W16 : W17 : W18 : W19`. -/
def sha1msg2 (a b : Nat) : Nat :=
  let w13 := elem b 32 2; let w14 := elem b 32 1; let w15 := elem b 32 0
  let w16 := rol32 (elem a 32 3 ^^^ w13) 1
  let w17 := rol32 (elem a 32 2 ^^^ w14) 1
  let w18 := rol32 (elem a 32 1 ^^^ w15) 1
  let w19 := rol32 (elem a 32 0 ^^^ w16) 1
  ofElems 32 4 fun i => if i = 3 then w16 else if i = 2 then w17 else if i = 1 then w18 else w19

/-- One `SHA256RNDS2` round on `(A, B, C, D, E, F, G, H)` with `WK`:
`T = Ch(E, F, G) + Σ1(E) + WK + H`, `A' = T + Maj(A, B, C) + Σ0(A)`, `E' = T + D`, the other
words shifted down. -/
def sha256Round (st : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) (wk : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let (a, b, c, d, e, f, g, h) := st
  let t := add32 (add32 (add32 (shaChoose e f g) (shaHashSigma1 e)) wk) h
  (add32 (add32 t (shaMajority a b c)) (shaHashSigma0 a), a, b, c, add32 t d, e, f, g)

/-- `SHA256RNDS2 xmm1, xmm2/m128, <XMM0>`: `A0 = SRC2[127:96]`, `B0 = SRC2[95:64]`,
`C0 = SRC1[127:96]`, `D0 = SRC1[95:64]`, `E0 = SRC2[63:32]`, `F0 = SRC2[31:0]`,
`G0 = SRC1[63:32]`, `H0 = SRC1[31:0]`, `WK0 = XMM0[31:0]`, `WK1 = XMM0[63:32]`; two rounds;
`DEST ← A2 : B2 : E2 : F2`. -/
def sha256rnds2 (a b k : Nat) : Nat :=
  let s0 := (elem b 32 3, elem b 32 2, elem a 32 3, elem a 32 2,
    elem b 32 1, elem b 32 0, elem a 32 1, elem a 32 0)
  let s1 := sha256Round s0 (elem k 32 0)
  let (a2, b2, _, _, e2, f2, _, _) := sha256Round s1 (elem k 32 1)
  ofElems 32 4 fun i => if i = 0 then f2 else if i = 1 then e2 else if i = 2 then b2 else a2

/-- `SHA256MSG1`: `W4 = SRC2[31:0]`, `W3..W0 = SRC1[127:96] .. SRC1[31:0]`;
`DEST ← (W3 + σ0(W4)) : (W2 + σ0(W3)) : (W1 + σ0(W2)) : (W0 + σ0(W1))`. -/
def sha256msg1 (a b : Nat) : Nat :=
  ofElems 32 4 fun i => add32 (elem a 32 i) (sigma0 (if i = 3 then elem b 32 0 else elem a 32 (i + 1)))

/-- `SHA256MSG2`: `W14 = SRC2[95:64]`, `W15 = SRC2[127:96]`, `W16 = SRC1[31:0] + σ1(W14)`,
`W17 = SRC1[63:32] + σ1(W15)`, `W18 = SRC1[95:64] + σ1(W16)`, `W19 = SRC1[127:96] + σ1(W17)`;
`DEST ← W19 : W18 : W17 : W16`. -/
def sha256msg2 (a b : Nat) : Nat :=
  let w16 := add32 (elem a 32 0) (sigma1 (elem b 32 2))
  let w17 := add32 (elem a 32 1) (sigma1 (elem b 32 3))
  let w18 := add32 (elem a 32 2) (sigma1 w16)
  let w19 := add32 (elem a 32 3) (sigma1 w17)
  ofElems 32 4 fun i => if i = 0 then w16 else if i = 1 then w17 else if i = 2 then w18 else w19

/-- The two-operand SHA-NI operations (`k = XMM0` for `SHA256RNDS2`). -/
def shaOp (op : ShaOp) (a b k : Nat) : Nat :=
  match op with
  | .sha1nexte => sha1nexte a b
  | .sha1msg1 => sha1msg1 a b
  | .sha1msg2 => sha1msg2 a b
  | .sha256rnds2 => sha256rnds2 a b k
  | .sha256msg1 => sha256msg1 a b
  | .sha256msg2 => sha256msg2 a b

/-! ## The executor -/

/-- Execute `i` at `pc` (next instruction at `next`), with `ea` the linear address of a memory
operand. -/
def exec (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : CryptoI XLoc Loc) :
    Except Fault State :=
  let x (n : Nat) : Nat := (s.xmm n).toNat
  match i with
  | .aes op d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (aesRound op (x d) b)
  | .aesimc d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (aesMixColumns true b)
  | .aeskeygenassist d src imm =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (keygenAssist b imm)
  | .pclmulqdq d src imm =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (clmul (x d) b imm)
  | .sha1rnds4 d src imm =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (sha1rnds4 (x d) b imm)
  | .sha op d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (shaOp op (x d) b (x 0))
  | .adx ovf w d src =>
    match readG s ea w src with
    | .error e => .error e
    | .ok v =>
      match (if ovf then s.flags.ovf else s.flags.cf) with
      | none => .error (.undefinedFlag pc)
      | some c =>
        let sum := (s.regs d).toNat % 2 ^ w + v + c.toNat
        let fl := if ovf then { s.flags with ovf := some (decide (2 ^ w ≤ sum)) }
          else { s.flags with cf := some (decide (2 ^ w ≤ sum)) }
        .ok { setReg s d (BitVec.ofNat 64 (sum % 2 ^ w)) with flags := fl, rip := next }

end Janus.Amd64.ExecCrypto

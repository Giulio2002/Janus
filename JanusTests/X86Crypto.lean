import Janus

/-!
# Known-answer tests of the x86 crypto extensions (WP-E)

* **Decoding** of each AES-NI / `PCLMULQDQ` / SHA-NI / ADX form, and neighbours that must stay
  rejected (wrong mandatory prefix, `LOCK`).
* **Known answers against the standards.** The instruction semantics of
  `Janus.Amd64.ExecCrypto`, composed the way Intel's reference code composes the instructions,
  compute the FIPS-197 appendix C.1 (AES-128) and C.3 (AES-256) vectors, encryption (key
  expansion with `AESKEYGENASSIST`, `AESENC`/`AESENCLAST`) and decryption (the Equivalent Inverse
  Cipher with `AESIMC`, `AESDEC`/`AESDECLAST`), and the FIPS 180-4 vectors SHA-1("abc") and
  SHA-256("abc") with `SHA1RNDS4`/`SHA1NEXTE`/`SHA1MSG1`/`SHA1MSG2` and
  `SHA256RNDS2`/`SHA256MSG1`/`SHA256MSG2`.
* **The Intel AES-NI white paper examples** (S. Gueron, *Intel Advanced Encryption Standard (AES)
  New Instructions Set*, rev. 3.01, §5), also observed on the oracle host, and carry-less products
  computed independently (Python).

All of it is evaluated by the kernel (`decide +kernel`).
-/

namespace JanusTests.X86Crypto

open Janus.Amd64 Janus.Amd64.ExecCrypto
open Janus.Arm64 (elem ofElems)

/-! ## Decoding -/

example : decode [0x66, 0x0f, 0x38, 0xdc, 0xc1] = some (.crypto (.aes .enc 0 (.xmm 1)), 5) := by decide
example : decode [0x66, 0x0f, 0x38, 0xdd, 0xc1] = some (.crypto (.aes .encLast 0 (.xmm 1)), 5) := by decide
example : decode [0x66, 0x44, 0x0f, 0x38, 0xde, 0x47, 0x10] =
    some (.crypto (.aes .dec 8 (.mem ⟨some 7, none, 0, 16, false, false⟩)), 7) := by decide
example : decode [0x66, 0x0f, 0x38, 0xdf, 0xc1] = some (.crypto (.aes .decLast 0 (.xmm 1)), 5) := by decide
example : decode [0x66, 0x0f, 0x38, 0xdb, 0xc1] = some (.crypto (.aesimc 0 (.xmm 1)), 5) := by decide
example : decode [0x66, 0x0f, 0x3a, 0xdf, 0xc8, 0x01] =
    some (.crypto (.aeskeygenassist 1 (.xmm 0) 1), 6) := by decide
example : decode [0x66, 0x0f, 0x3a, 0x44, 0xc1, 0x11] = some (.crypto (.pclmulqdq 0 (.xmm 1) 0x11), 6) := by decide
example : decode [0x0f, 0x3a, 0xcc, 0xc1, 0x02] = some (.crypto (.sha1rnds4 0 (.xmm 1) 2), 5) := by decide
example : decode [0x0f, 0x38, 0xc8, 0xc1] = some (.crypto (.sha .sha1nexte 0 (.xmm 1)), 4) := by decide
example : decode [0x0f, 0x38, 0xcb, 0xca] = some (.crypto (.sha .sha256rnds2 1 (.xmm 2)), 4) := by decide
example : decode [0x0f, 0x38, 0xcd, 0xca] = some (.crypto (.sha .sha256msg2 1 (.xmm 2)), 4) := by decide
example : decode [0x66, 0x48, 0x0f, 0x38, 0xf6, 0xc3] = some (.crypto (.adx false 64 0 (.reg 3)), 6) := by decide
example : decode [0xf3, 0x0f, 0x38, 0xf6, 0x07] =
    some (.crypto (.adx true 32 0 (.mem ⟨some 7, none, 0, 0, false, false⟩)), 5) := by decide
-- rejected: AESENC without 66, SHA1MSG1 with 66, ADCX/ADOX with F2 or with 66 and F3, LOCK,
-- AESKEYGENASSIST with F3, SHA1RNDS4 with 66
example : decode [0x0f, 0x38, 0xdc, 0xc1] = none := by decide
example : decode [0x66, 0x0f, 0x38, 0xc9, 0xc1] = none := by decide
example : decode [0xf2, 0x0f, 0x38, 0xf6, 0xc3] = none := by decide
example : decode [0x66, 0xf3, 0x0f, 0x38, 0xf6, 0xc3] = none := by decide
example : decode [0xf0, 0x66, 0x0f, 0x38, 0xdc, 0x07] = none := by decide
example : decode [0xf3, 0x0f, 0x3a, 0xdf, 0xc8, 0x01] = none := by decide
example : decode [0x66, 0x0f, 0x3a, 0xcc, 0xc1, 0x00] = none := by decide

/-! ## The Intel white paper examples (and the host) -/

def wpA : Nat := 0x7b5b54657374566563746f725d53475d
def wpK : Nat := 0x48692853686179295b477565726f6e5d

example : aesRound .enc wpA wpK = 0xa8311c2f9fdba3c58b104b58ded7e595 := by decide +kernel
example : aesRound .encLast wpA wpK = 0xc7fb881e938c5964177ec42553fdc611 := by decide +kernel
example : aesRound .dec wpA wpK = 0x138ac342faea2787b58eb95eb730392a := by decide +kernel
example : aesRound .decLast wpA wpK = 0xc5a391ef6b317f95d410637b72a593d0 := by decide +kernel
example : Janus.Arm64.aesMixColumns true wpK = 0x597f8df109efaa15f39bc5a119d859b6 := by decide +kernel
example : keygenAssist 0x3c4fcf098815f7aba6d2ae2816157e2b 1 = 0x01eb848beb848a013424b5e524b5e434 := by
  decide +kernel
example : clmul wpA wpK 0x00 = 0x1d4d84c85c3440c0929633d5d36f0451 := by decide +kernel
example : clmul wpA wpK 0x01 = 0x1a2bf6db3a30862fbabf262df4b7d5c9 := by decide +kernel
example : clmul wpA wpK 0x10 = 0x1bd17c8d556ab5a17fa540ac2a281315 := by decide +kernel
example : clmul wpA wpK 0x11 = 0x1d1e1f2c592e7c45d66ee03e410fd4ed := by decide +kernel
-- the other immediate bits are ignored
example : clmul wpA wpK 0xee = clmul wpA wpK 0x00 := by decide +kernel
example : clmul wpA wpK 0xff = clmul wpA wpK 0x11 := by decide +kernel
-- carry-less arithmetic: (x + 1)^2 = x^2 + 1, x^63 · x^63 = x^126
example : clmul 3 3 0 = 5 := by decide +kernel
example : clmul (2 ^ 63) (2 ^ 63 * 2 ^ 64) 0x10 = 2 ^ 126 := by decide +kernel
-- observed on the host (Intel Xeon Gold 5412U, gcc intrinsics)
example : sha1rnds4 wpA wpK 0 = 0xd80be11fc27a282f4c98cee8df735d84 := by decide +kernel
example : sha256rnds2 wpA wpK 0x3c4fcf098815f7aba6d2ae2816157e2b = 0x3999e8a01ce7b852914bc358f3d151da := by
  decide +kernel

/-! ## AES: FIPS-197 appendix C -/

/-- The little-endian value of a byte list (the bytes as a 128-bit `MOVUPS` load sees them). -/
def ofBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * ofBytes bs

def rcon : List Nat := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

/-- FIPS-197 `KeyExpansion` for `nk` key words, with `SubWord`/`RotWord` from
`AESKEYGENASSIST` (`w[i-1]` in dword 1 of the source: dword 1 of the result is
`RotWord(SubWord(w)) XOR rcon`, dword 0 is `SubWord(w)`). -/
def expand (nk : Nat) : Nat → List Nat → List Nat
  | 0, ws => ws
  | k + 1, ws =>
    let ws := expand nk k ws
    let i := ws.length
    let t := ws.getD (i - 1) 0
    let t := if i % nk = 0 then elem (keygenAssist (t * 2 ^ 32) (rcon.getD (i / nk - 1) 0)) 32 1
      else if nk > 6 ∧ i % nk = 4 then elem (keygenAssist (t * 2 ^ 32) 0) 32 0 else t
    ws ++ [ws.getD (i - nk) 0 ^^^ t]

/-- Round key `j` (words `4j .. 4j+3`, word `4j` in dword 0). -/
def rk (ws : List Nat) (j : Nat) : Nat := ofElems 32 4 fun e => ws.getD (4 * j + e) 0

/-- The key words of a key given as bytes. -/
def keyWords (key : List Nat) : List Nat :=
  (List.range (key.length / 4)).map fun i => ofBytes ((key.drop (4 * i)).take 4)

/-- `AESENC` for rounds `1 .. nr-1`, `AESENCLAST` for round `nr`, after the initial `PXOR`. -/
def encrypt (ws : List Nat) (nr pt : Nat) : Nat :=
  let st := (List.range (nr - 1)).foldl (fun st j => aesRound .enc st (rk ws (j + 1))) (pt ^^^ rk ws 0)
  aesRound .encLast st (rk ws nr)

/-- The Equivalent Inverse Cipher (FIPS-197 §5.3.5): `AESDEC` with the `AESIMC` of round keys
`nr-1 .. 1`, then `AESDECLAST` with round key 0. -/
def decrypt (ws : List Nat) (nr ct : Nat) : Nat :=
  let st := (List.range (nr - 1)).foldl
    (fun st j => aesRound .dec st (Janus.Arm64.aesMixColumns true (rk ws (nr - 1 - j)))) (ct ^^^ rk ws nr)
  aesRound .decLast st (rk ws 0)

def pt : Nat := ofBytes [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb,
  0xcc, 0xdd, 0xee, 0xff]

def w128 : List Nat := expand 4 40 (keyWords (List.range 16))
def ct128 : Nat := ofBytes [0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80,
  0x70, 0xb4, 0xc5, 0x5a]

-- FIPS-197 appendix A.1: the last round key
example : rk w128 10 = ofBytes [0x13, 0x11, 0x1d, 0x7f, 0xe3, 0x94, 0x4a, 0x17, 0xf3, 0x07, 0xa7, 0x8b,
    0x4d, 0x2b, 0x30, 0xc5] := by decide +kernel
-- C.1 AES-128
example : encrypt w128 10 pt = ct128 := by decide +kernel
example : decrypt w128 10 ct128 = pt := by decide +kernel

def w256 : List Nat := expand 8 52 (keyWords (List.range 32))
def ct256 : Nat := ofBytes [0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90,
  0x4b, 0x49, 0x60, 0x89]

-- C.3 AES-256
example : encrypt w256 14 pt = ct256 := by decide +kernel
example : decrypt w256 14 ct256 = pt := by decide +kernel

/-! ## SHA-256("abc") with SHA256RNDS2/MSG1/MSG2 (FIPS 180-4, appendix B.1) -/

def k256 : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Words `4i .. 4i+3` of `l` as a vector (dword 0 = word `4i`). -/
def vec4 (l : List Nat) (i : Nat) : Nat := ofElems 32 4 fun e => l.getD (4 * i + e) 0

/-- Words `4i .. 4i+3` of `l` with word `4i` in dword 3 (the SHA-1 message layout). -/
def vec4r (l : List Nat) (i : Nat) : Nat := ofElems 32 4 fun e => l.getD (4 * i + 3 - e) 0

/-- `PADDD`. -/
def add4 (x y : Nat) : Nat := ExecSSE.pintOp (.add 32) x y

/-- `W[k+4] = SHA256MSG2(SHA256MSG1(W[k], W[k+1]) + PALIGNR(W[k+3], W[k+2], 4), W[k+3])`. -/
def sched256 : Nat → List Nat → List Nat
  | 0, ws => ws
  | k + 1, ws =>
    let ws := sched256 k ws
    let i := ws.length - 4
    ws ++ [sha256msg2 (add4 (sha256msg1 (ws.getD i 0) (ws.getD (i + 1) 0))
      (ExecSSE.pimmOp .palignr (ws.getD (i + 3) 0) (ws.getD (i + 2) 0) 4)) (ws.getD (i + 3) 0)]

/-- Four rounds per step on `(ABEF, CDGH)`: `CDGH ← SHA256RNDS2(CDGH, ABEF, WK)`, then
`ABEF ← SHA256RNDS2(ABEF, CDGH', WK >> 64)` (`PSHUFD $0x0E`). -/
def rounds256 (ws : List Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st =>
    let st := rounds256 ws k st
    let wk := add4 (ws.getD k 0) (vec4 k256 k)
    let s1 := sha256rnds2 st.2 st.1 wk
    (sha256rnds2 st.1 s1 (wk / 2 ^ 64), s1)

def abc : List Nat := [0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x18]

def h256 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- `ABEF` and `CDGH` (high to low) from `H0 .. H7`. -/
def abef (h : List Nat) : Nat := ofElems 32 4 fun e => h.getD ([5, 4, 1, 0].getD e 0) 0
def cdgh (h : List Nat) : Nat := ofElems 32 4 fun e => h.getD ([7, 6, 3, 2].getD e 0) 0

def sha256abc : List Nat :=
  let ws := sched256 12 ((List.range 4).map (vec4 abc))
  let st := rounds256 ws 16 (abef h256, cdgh h256)
  let x := add4 st.1 (abef h256)
  let y := add4 st.2 (cdgh h256)
  [elem x 32 3, elem x 32 2, elem y 32 3, elem y 32 2, elem x 32 1, elem x 32 0, elem y 32 1, elem y 32 0]

example : sha256abc = [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
    0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by decide +kernel

/-! ## SHA-1("abc") with SHA1RNDS4/NEXTE/MSG1/MSG2 (FIPS 180-4, appendix A.1) -/

/-- `W[k+4] = SHA1MSG2(SHA1MSG1(W[k], W[k+1]) XOR W[k+2], W[k+3])`. -/
def sched1 : Nat → List Nat → List Nat
  | 0, ws => ws
  | k + 1, ws =>
    let ws := sched1 k ws
    let i := ws.length - 4
    ws ++ [sha1msg2 (sha1msg1 (ws.getD i 0) (ws.getD (i + 1) 0) ^^^ ws.getD (i + 2) 0) (ws.getD (i + 3) 0)]

/-- Groups of four rounds on `(ABCD_k, ABCD_{k-1})`: the first adds `E` to `W0` (`PADDD`), the
others take `E` from `SHA1NEXTE(ABCD_{k-1}, W)`. -/
def rounds1 (ws : List Nat) (e : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st =>
    let st := rounds1 ws e k st
    let x := if k = 0 then add4 (e * 2 ^ 96) (ws.getD 0 0) else sha1nexte st.2 (ws.getD k 0)
    (sha1rnds4 st.1 x (k / 5), st.1)

def sha1abc : List Nat :=
  let ws := sched1 16 ((List.range 4).map (vec4r abc))
  let h := [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]
  let e := 0xc3d2e1f0
  let st := rounds1 ws e 20 (vec4r h 0, 0)
  let abcd := add4 st.1 (vec4r h 0)
  let e' := elem (sha1nexte st.2 (e * 2 ^ 96)) 32 3
  [elem abcd 32 3, elem abcd 32 2, elem abcd 32 1, elem abcd 32 0, e']

example : sha1abc = [0xa9993e36, 0x4706816a, 0xba3e2571, 0x7850c26c, 0x9cd0d89d] := by decide +kernel

/-! ## ADCX / ADOX -/

/-- `RAX`, `CF`, `OF` and the other flags after executing `i` from `RAX = a`, `RBX = b`, the
given flags. -/
def adxRun (i : CryptoI XLoc Loc) (a b : Nat) (f : Flags) : Option (Nat × Flags) :=
  let s : State := { (default : State) with
    regs := fun r => if r = 0 then BitVec.ofNat 64 a else if r = 3 then BitVec.ofNat 64 b else 0,
    flags := f }
  match ExecCrypto.exec s 0 0 (fun _ => 0) i with
  | .ok s' => some ((s'.regs 0).toNat, s'.flags)
  | .error _ => none

def fl (cf ovf : Bool) : Flags := ⟨some cf, some true, none, some false, some true, some ovf⟩

-- ADCX: carry in and out through CF only; OF, PF, AF (undefined here), ZF, SF untouched
example : adxRun (.adx false 64 0 (.reg 3)) (2 ^ 64 - 1) 0 (fl true false) =
    some (0, fl true false) := by decide
example : adxRun (.adx false 64 0 (.reg 3)) 5 7 (fl true true) = some (13, fl false true) := by decide
-- ADOX: through OF only
example : adxRun (.adx true 64 0 (.reg 3)) (2 ^ 64 - 1) 1 (fl false true) =
    some (1, fl false true) := by decide
example : adxRun (.adx true 64 0 (.reg 3)) 5 7 (fl true false) = some (12, fl true false) := by decide
-- the 32-bit form zero-extends the destination and carries at bit 32
example : adxRun (.adx false 32 0 (.reg 3)) (2 ^ 40 + 2 ^ 32 - 1) 1 (fl false false) =
    some (0, fl true false) := by decide
-- an undefined carry in faults
example : adxRun (.adx false 64 0 (.reg 3)) 1 1 ⟨none, none, none, none, none, some false⟩ = none := by decide
example : adxRun (.adx true 64 0 (.reg 3)) 1 1 ⟨some false, none, none, none, none, none⟩ = none := by decide

end JanusTests.X86Crypto

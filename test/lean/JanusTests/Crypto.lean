import Janus.Arm64.Exec

/-!
# Crypto extension, CRC32 and permutes: decoding and known-answer tests

* **Decoding.** Every crypto/CRC32/permute/scalar-DUP encoding of the Go 1.26 std assembly that
  the decoder rejected before (`scripts/coverage.sh insn`, arm64), with its `CryptoInstr`, and
  reserved or unallocated neighbours that must stay rejected.
* **Known answers, against the standards, not against qemu.** The operations of
  `Janus.Arm64.Crypto`, composed the way Go's (and Arm's reference) kernels compose the
  instructions, compute the FIPS 180-4 test vectors SHA-1("abc") and SHA-256("abc"), and
  CRC32/CRC32C compute the CRC-32 and CRC-32C check values of "123456789" (ITU-T V.42, RFC 3720).
  PMULL is checked against carry-less products computed independently (Python).

All of it is evaluated by the kernel (`decide +kernel`: no elaborator-side evaluation).
-/

namespace JanusTests.Crypto
open Janus.Arm64

/-! ## Decoding the std words -/

example : decode 0x5e100022 = some (.crypto (.sha3Reg 0 16 1 2)) := by decide   -- sha1c q2, s1, v16.4s
example : decode 0x5e101022 = some (.crypto (.sha3Reg 1 16 1 2)) := by decide   -- sha1p q2, s1, v16.4s
example : decode 0x5e102022 = some (.crypto (.sha3Reg 2 16 1 2)) := by decide   -- sha1m q2, s1, v16.4s
example : decode 0x5e053087 = some (.crypto (.sha3Reg 3 5 4 7)) := by decide    -- sha1su0 v7.4s, v4.4s, v5.4s
example : decode 0x5e094062 = some (.crypto (.sha3Reg 4 9 3 2)) := by decide    -- sha256h q2, q3, v9.4s
example : decode 0x5e095103 = some (.crypto (.sha3Reg 5 9 8 3)) := by decide    -- sha256h2 q3, q8, v9.4s
example : decode 0x5e056086 = some (.crypto (.sha3Reg 6 5 4 6)) := by decide    -- sha256su1 v6.4s, v4.4s, v5.4s
example : decode 0x5e280861 = some (.crypto (.sha2Reg 0 3 1)) := by decide      -- sha1h s1, s3
example : decode 0x5e281885 = some (.crypto (.sha2Reg 1 4 5)) := by decide      -- sha1su1 v5.4s, v4.4s
example : decode 0x5e282887 = some (.crypto (.sha2Reg 2 4 7)) := by decide      -- sha256su0 v7.4s, v4.4s
example : decode 0xce608000 = some (.crypto (.sha512Reg 0 0 0 0)) := by decide  -- sha512h q0, q0, v0.2d
example : decode 0xce608400 = some (.crypto (.sha512Reg 1 0 0 0)) := by decide  -- sha512h2
example : decode 0xce608800 = some (.crypto (.sha512Reg 2 0 0 0)) := by decide  -- sha512su1
example : decode 0xce608c00 = some (.crypto (.sha512Reg 3 0 0 0)) := by decide  -- rax1
example : decode 0xcec08000 = some (.crypto (.sha512Su0 0 0)) := by decide      -- sha512su0
example : decode 0xce220400 = some (.crypto (.sha4Reg 1 2 1 0 0)) := by decide  -- bcax v0.16b, v0.16b, v2.16b, v1.16b
example : decode 0xce000000 = some (.crypto (.sha4Reg 0 0 0 0 0)) := by decide  -- eor3
example : decode 0xce800000 = some (.crypto (.xar 0 0 0 0)) := by decide        -- xar v0.2d, v0.2d, v0.2d, #0
example : decode 0x0eefe10b = some (.crypto (.pmull false 3 15 8 11)) := by decide  -- pmull v11.1q, v8.1d, v15.1d
example : decode 0x4ee0e188 = some (.crypto (.pmull true 3 0 12 8)) := by decide    -- pmull2 v8.1q, v12.2d, v0.2d
example : decode 0x0e20e000 = some (.crypto (.pmull false 0 0 0 0)) := by decide    -- pmull v0.8h, v0.8b, v0.8b
example : decode 0x9ac84d29 = some (.crypto (.crc32 true 8 false 3 9 9)) := by decide    -- crc32x w9, w9, x8
example : decode 0x1aca4929 = some (.crypto (.crc32 false 10 false 2 9 9)) := by decide  -- crc32w w9, w9, w10
example : decode 0x1aca4529 = some (.crypto (.crc32 false 10 false 1 9 9)) := by decide  -- crc32h w9, w9, w10
example : decode 0x1aca4129 = some (.crypto (.crc32 false 10 false 0 9 9)) := by decide  -- crc32b w9, w9, w10
example : decode 0x9ac85d29 = some (.crypto (.crc32 true 8 true 3 9 9)) := by decide     -- crc32cx w9, w9, x8
example : decode 0x1aca5129 = some (.crypto (.crc32 false 10 true 0 9 9)) := by decide   -- crc32cb w9, w9, w10
example : decode 0x5e040681 = some (.crypto (.dupScalar 4 20 1)) := by decide            -- mov s1, v20.s[0]
example : decode 0x4ed23a00 = some (.crypto (.permute true 3 18 3 16 0)) := by decide    -- zip1 v0.2d, v16.2d, v18.2d
example : decode 0x4ed27a04 = some (.crypto (.permute true 3 18 7 16 4)) := by decide    -- zip2 v4.2d, v16.2d, v18.2d
example : decode 0x4e813800 = some (.crypto (.permute true 2 1 3 0 0)) := by decide      -- zip1 v0.4s, v0.4s, v1.4s

/-! ## Rejected neighbours -/

example : decode 0x5e007000 = none := by decide   -- three-register SHA, opcode 111 (unallocated)
example : decode 0x5e400000 = none := by decide   -- three-register SHA, size = 01
example : decode 0x5e283800 = none := by decide   -- two-register SHA, opcode 00011
example : decode 0xce60c000 = none := by decide   -- SM3PARTW1 (O = 1)
example : decode 0xcec08400 = none := by decide   -- SM4E
example : decode 0xce400000 = none := by decide   -- SM3SS1 (four-register, Op0 = 10)
example : decode 0xce408000 = none := by decide   -- SM3TT1A
example : decode 0x0e60e000 = none := by decide   -- PMULL, size = 01 (UNDEFINED)
example : decode 0x0ea0e000 = none := by decide   -- PMULL, size = 10 (UNDEFINED)
example : decode 0x0ec03800 = none := by decide   -- ZIP1 .1D (size:Q = 110, UNDEFINED)
example : decode 0x0e000800 = none := by decide   -- permute, opcode 000 (unallocated)
example : decode 0x0e004800 = none := by decide   -- permute, opcode 100 (unallocated)
example : decode 0x5e000400 = none := by decide   -- DUP (scalar), imm5 = 00000 (UNDEFINED)
example : decode 0x5e100400 = none := by decide   -- DUP (scalar), imm5 = 10000 (UNDEFINED)
example : decode 0x7e040400 = none := by decide   -- scalar copy, op = 1 (unallocated)
example : decode 0x1ac84d29 = none := by decide   -- CRC32X with sf = 0 (UNDEFINED)
example : decode 0x9ac84929 = none := by decide   -- CRC32W with sf = 1 (UNDEFINED)

/-! ## CRC-32 and CRC-32C check values of "123456789" -/

/-- The bytes of "123456789". -/
def check : List Nat := [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

/-- CRC32B / CRC32CB over a byte list, from the register `c`. -/
def crcB (C : Bool) (c : Nat) : List Nat → Nat
  | [] => c
  | b :: bs => crcB C (crc32Op C 8 c b) bs

-- CRC-32 (ITU-T V.42, zlib): 0xCBF43926; CRC-32C (RFC 3720): 0xE3069283.
example : crcB false 0xFFFFFFFF check ^^^ 0xFFFFFFFF = 0xCBF43926 := by decide +kernel
example : crcB true 0xFFFFFFFF check ^^^ 0xFFFFFFFF = 0xE3069283 := by decide +kernel
-- The same with one CRC32X over "12345678" (little-endian) and a CRC32B, as hash/crc32 does.
example : crc32Op false 8 (crc32Op false 64 0xFFFFFFFF 0x3837363534333231) 0x39 ^^^ 0xFFFFFFFF = 0xCBF43926 := by
  decide +kernel
example : crc32Op true 8 (crc32Op true 64 0xFFFFFFFF 0x3837363534333231) 0x39 ^^^ 0xFFFFFFFF = 0xE3069283 := by
  decide +kernel
-- CRC32W / CRC32H split the same way.
example : crc32Op false 8 (crc32Op false 32 (crc32Op false 16 (crc32Op false 16 0xFFFFFFFF 0x3231) 0x3433)
    0x38373635) 0x39 ^^^ 0xFFFFFFFF = 0xCBF43926 := by decide +kernel

/-! ## SHA-256("abc") with SHA256H/H2/SU0/SU1 (FIPS 180-4, appendix B.1) -/

/-- The 64 round constants. -/
def k256 : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Words `4i .. 4i+3` of `l` as a vector (lane 0 = word `4i`). -/
def vec4 (l : List Nat) (i : Nat) : Nat := ofElems 32 4 fun e => l.getD (4 * i + e) 0

/-- `ADD Vd.4S, Vn.4S, Vm.4S`. -/
def add4 (x y : Nat) : Nat := ofElems 32 4 fun e => (elem x 32 e + elem y 32 e) % 2 ^ 32

/-- The message schedule: `W[i+4] = SHA256SU1(SHA256SU0(W[i], W[i+1]), W[i+2], W[i+3])`. -/
def sched256 : Nat → List Nat → List Nat
  | 0, ws => ws
  | k + 1, ws =>
    let ws := sched256 k ws
    let i := ws.length - 4
    ws ++ [sha256Su1Op (sha256Su0Op (ws.getD i 0) (ws.getD (i + 1) 0)) (ws.getD (i + 2) 0) (ws.getD (i + 3) 0)]

/-- Four rounds per step: `SHA256H` (new `abcd`) and `SHA256H2` (new `efgh`) from the same old state. -/
def rounds256 (ws : List Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st =>
    let st := rounds256 ws k st
    let t := add4 (ws.getD k 0) (vec4 k256 k)
    (sha256Hash st.1 st.2 t true, sha256Hash st.1 st.2 t false)

/-- The padded block of "abc" as sixteen big-endian words. -/
def abc256 : List Nat := [0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x18]

def h256 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def sha256abc : List Nat :=
  let ws := sched256 12 ((List.range 4).map (vec4 abc256))
  let st := rounds256 ws 16 (vec4 h256 0, vec4 h256 1)
  let a := add4 st.1 (vec4 h256 0)
  let e := add4 st.2 (vec4 h256 1)
  (List.range 4).map (elem a 32) ++ (List.range 4).map (elem e 32)

example : sha256abc = [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
    0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad] := by decide +kernel

/-! ## SHA-1("abc") with SHA1C/P/M/H/SU0/SU1 (FIPS 180-4, appendix A.1) -/

/-- `W[i+4] = SHA1SU1(SHA1SU0(W[i], W[i+1], W[i+2]), W[i+3])`. -/
def sched1 : Nat → List Nat → List Nat
  | 0, ws => ws
  | k + 1, ws =>
    let ws := sched1 k ws
    let i := ws.length - 4
    ws ++ [sha1Su1Op (sha1Su0Op (ws.getD i 0) (ws.getD (i + 1) 0) (ws.getD (i + 2) 0)) (ws.getD (i + 3) 0)]

/-- Group `k` of four rounds: `e' = SHA1H(abcd<31:0>)`, `abcd = SHA1{C,P,M}(abcd, e, W + K)`. -/
def rounds1 (ws : List Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st =>
    let st := rounds1 ws k st
    let K := if k < 5 then 0x5a827999 else if k < 10 then 0x6ed9eba1 else if k < 15 then 0x8f1bbcdc else 0xca62c1d6
    let f := if k < 5 then shaChoose else if k < 10 then shaParity else if k < 15 then shaMajority else shaParity
    let t := add4 (ws.getD k 0) (ofElems 32 4 fun _ => K)
    (sha1HashOp f st.1 st.2 t, sha1HOp (elem st.1 32 0))

def sha1abc : List Nat :=
  let ws := sched1 16 ((List.range 4).map (vec4 abc256))
  let h := [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]
  let st := rounds1 ws 20 (vec4 h 0, 0xc3d2e1f0)
  (List.range 4).map (fun e => (elem st.1 32 e + h.getD e 0) % 2 ^ 32) ++ [(st.2 + 0xc3d2e1f0) % 2 ^ 32]

example : sha1abc = [0xa9993e36, 0x4706816a, 0xba3e2571, 0x7850c26c, 0x9cd0d89d] := by decide +kernel

/-! ## PMULL / PMULL2 against independently computed carry-less products -/

example : pmullOp 64 false 0x0c5c7fd0a6a3a450f2a74de452e6b438 0xd23f0824128b2f336513270e269e0d37 =
    0x21cb21aed829d7a3c678c0c05119d028 := by decide +kernel
example : pmullOp 64 true 0x0c5c7fd0a6a3a450f2a74de452e6b438 0xd23f0824128b2f336513270e269e0d37 =
    0x05e556430ead1a9cfdbf4c99100f13f0 := by decide +kernel
example : pmullOp 64 false 0xe8e25d940ed904751818e811892f902b 0x36f675cc81e74ef59531985d5d9dc9f8 =
    0x0df71600e563741fa919d435b4baaac8 := by decide +kernel
example : pmullOp 8 false 0x90c192cfd3ac94af0f21ddb66cad4a26 0xa170b33839263059f28c105d1fb17c23 =
    0x054e110c0dd0213e04a4495d1c1804aa := by decide +kernel
example : pmullOp 8 true 0x90c192cfd3ac94af0f21ddb66cad4a26 0xa170b33839263059f28c105d1fb17c23 =
    0x5a90247053d61368111b16681bc024e7 := by decide +kernel

end JanusTests.Crypto

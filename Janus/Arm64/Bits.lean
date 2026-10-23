/-!
# Bit-level helpers shared by `Decode` and `Exec`

Everything here is plain `Nat` arithmetic with structural recursion only, so that the kernel
(`decide`, `rfl`) and `simp` (via the `Nat.reduce*` simprocs) can evaluate it on literals.
-/

namespace Janus.Arm64

/-- The field `w<hi:lo>` of an instruction word (ARM ARM notation), as a natural number. -/
def bits (w hi lo : Nat) : Nat := (w >>> lo) % 2 ^ (hi + 1 - lo)

/-- The single bit `w<i>`. -/
def bit (w i : Nat) : Bool := (w >>> i) % 2 == 1

/-- `HighestSetBit` of a 7-bit value (`none` when the value is zero). -/
def highestSetBit7 (v : Nat) : Option Nat :=
  if v ≥ 64 then some 6 else if v ≥ 32 then some 5 else if v ≥ 16 then some 4 else
  if v ≥ 8 then some 3 else if v ≥ 4 then some 2 else if v ≥ 2 then some 1 else
  if v ≥ 1 then some 0 else none

/-- `Replicate(elem, k)` for an `esize`-bit element: `k` copies, element 0 in the low bits. -/
def replicateNat (elem esize : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => elem + 2 ^ esize * replicateNat elem esize k

/-- `ROR(x, r)` on an `esize`-bit value, for `r < esize`. -/
def rorNat (esize x r : Nat) : Nat := ((x >>> r) ||| (x <<< (esize - r))) % 2 ^ esize

/-- ARM ARM `DecodeBitMasks(immN, imms, immr, immediate, M)`, returning `(wmask, tmask)`
as naturals `< 2^M`, or `none` where the pseudocode is UNDEFINED (or its assertion
`M >= 2^len` fails). `imms`, `immr` are 6-bit fields.

```
len = HighestSetBit(immN:NOT(imms));  if len < 1 then UNDEFINED;
levels = ZeroExtend(Ones(len), 6);
if immediate && (imms AND levels) == levels then UNDEFINED;
S = UInt(imms AND levels); R = UInt(immr AND levels);
diff = S - R;  esize = 1 << len;  d = UInt(diff<len-1:0>);
welem = ZeroExtend(Ones(S + 1), esize); telem = ZeroExtend(Ones(d + 1), esize);
wmask = Replicate(ROR(welem, R)); tmask = Replicate(telem);
```
-/
def decodeBitMasks (immN : Bool) (imms immr : Nat) (immediate : Bool) (M : Nat) :
    Option (Nat × Nat) :=
  match highestSetBit7 (immN.toNat * 64 + (63 - imms)) with
  | none => none
  | some len =>
    if len < 1 then none else
    if M < 2 ^ len then none else
    let levels := 2 ^ len - 1
    if immediate && (imms &&& levels) == levels then none else
    let S := imms &&& levels
    let R := immr &&& levels
    let esize := 2 ^ len
    -- `diff<len-1:0>` of the 6-bit subtraction `S - R` (both `< esize`):
    let d := (S + esize - R) % esize
    let welem := 2 ^ (S + 1) - 1
    let telem := 2 ^ (d + 1) - 1
    some (replicateNat (rorNat esize welem R) esize (M / esize),
          replicateNat telem esize (M / esize))

/-- Number of leading zero bits of the `n`-bit value `x` (`CountLeadingZeroBits`). -/
def clzNat : (n : Nat) → (x : Nat) → Nat
  | 0, _ => 0
  | n + 1, x => if x.testBit n then 0 else 1 + clzNat n x

/-- Bit reversal of the low `n` bits of `x`. -/
def rbitNat : (n : Nat) → (x : Nat) → Nat
  | 0, _ => 0
  | n + 1, x => (x % 2) * 2 ^ n + rbitNat n (x / 2)

/-- Byte reversal of the low `k` bytes of `x`. -/
def revBytesNat : (k : Nat) → (x : Nat) → Nat
  | 0, _ => 0
  | k + 1, x => (x % 256) * 256 ^ k + revBytesNat k (x / 256)

/-- Reverse the bytes inside each of `c` consecutive `cb`-byte containers of `x`
(REV16/REV32/REV64). -/
def revContainersNat (cb : Nat) : (c : Nat) → (x : Nat) → Nat
  | 0, _ => 0
  | c + 1, x => revBytesNat cb (x % 256 ^ cb) + 256 ^ cb * revContainersNat cb c (x / 256 ^ cb)

end Janus.Arm64

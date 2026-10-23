import Janus

/-!
# Audit: model vs. ARM ARM, memory corner cases (attack surface 3)

Run: `cd /srv/janus && lake env lean audit/model/Model.lean`

**Status after fix F5** (`Memory.accessible`: one region ending at or below `2^48`, and no
read-only region overlapping a write): M1, M2 and M3 are blocked; each section below now has a
`decide` control showing the faulting behaviour.

The decoder and the per-instruction semantics held up (see docs/AUDIT.md, section 3). The
mismatches below are all in the *memory model*: `Memory.accessible` compares `Nat` bounds
against caller-supplied regions without bounding them to the architectural address space,
so a precondition can admit regions that hardware cannot have, and on those states `step`
returns `.ok` with a result the ARM ARM does not produce.

Encodings (checked with aarch64-linux-gnu-as/objdump):
  0xf9000022  str x2, [x1]
  0xb9400083  ldr w3, [x4]
  0xf9000002  str x2, [x0]
  0xf9400023  ldr x3, [x1]
  0xf9400020  ldr x0, [x1]
-/

open Janus Janus.Arm64

namespace Audit.Model

def mkState (regs : Nat → W64) (regions : List Region) (bytes : Nat → Byte := fun _ => 0) :
    State :=
  { regs := regs, sp := 0x10000, pc := 0x400000, flags := ⟨false, false, false, false⟩,
    mem := { bytes := bytes, regions := regions } }

/-- Run a list of words sequentially (no program/fetch involved). -/
def runWords : List Nat → State → Except Fault State
  | [], s => .ok s
  | w :: ws, s => do let s' ← step w s; runWords ws s'

def reg? (r : Nat) : Except Fault State → Option Nat
  | .ok s => some (s.regs r).toNat
  | .error _ => none

/-! ## M1. An access crossing 2^64 succeeds and touches `Nat` addresses ≥ 2^64

`ldr x0, [x1]` with `x1 = 2^64 - 4` and a region `[2^64 - 4, 2^64 + 4)`. ARM ARM `Mem[]`
computes each byte address in 64-bit arithmetic, so bytes 4..7 come from addresses 0..3
(and on Linux EL0 the access faults: nothing is mapped near 2^64). The model returns `.ok`
with bytes read from `Nat` addresses 2^64 .. 2^64+3, which do not exist. -/

def m1Bytes (a : Nat) : Byte :=
  if a < 4 then 0xAA            -- what ARM would read for the upper half (addresses 0..3)
  else if a ≥ 2 ^ 64 then 0x55   -- phantom bytes the model reads
  else 0x11
def m1 : State := mkState (fun i => if i = 1 then BitVec.ofNat 64 (2 ^ 64 - 4) else 0)
  [⟨2 ^ 64 - 4, 8, true⟩, ⟨0, 4, true⟩] m1Bytes

-- before F5: some 0x5555555511111111 ; ARM ARM (wrapping Mem[]): 0xAAAAAAAA11111111
-- after F5 (regions must end at or below 2^48): none (the load faults)
#eval (reg? 0 (runWords [0xf9400020] m1)).map (fun n => String.ofList (Nat.toDigits 16 n))

/-- Store at 2^64-4 then load at 0: the model's store does not reach addresses 0..3, so the
load sees the old bytes. ARM ARM: the store's upper half lands at 0..3, `w3 = 0x...x2>>32`. -/
def m1b : State := mkState
  (fun i => if i = 1 then BitVec.ofNat 64 (2 ^ 64 - 4) else if i = 2 then 0x1122334455667788
    else 0)
  [⟨2 ^ 64 - 4, 8, true⟩, ⟨0, 4, true⟩]
-- before F5: some 0 ; ARM ARM: 0x11223344 ; after F5: none (the store faults)
#eval reg? 3 (runWords [0xf9000022, 0xb9400083] m1b)

/-- M1 blocked: both accesses that would cross 2^64 now fault. -/
example : reg? 0 (runWords [0xf9400020] m1) = none := by decide
example : reg? 3 (runWords [0xf9000022, 0xb9400083] m1b) = none := by decide

/-! ## M2. Top-byte-ignore aliasing is not modelled when a region sits at a tagged address

Linux enables TBI0 for EL0: `[x | (t << 56)]` accesses the same byte as `[x]`. The model
treats `x` and `x + 2^56` as distinct, independently-valued bytes if the precondition lists
regions at both. `Spec.Disjoint x 8 (x + 2^56) 8` holds in `Nat`, yet on hardware the two
pointers alias. -/

def m2 : State := mkState
  (fun i => if i = 0 then 0x1000 else if i = 1 then BitVec.ofNat 64 (2 ^ 56 + 0x1000)
    else if i = 2 then 0xdeadbeef else 0)
  [⟨0x1000, 8, true⟩, ⟨2 ^ 56 + 0x1000, 8, true⟩]
-- before F5: some 0 ; ARM (TBI0, Linux EL0): 0xdeadbeef ; after F5: none (tagged load faults)
#eval reg? 3 (runWords [0xf9000002, 0xf9400023] m2)
/-- M2 blocked: a tagged address is never accessible, so `Ptr` excludes it. `Disjoint` alone is
still plain arithmetic, but no precondition can make memory at `2^56 + 0x1000` usable. -/
example : reg? 3 (runWords [0xf9000002, 0xf9400023] m2) = none := by decide
example : Janus.Spec.Disjoint 0x1000 8 (2 ^ 56 + 0x1000) 8 := by
  unfold Janus.Spec.Disjoint; omega
example (m : Memory) (w : Bool) : ¬ Janus.Spec.Ptr m (BitVec.ofNat 64 (2 ^ 56 + 0x1000)) 8 w :=
  fun h => by have := h.2; revert this; decide

/-! ## M3. "Read-only" is not exclusive: an overlapping writable region permits the store

`store` succeeds if *any* region containing the access is writable, so a read-only data
region (what `Program.DataLoaded` asks for) overlapped by a writable one can be overwritten.
Hardware permissions are per page; a byte is either writable or not. -/

def m3 : State := mkState (fun i => if i = 0 then 0x2000 else if i = 2 then 7 else 0)
  [⟨0x2000, 8, false⟩, ⟨0x2000, 8, true⟩]
-- before F5: .ok (store into the "read-only" bytes); hardware: permission fault
-- after F5: fault readOnly 0x2000 8
#eval match runWords [0xf9000002] m3 with
  | .ok s => s!"ok, byte at 0x2000 = {(s.mem.bytes 0x2000).toNat}"
  | .error e => s!"fault {repr e}"
/-- M3 blocked: the store faults on the read-only bytes. -/
example : (match runWords [0xf9000002] m3 with | .ok _ => false | .error e => decide (e = .readOnly 0x2000 8)) = true := by
  decide

/-! ## Controls: the decoder rejects the CONSTRAINED UNPREDICTABLE / reserved encodings -/

-- ldr x0, [x0], #8 (post-index, Rt = Rn): rejected
example : decode 0xf8408400 = none := by decide
-- ldp x0, x0, [x1] (Rt = Rt2 load): rejected
example : decode 0xa9400020 = none := by decide
-- ldp x1, x2, [x1], #16 (writeback, Rt = Rn): rejected
example : decode 0xa8c10821 = none := by decide
-- add w0, w1, w2, lsl #32 (32-bit, shift ≥ 32): rejected
example : decode 0x0b028020 = none := by decide
-- add x0, x1, x2, ror #1 (ROR in add/sub shifted): rejected
example : decode 0x8bc20420 = none := by decide
-- extr w0, w1, w2, #32 (imms ≥ 32 in W form): rejected
example : decode 0x13828020 = none := by decide
-- extr with sf = 1, N = 0: rejected
example : decode 0x93820020 = none := by decide
-- sbfm with sf = 1, N = 0: rejected
example : decode 0x93000020 = none := by decide
-- movz w0, #1, lsl #32 (hw = 2 in W form): rejected
example : decode 0x52c00020 = none := by decide
-- add x0, x1, w2, uxtw #5 (extended, shift > 4): rejected
example : decode 0x8b225420 = none := by decide
-- ldr x0, [x1, w2, uxtb] (register offset, option<1> = 0): rejected
example : decode 0xf8620820 = none := by decide
-- and w0, w1, #pattern with N = 1 in W form: rejected
example : decode 0x12400020 = none := by decide

/-! ## Controls: semantics at the probed corners agree with the ARM ARM -/

-- ADRP at pc = 2^64 - 4096 with imm = +1 page wraps to 0.
-- adrp x0, #+0x1000 = 0x90000000 | immlo=1 (bit 29) → 0xb0000000
example :
    (match step 0xb0000000 { (default : State) with pc := BitVec.ofNat 64 (2 ^ 64 - 4096) } with
     | .ok s => (s.regs 0).toNat | .error _ => 1) = 0 := by decide

-- ccmp x1, #0, #0b1010 (N=1,Z=0,C=1,V=0), ne, when NE fails (Z set): flags = nzcv immediate.
-- ccmp x1, #0, #10, ne = 0xfa40182a
example :
    (match step 0xfa40182a { (default : State) with flags := ⟨false, true, false, false⟩ } with
     | .ok s => s.flags | .error _ => ⟨false, false, false, false⟩) = ⟨true, false, true, false⟩ := by
  decide

-- tbnz x0, #40, +8: bit 40 (b5 = 1, b40 = 8): 0xb7400040
example :
    (match step 0xb7400040 { (default : State) with regs := fun i => if i = 0 then 1 <<< 40 else 0 } with
     | .ok s => s.pc.toNat | .error _ => 1) = 8 := by decide

-- SP alignment: str x0, [sp, #-8]! (0xf81f8fe0) with SP = 0x10008 faults; with 0x10000 succeeds
-- even though the effective address is only 8-aligned (ARM checks the base SP only).
example :
    (match step 0xf81f8fe0 ({ (default : State) with sp := 0x10008, mem := ⟨fun _ => 0, [⟨0, 2 ^ 20, true⟩]⟩ } : State) with
     | .ok _ => false | .error e => decide (e = .spMisaligned 0x10008)) = true := by decide
example :
    (match step 0xf81f8fe0 ({ (default : State) with sp := 0x10000, mem := ⟨fun _ => 0, [⟨0, 2 ^ 20, true⟩]⟩ } : State) with
     | .ok s => s.sp.toNat | .error _ => 0) = 0xfff8 := by decide

end Audit.Model

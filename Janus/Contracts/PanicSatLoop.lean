import Janus.Contracts.PanicSat

/-!
# The panic model engine's loop (arm64)

The steps of the loop head `LH` of the model engine (`docs/model/panic_model_arm64.s`), each a
`ReachesRet` of the engine alone, and the recovery (`DROP`) loop. `Janus.Contracts.PanicSatEngine`
assembles them into the proof that the `gopanic`, `Goexit` and `deferreturn` contracts hold.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel

/-! ## The loop (`LH`)

At the loop head the model's frame (96 bytes at `msp = F.sp - 96`) holds `F.sp`, `F.bound`,
`F.resume`, the mode, the phase (open-coded defers still to run, or records), the `deferBits` and
slot addresses and the caller's `X18` (and, for `deferreturn`, the return address and `X29`). The
calls still to make are `frameItems` of the current memory, for the frame with or without its
open-coded part. -/

def modeCode : DeferMode → Nat
  | .panic => 0 | .goexit => 1 | .ret => 2

/-- The frame the loop is still running: without its open-coded part once the phase is `0`. -/
def phF (F : Frame) (ph : Nat) : Frame := if ph = 0 then { F with openAt := none } else F

/-- The calls still to make at a loop state with memory `m` and phase `ph`. -/
def curItems (m : Memory) (F : Frame) (ph : Nat) : List Item := frameItems m (phF F ph) (defers0 m)

/-- The model's frame in memory `m` (at `msp = F.sp - 96`). -/
structure FrameMem (m : Memory) (F : Frame) (mode : DeferMode) (ph : Nat) (x18 lr x29 : Nat) : Prop where
  w0 : m.readLE (F.sp - 96) 8 = F.sp
  w8 : m.readLE (F.sp - 96 + 8) 8 = F.bound
  w16 : m.readLE (F.sp - 96 + 16) 8 = F.resume
  w24 : m.readLE (F.sp - 96 + 24) 8 = modeCode mode
  w32 : m.readLE (F.sp - 96 + 32) 8 = ph
  w40 : ∀ ba sa, F.openAt = some (ba, sa) → m.readLE (F.sp - 96 + 40) 8 = ba ∧ m.readLE (F.sp - 96 + 48) 8 = sa
  w56 : m.readLE (F.sp - 96 + 56) 8 = x18
  w64 : mode = .ret → m.readLE (F.sp - 96 + 64) 8 = lr ∧ m.readLE (F.sp - 96 + 72) 8 = x29
  hph : ph ≠ 0 → F.openAt.isSome

/-! ### The open-coded step: the top `deferBits` bit -/

/-- The index the model's `clz` computes for a byte `b` (the symbolic form of `31 - clz32 b`). -/
def clzTop (b : Nat) : BitVec 64 := BitVec.setWidth 64
  (31#32 - BitVec.setWidth 32 (BitVec.setWidth 64
    (BitVec.ofNat 32 (clzNat 32 (BitVec.setWidth 32 (BitVec.ofNat 64 b)).toNat))))

/-- The highest set bit of a non-zero byte. -/
def topBit (b : Nat) : Nat := (openBits b).headD 0

set_option maxRecDepth 100000 in
theorem clzTop_eq : ∀ b, b < 256 → 0 < b → clzTop b = BitVec.ofNat 64 (topBit b) := by decide

/-- The byte the model stores back (`bic`: the top bit cleared). -/
def bicTop (b : Nat) : Nat := (BitVec.setWidth 64
  (BitVec.setWidth 32 (BitVec.ofNat 64 b) &&& ~~~BitVec.setWidth 32 (BitVec.setWidth 64
    (1#32 <<< ((BitVec.setWidth 32 (clzTop b)).toNat % 32))))).toNat

set_option maxRecDepth 100000 in
theorem bicTop_eq : ∀ b, b < 256 → 0 < b → bicTop b = b % 2 ^ topBit b := by decide

set_option maxRecDepth 100000 in
theorem openBits_top : ∀ b, b < 256 → 0 < b → openBits b = topBit b :: openBits (b % 2 ^ topBit b) := by decide

set_option maxRecDepth 100000 in
theorem openBits_mod_sub : ∀ b, b < 256 → 0 < b → ∀ i ∈ openBits (b % 2 ^ topBit b), i ∈ openBits b := by decide

/-- The byte the model stores back for index `i`. -/
def bicI (b i : Nat) : Nat := (BitVec.setWidth 64
  (BitVec.setWidth 32 (BitVec.ofNat 64 b) &&& ~~~BitVec.setWidth 32 (BitVec.setWidth 64
    (1#32 <<< ((BitVec.setWidth 32 (BitVec.ofNat 64 i)).toNat % 32))))).toNat

set_option maxRecDepth 100000 in
theorem bicI_eq : ∀ b, b < 256 → 0 < b → bicI b (topBit b) = b % 2 ^ topBit b := by decide

set_option maxRecDepth 100000 in
theorem topBit_lt : ∀ b, b < 256 → 0 < b → topBit b < 8 := by decide

set_option maxHeartbeats 0 in
/-- `LH` with open-coded defers pending: the model clears the top bit and calls the slot's closure. -/
theorem seg_open (c : State) (ba sa b fn : Nat) (hpc : c.pc = BitVec.ofNat 64 eLH)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : c.mem.accessible c.sp.toNat 96 true = true)
    (hph : c.mem.readLE (c.sp.toNat + 32) 8 ≠ 0) (hba : c.mem.readLE (c.sp.toNat + 40) 8 = ba)
    (hsa : c.mem.readLE (c.sp.toNat + 48) 8 = sa) (hb : c.mem.readLE ba 1 = b) (hb0 : 0 < b)
    (hba2 : ba + 1 ≤ 2 ^ 48) (hbaa : c.mem.accessible ba 1 true = true)
    (hsl : sa + 8 * topBit b + 8 ≤ 2 ^ 48) (hsla : c.mem.accessible (sa + 8 * topBit b) 8 false = true)
    (hfn : c.mem.readLE (sa + 8 * topBit b) 8 = fn)
    (hfa : fn + 8 ≤ 2 ^ 48) (hfaa : c.mem.accessible fn 8 false = true)
    (hbaf : c.sp.toNat + 96 ≤ ba) (hsld : sa + 8 * topBit b + 8 ≤ ba ∨ ba + 1 ≤ sa + 8 * topBit b)
    (hfd : fn + 8 ≤ ba ∨ ba + 1 ≤ fn) (hcw : c.mem.readLE fn 8 < 2 ^ 48) (hcw4 : c.mem.readLE fn 8 % 4 = 0) :
    ReachesRet qE (BitVec.ofNat 64 (c.mem.readLE fn 8)) c (fun e =>
      e.mem = c.mem.writeLE ba 1 (b % 2 ^ topBit b) ∧ e.sp = c.sp ∧ e.regs 26 = BitVec.ofNat 64 fn ∧
      e.regs 28 = c.regs 28 ∧ e.regs 18 = c.regs 18 ∧ e.regs 29 = c.sp - 8 ∧
      e.regs 30 = BitVec.ofNat 64 RPa) := by
  have hbl : b < 256 := by rw [← hb]; exact lt_of_lt_of_eq (Memory.readLE_lt _ _ 1) (by decide)
  have hci := clzTop_eq b hbl hb0
  unfold clzTop at hci
  have hbi := bicI_eq b hbl hb0
  unfold bicI at hbi
  have ht8 := topBit_lt b hbl hb0
  generalize topBit b = i at *
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  have hfn' : cm.readLE (sa + i * 8) 8 = fn := by rw [show sa + i * 8 = sa + 8 * i by omega]; exact hfn
  have hcw' : (cm.writeLE ba 1 (b % 2 ^ i)).readLE fn 8 = cm.readLE fn 8 :=
    cm.readLE_writeLE_of_disjoint _ (by omega)
  janus_run [hba, hsa, hb, hci, hbi, hfn', hcw']
  done

set_option maxHeartbeats 0 in
/-- `LH` with the open-coded defers done: the model clears the phase and loops. -/
theorem seg_torec (c : State) (ba : Nat) (hpc : c.pc = BitVec.ofNat 64 eLH)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : c.mem.accessible c.sp.toNat 96 true = true)
    (hph : c.mem.readLE (c.sp.toNat + 32) 8 ≠ 0) (hba : c.mem.readLE (c.sp.toNat + 40) 8 = ba)
    (hb : c.mem.readLE ba 1 = 0) (hba2 : ba + 1 ≤ 2 ^ 48) (hbaa : c.mem.accessible ba 1 true = true) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x2ec)) c (fun e => e.mem = c.mem.writeLE (c.sp.toNat + 32) 8 0 ∧
      e.sp = c.sp ∧ e.regs 28 = c.regs 28 ∧ e.regs 18 = c.regs 18) := by
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [hba, hb]

set_option maxHeartbeats 0 in
/-- The two `b LH` instructions (after `TOREC` and `POPREC`). -/
theorem seg_back (c : State) (h : c.pc = BitVec.ofNat 64 (E + 0x2ec) ∨ c.pc = BitVec.ofNat 64 (E + 0x358)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun e => e.mem = c.mem ∧ e.sp = c.sp ∧ e.regs = c.regs) := by
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at h ⊢
  rcases h with rfl | rfl <;> janus_run

/-- The memory after the model took funcval `n` off the top record `j` (converted, its count
decremented, popped when it was the last). -/
def recTake (m : Memory) (j n : Nat) : Memory :=
  if n = 0 then (((m.writeLE (j * 96 + 66064) 8 1).writeLE (j * 96 + 66072) 8 n).writeLE 65544 8 j)
  else (m.writeLE (j * 96 + 66064) 8 1).writeLE (j * 96 + 66072) 8 n

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with a funcval left in the frame's top record: the model takes it and
calls it. -/
theorem seg_rec_call (c : State) (j n fn : Nat) (hpc : c.pc = BitVec.ofNat 64 eLH)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : c.mem.accessible c.sp.toNat 96 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (c.sp.toNat + 32) 8 = 0) (hnd : ndef c.mem = j + 1) (hj : j < 8)
    (hrs : recSp c.mem j = c.mem.readLE c.sp.toNat 8) (hn : recN c.mem j = n + 1) (hn8 : n < 8)
    (hfn : recFn c.mem j n = fn) (hfa : fn + 8 ≤ 2 ^ 48)
    (hfaa : c.mem.accessible fn 8 false = true)
    (hcw : (recTake c.mem j n).readLE fn 8 < 2 ^ 48) (hcw4 : (recTake c.mem j n).readLE fn 8 % 4 = 0) :
    ReachesRet qE (BitVec.ofNat 64 ((recTake c.mem j n).readLE fn 8)) c (fun e =>
      e.mem = recTake c.mem j n ∧ e.sp = c.sp ∧ e.regs 26 = BitVec.ofNat 64 fn ∧
      e.regs 28 = c.regs 28 ∧ e.regs 18 = c.regs 18 ∧ e.regs 29 = c.sp - 8 ∧
      e.regs 30 = BitVec.ofNat 64 RPa) := by
  have hnd' : c.mem.readLE 65544 8 = j + 1 := hnd
  have hrs' : c.mem.readLE (j * 96 + 66048) 8 = c.mem.readLE c.sp.toNat 8 := by
    rw [← hrs]; simp only [recSp, rd, recAt, B]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
  have hn' : c.mem.readLE (j * 96 + 66072) 8 = n + 1 := by
    rw [← hn]; simp only [recN, rd, recAt, B]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
  have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hfn1 : c.mem.readLE (j * 96 + 66080 + 8 * n) 8 = fn := by
    rw [← hfn]; simp only [recFn, rd, recAt, B]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.mul_zero, Nat.add_zero] at hfn1
    simp only [recTake, if_true, ite_true] at *
    janus_run [hph, hnd', hrs', hn', hmul, hmul2, hfn1]
  · simp only [recTake, hn0, if_false] at hcw hcw4 ⊢
    janus_run [hph, hnd', hrs', hn', hmul, hmul2, hfn1]

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with an empty top record of the frame: the model pops it. -/
theorem seg_rec_pop (c : State) (j : Nat) (hpc : c.pc = BitVec.ofNat 64 eLH)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : c.mem.accessible c.sp.toNat 96 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (c.sp.toNat + 32) 8 = 0) (hnd : ndef c.mem = j + 1) (hj : j < 8)
    (hrs : recSp c.mem j = c.mem.readLE c.sp.toNat 8) (hn : recN c.mem j = 0) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x358)) c (fun e =>
      e.mem = ((c.mem.writeLE (j * 96 + 66064) 8 1).writeLE 65544 8 j) ∧ e.sp = c.sp ∧
      e.regs 28 = c.regs 28 ∧ e.regs 18 = c.regs 18) := by
  have hnd' : c.mem.readLE 65544 8 = j + 1 := hnd
  have hrs' : c.mem.readLE (j * 96 + 66048) 8 = c.mem.readLE c.sp.toNat 8 := by
    rw [← hrs]; simp only [recSp, rd, recAt, B]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
  have hn' : c.mem.readLE (j * 96 + 66072) 8 = 0 := by
    rw [← hn]; simp only [recN, rd, recAt, B]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
  have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [hph, hnd', hrs', hn', hmul, hmul2]

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with no record of the frame on top: the loop ends. A panic or
`Goexit` goes to the unwinding state (`RP` with `SP` the frame's entry `SP`); `deferreturn`
returns to its caller. -/
theorem seg_fin (c : State) (mode : DeferMode) (bound lr x29 : Nat) (hpc : c.pc = BitVec.ofNat 64 eLH)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : c.mem.accessible c.sp.toNat 96 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (c.sp.toNat + 32) 8 = 0)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ j < 8 ∧ recSp c.mem j ≠ c.mem.readLE c.sp.toNat 8)
    (hmode : c.mem.readLE (c.sp.toNat + 24) 8 = modeCode mode)
    (hbound : c.mem.readLE (c.sp.toNat + 8) 8 = bound) (hbd : bound < 2 ^ 64)
    (hlr : c.mem.readLE (c.sp.toNat + 64) 8 = lr) (hx29 : c.mem.readLE (c.sp.toNat + 72) 8 = x29)
    (hfsp : c.mem.readLE c.sp.toNat 8 < 2 ^ 64) (hlrb : mode = .ret → lr % 4 = 0 ∧ lr < 2 ^ 48) :
    ReachesRet qE (if mode = .ret then BitVec.ofNat 64 lr else BitVec.ofNat 64 RPa) c (fun d =>
      d.mem = c.mem ∧ d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧
      (if mode = .ret then d.sp = BitVec.ofNat 64 (c.mem.readLE c.sp.toNat 8) ∧ d.regs 29 = BitVec.ofNat 64 x29
       else d.sp = BitVec.ofNat 64 bound)) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  rcases hend with hend | ⟨j, hnd, hj, hrs⟩
  · have hnd' : cm.readLE 65544 8 = 0 := hend
    cases mode
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus_run [hph, hnd', hmode, hbound]
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus_run [hph, hnd', hmode, hbound]
    · obtain ⟨hl4, hl48⟩ := hlrb rfl
      simp only [modeCode] at hmode; simp only [reduceIte]
      janus_run [hph, hnd', hmode, hlr, hx29]
  · have hnd' : cm.readLE 65544 8 = j + 1 := hnd
    have hrs' : ¬ cm.readLE (j * 96 + 66048) 8 = cm.readLE (BitVec.toNat csp) 8 := by
      intro h; apply hrs; simp only [recSp, rd, recAt, B]; rw [← h]; exact congrArg (Janus.Arm64.Memory.readLE _ · 8) (by omega)
    have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    cases mode
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus_run [hph, hnd', hmode, hbound, hmul, hmul2]
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus_run [hph, hnd', hmode, hbound, hmul, hmul2]
    · obtain ⟨hl4, hl48⟩ := hlrb rfl
      simp only [modeCode] at hmode; simp only [reduceIte]
      janus_run [hph, hnd', hmode, hlr, hx29, hmul, hmul2]

set_option maxHeartbeats 0 in
/-- `RP` after a deferred call (or a nested panic) with nothing recovered: back to `LH`, `X18`
reloaded. -/
theorem seg_rp_lh (u : State) (x18 : Nat) (hpc : u.pc = BitVec.ofNat 64 RPa)
    (hal : u.sp.toNat % 16 = 0) (hsp : u.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : u.mem.accessible u.sp.toNat 96 true = true) (hB : u.mem.accessible B 0x1000 true = true)
    (h18 : u.mem.readLE (u.sp.toNat + 56) 8 = x18)
    (hcase : u.mem.readLE (u.sp.toNat + 24) 8 ≠ 0 ∨
      (u.mem.readLE (u.sp.toNat + 24) 8 = 0 ∧ ∃ k, npan u.mem = k + 1 ∧ k < 8 ∧
        rd u.mem (panAt k + 24) / 2 % 2 = 0)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) u (fun c => c.mem = u.mem ∧ c.sp = u.sp ∧
      c.regs 28 = u.regs 28 ∧ c.regs 18 = BitVec.ofNat 64 x18) := by
  have hB' : u.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := u
  dsimp only at *
  simp only [RPa, eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  rcases hcase with hm | ⟨hm, k, hk, hk8, hf⟩
  · janus_run [h18]
  · have hk' : cm.readLE 65536 8 = k + 1 := hk
    have hmul : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hsh : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.shiftLeft_eq]; omega
    have hf' : (BitVec.ofNat 64 (cm.readLE (65792 + (k * 32 + 24)) 8)).getLsbD 1 = false := by
      have : cm.readLE (65792 + (k * 32 + 24)) 8 / 2 % 2 = 0 := by
        rw [show 65792 + (k * 32 + 24) = 65792 + 32 * k + 24 by omega]; exact hf
      simp only [BitVec.getLsbD_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
      simp; omega
    janus_run [h18, hm, hk', hmul, hsh, hf']

/-! ### Recovery -/

/-- How many panic entries remain after dropping, from the top, those started at or below `fsp`. -/
def dropCount (m : Memory) (fsp : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if rd m (panAt k + 16) ≤ fsp then dropCount m fsp k else k + 1

theorem dropCount_le (m : Memory) (fsp : Nat) : ∀ k, dropCount m fsp k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    simp only [dropCount]; split
    · have := dropCount_le m fsp k; omega
    · exact Nat.le_refl _

theorem panList_dropCount (m : Memory) (fsp : Nat) : ∀ k,
    panList m (dropCount m fsp k) = (panList m k).dropWhile (·.start ≤ fsp)
  | 0 => rfl
  | k + 1 => by
    rw [panList_succ]
    simp only [dropCount, List.dropWhile_cons]
    have hs : (decPan m k).start = rd m (panAt k + 16) := rfl
    split
    · rename_i h; rw [hs, decide_eq_true h]; exact panList_dropCount m fsp k
    · rename_i h; rw [hs, decide_eq_false h]; rfl

theorem dropCount_w {m : Memory} {fsp v : Nat} : ∀ k, k ≤ 8 →
    dropCount (m.writeLE 65536 8 v) fsp k = dropCount m fsp k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [dropCount]
    rw [rd_w (by simp only [panAt, B]; omega), dropCount_w k (by omega)]

set_option maxHeartbeats 0 in
/-- The `DROP` loop. -/
theorem seg_drop (fsp : Nat) (hfsp : fsp < 2 ^ 64) : ∀ k (d : State), d.pc = BitVec.ofNat 64 (E + 0x394) →
    d.regs 6 = BitVec.ofNat 64 B → d.regs 1 = BitVec.ofNat 64 fsp → npan d.mem = k → k ≤ 8 →
    d.mem.accessible B 0x1000 true = true →
    ReachesRet qE (BitVec.ofNat 64 (E + 0x3bc)) d (fun d' => d'.sp = d.sp ∧ d'.regs 28 = d.regs 28 ∧
      d'.regs 18 = d.regs 18 ∧ d'.regs 6 = BitVec.ofNat 64 B ∧ d'.regs 1 = BitVec.ofNat 64 fsp ∧
      MemFrame d.mem d'.mem [(B, B + 8)] ∧ npan d'.mem = dropCount d.mem fsp k)
  | 0, d, hpc, h6, h1, hk, _, hB => by
    have hk' : d.mem.readLE 65536 8 = 0 := hk
    have hB' : d.mem.accessible 65536 4096 true = true := hB
    obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := d
    dsimp only at *
    simp only [E, B, Nat.reduceAdd] at hpc h6 ⊢
    subst hpc
    janus_run [hk', h6, h1]
    exact ⟨MemFrame.refl _ _, rfl⟩
  | k + 1, d, hpc, h6, h1, hk, hk8, hB => by
    have hk' : d.mem.readLE 65536 8 = k + 1 := hk
    have hB' : d.mem.accessible 65536 4096 true = true := hB
    have hmul : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hsh : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.shiftLeft_eq]; omega
    by_cases hs : rd d.mem (panAt k + 16) ≤ fsp
    · -- pop and loop
      have hs' : d.mem.readLE (65792 + (k * 32 + 16)) 8 ≤ fsp := by
        rw [show 65792 + (k * 32 + 16) = panAt k + 16 by simp [panAt, B]; omega]; exact hs
      have ih := seg_drop fsp hfsp k
      obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := d
      dsimp only at *
      simp only [E, B, Nat.reduceAdd] at hpc h6 ⊢
      subst hpc
      janus_run [hk', h6, h1, hmul, hsh, hs'] until [0x300394]
      refine reachesRet_mono (ih _ rfl (by simp [setReg, h6]) (by simp [setReg, h1])
        (by show (cm.writeLE 65536 8 k).readLE 65536 8 = k; rw [Memory.readLE_writeLE_self]
            exact Nat.mod_eq_of_lt (by omega)) (by omega) (by simpa using hB)) ?_
      rintro d' ⟨h1', h2', h3', h4', h5', h6', h7'⟩
      refine ⟨h1', by simpa [setReg] using h2', by simpa [setReg] using h3', h4', h5', ?_, ?_⟩
      · exact (MemFrame.of_writeLE cm k (List.mem_singleton.2 rfl) (by simp) (by simp)).trans h6'
          fun a n h => ⟨h, h⟩
      · rw [h7', dropCount_w k (by omega)]
        simp only [dropCount, if_pos hs]
    · have hs' : ¬ d.mem.readLE (65792 + (k * 32 + 16)) 8 ≤ fsp := by
        rw [show 65792 + (k * 32 + 16) = panAt k + 16 by simp [panAt, B]; omega]; exact hs
      obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := d
      dsimp only at *
      simp only [E, B, Nat.reduceAdd] at hpc h6 ⊢
      subst hpc
      janus_run [hk', h6, h1, hmul, hsh, hs']
      refine ⟨MemFrame.refl _ _, ?_⟩
      simp only [dropCount, if_neg hs]

set_option maxHeartbeats 0 in
/-- After `DROP`: the model records the open-coded defers still pending (`saved`) and resumes the
frame at its `deferreturn` call. -/
theorem seg_dropped (d : State) (fsp resume ph ba sa : Nat) (hpc : d.pc = BitVec.ofNat 64 (E + 0x3bc))
    (h6 : d.regs 6 = BitVec.ofNat 64 B) (h1 : d.regs 1 = BitVec.ofNat 64 fsp)
    (hal : d.sp.toNat % 16 = 0) (hsp : d.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : d.mem.accessible d.sp.toNat 96 true = true) (hB : d.mem.accessible B 0x1000 true = true)
    (hres : d.mem.readLE (d.sp.toNat + 16) 8 = resume) (hres4 : resume % 4 = 0) (hres48 : resume < 2 ^ 48)
    (hph : d.mem.readLE (d.sp.toNat + 32) 8 = ph) (hba : d.mem.readLE (d.sp.toNat + 40) 8 = ba)
    (hsa : d.mem.readLE (d.sp.toNat + 48) 8 = sa)
    (hbaa : ph ≠ 0 → ba + 1 ≤ 2 ^ 48 ∧ d.mem.accessible ba 1 false = true ∧ (ba + 1 ≤ B ∨ B + 0x1000 ≤ ba))
    (hfsp : fsp < 2 ^ 64) (hph64 : ph < 2 ^ 64) (hsa64 : sa < 2 ^ 64) (hbyte : d.mem.readLE ba 1 < 256) (hspB : d.sp.toNat + 96 ≤ B ∨ B + 0x1000 ≤ d.sp.toNat) :
    ReachesRet qE (BitVec.ofNat 64 resume) d (fun d' => d'.sp = BitVec.ofNat 64 fsp ∧
      d'.regs 29 = d'.sp - 8 ∧ d'.regs 28 = d.regs 28 ∧ d'.regs 18 = d.regs 18 ∧
      MemFrame d.mem d'.mem [(B + 0x10, B + 0x28)] ∧
      (if ph ≠ 0 ∧ d.mem.readLE ba 1 ≠ 0 then
        rd d'.mem (B + 0x10) = 1 ∧ rd d'.mem (B + 0x18) = ba ∧ rd d'.mem (B + 0x20) = sa
       else rd d'.mem (B + 0x10) = 0)) := by
  have hB' : d.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := d
  dsimp only at *
  simp only [E, B, Nat.reduceAdd] at hpc h6 hspB hbaa ⊢
  subst hpc
  by_cases hp0 : ph = 0
  · subst hp0
    janus_run [h6, h1, hres, hph]
    repeat' (first | janus_frame | with_reducible apply And.intro)
    all_goals (first | (simp_all; done) | skip)
  · obtain ⟨hb1, hb2, hb3⟩ := hbaa hp0
    by_cases hbz : cm.readLE ba 1 = 0
    · janus_run [h6, h1, hres, hph, hba, hsa, hbz]
      repeat' (first | janus_frame | with_reducible apply And.intro)
      all_goals (first | (simp_all; done) | skip)
    · janus_run [h6, h1, hres, hph, hba, hsa]
      repeat' (first | janus_frame | with_reducible apply And.intro)
      all_goals (first | (simp_all; done) | skip)

end Janus.Contracts.PanicSat

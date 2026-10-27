import Janus.Contracts.PanicSatAmd64
import Janus.Contracts.PanicSatDecode

/-!
# The amd64 panic model engine's loop

The steps of the loop head `LH` of the amd64 model engine (`docs/model/panic_model_amd64.s`), each a
`ReachesRet` of the engine alone, and the recovery (`DROP`) loop: the x86-64 twin of
`Janus.Contracts.PanicSatLoop`. The engine's frame (96 bytes at `msp = RSP`, the frame's `SP` being
`msp + 104`) holds `F.sp`, `F.bound`, `F.resume`, the mode, the phase, the `deferBits` and slot
addresses; a deferred call is a `CALL` (so the closure's `RSP` is `msp - 8`, its return address
`RPa`), and a nested panic leaving the closure resumes `RP` at `bound + 8 = msp`.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Contracts.Panic (DeferMode Frame Item)
open Janus.Contracts.PanicSat (modeCode phF curItems FrameMem clzTop topBit bicTop clzTop_eq bicTop_eq openBits_top openBits_mod_sub bicI bicI_eq topBit_lt recTake dropCount dropCount_le panList_dropCount dropCount_w)

set_option maxRecDepth 100000 in
theorem nz8 : ∀ b, b < 256 → 0 < b →
    ¬ BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b))) = 0#32 := by decide

set_option maxRecDepth 100000 in
theorem bsrTop_eq : ∀ b, b < 256 → 0 < b →
    (31 - Arm64.clzNat 32 (b % 256 % 4294967296)) % 4294967296 = topBit b := by decide

set_option maxRecDepth 100000 in
theorem btrTop_eq : ∀ b, b < 256 → 0 < b →
    (b % 256 % 4294967296 &&& (~~~((2 ^ (topBit b % 32) : Nat) : BitVec 32)).toNat) % 256 = b % 2 ^ topBit b := by decide

theorem rl64 (m : Memory) (a : Nat) : m.readLE a 8 < 18446744073709551616 := by
  have := Janus.Arm64.Memory.readLE_lt m a 8; simpa using this

abbrev rsp (c : State) : Nat := (c.regs 4).toNat

set_option maxHeartbeats 0 in
theorem seg_open (c : State) (ba sa b fn : Nat) (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hal : rsp c % 8 = 0) (hsp : rsp c + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp c)
    (hacc : c.mem.accessible (rsp c - 8) 104 true = true)
    (hph : c.mem.readLE (rsp c + 32) 8 ≠ 0) (hba : c.mem.readLE (rsp c + 40) 8 = ba)
    (hsa : c.mem.readLE (rsp c + 48) 8 = sa) (hb : c.mem.readLE ba 1 = b) (hb0 : 0 < b)
    (hba2 : ba + 1 ≤ 2 ^ 48) (hbaa : c.mem.accessible ba 1 true = true)
    (hsl : sa + 8 * topBit b + 8 ≤ 2 ^ 48) (hsla : c.mem.accessible (sa + 8 * topBit b) 8 false = true)
    (hfn : c.mem.readLE (sa + 8 * topBit b) 8 = fn)
    (hfa : fn + 8 ≤ 2 ^ 48) (hfaa : c.mem.accessible fn 8 false = true)
    (hbaf : rsp c + 96 ≤ ba) (hsld : sa + 8 * topBit b + 8 ≤ ba ∨ ba + 1 ≤ sa + 8 * topBit b)
    (hfd : fn + 8 ≤ ba ∨ ba + 1 ≤ fn) (hcw : c.mem.readLE fn 8 < 2 ^ 47) :
    ReachesRet qE (BitVec.ofNat 64 (c.mem.readLE fn 8)) c (fun e =>
      e.mem = (c.mem.writeLE ba 1 (b % 2 ^ topBit b)).writeLE (rsp c - 8) 8 RPa ∧
      e.regs 4 = c.regs 4 - 8 ∧ e.regs 2 = BitVec.ofNat 64 fn ∧ e.regs 14 = c.regs 14 ∧
      e.regs 5 = c.regs 5 ∧ e.xmm 15 = c.xmm 15 ∧ e.df = c.df) := by
  have hbl : b < 256 := by rw [← hb]; exact lt_of_lt_of_eq (Janus.Arm64.Memory.readLE_lt _ _ 1) (by decide)
  have hb0' := hb0
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [rsp] at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  have hbne := nz8 b hbl hb0
  have hbs := bsrTop_eq b hbl hb0
  have hfn' : cm.readLE (sa + topBit b * 8) 8 = fn := by rw [show sa + topBit b * 8 = sa + 8 * topBit b by omega]; exact hfn
  have hcw' : (cm.writeLE ba 1 (b % 2 ^ topBit b)).readLE fn 8 = cm.readLE fn 8 :=
    cm.readLE_writeLE_of_disjoint _ (by omega)
  janus64_run [hba, hsa, hb, hbne, hbs, hfn', hcw']
  rw [btrTop_eq b hbl hb0]

/-- The registers the model engine leaves alone. -/
def Same (c e : State) : Prop :=
  e.regs 4 = c.regs 4 ∧ e.regs 5 = c.regs 5 ∧ e.regs 14 = c.regs 14 ∧ e.xmm 15 = c.xmm 15 ∧ e.df = c.df

set_option maxHeartbeats 0 in
theorem seg_torec (c : State) (ba : Nat) (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hal : rsp c % 8 = 0) (hsp : rsp c + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp c)
    (hacc : c.mem.accessible (rsp c - 8) 104 true = true)
    (hph : c.mem.readLE (rsp c + 32) 8 ≠ 0) (hba : c.mem.readLE (rsp c + 40) 8 = ba)
    (hb : c.mem.readLE ba 1 = 0) (hba2 : ba + 1 ≤ 2 ^ 48) (hbaa : c.mem.accessible ba 1 true = true) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x317)) c (fun e => e.mem = c.mem.writeLE (rsp c + 32) 8 0 ∧
      Same c e) := by
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [rsp] at *
  simp only [eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  have hb' : cm.readLE ba 1 % 256 = 0 := by rw [hb]
  have hbz : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (cm.readLE ba 1)))) = 0#32 := by
    rw [hb]; decide
  janus64_run [hba, hb, hbz]
  unfold Same; simp [setRegF]

set_option maxHeartbeats 0 in
/-- The two `jmp LH` instructions (after `TOREC` and `POPREC`). -/
theorem seg_back (c : State) (h : c.rip = BitVec.ofNat 64 (E + 0x317) ∨ c.rip = BitVec.ofNat 64 (E + 0x37e)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun e => e.mem = c.mem ∧ e.regs = c.regs ∧ e.xmm = c.xmm ∧ e.df = c.df) := by
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [eLH, E, Nat.reduceAdd] at h ⊢
  rcases h with rfl | rfl <;> janus64_run

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with a funcval left in the frame's top record: the model takes it and
calls it. -/
theorem seg_rec_call (c : State) (j n fn : Nat) (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hal : rsp c % 8 = 0) (hsp : rsp c + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp c)
    (hacc : c.mem.accessible (rsp c - 8) 104 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (rsp c + 32) 8 = 0) (hnd : ndef c.mem = j + 1) (hj : j < 8)
    (hrs : recSp c.mem j = c.mem.readLE (rsp c) 8) (hn : recN c.mem j = n + 1) (hn8 : n < 8)
    (hfn : recFn c.mem j n = fn) (hfa : fn + 8 ≤ 2 ^ 48)
    (hfaa : c.mem.accessible fn 8 false = true)
    (hcw : (recTake c.mem j n).readLE fn 8 < 2 ^ 47) :
    ReachesRet qE (BitVec.ofNat 64 ((recTake c.mem j n).readLE fn 8)) c (fun e =>
      e.mem = (recTake c.mem j n).writeLE (rsp c - 8) 8 RPa ∧
      e.regs 4 = c.regs 4 - 8 ∧ e.regs 2 = BitVec.ofNat 64 fn ∧ e.regs 14 = c.regs 14 ∧
      e.regs 5 = c.regs 5 ∧ e.xmm 15 = c.xmm 15 ∧ e.df = c.df) := by
  have hnd' : c.mem.readLE 65544 8 = j + 1 := hnd
  have hrs' : c.mem.readLE (j * 96 + 66048) 8 = c.mem.readLE (rsp c) 8 := by
    rw [← hrs]; simp only [recSp, rd, recAt, B]; congr 1; omega
  have hn' : c.mem.readLE (j * 96 + 66072) 8 = n + 1 := by
    rw [← hn]; simp only [recN, rd, recAt, B]; congr 1; omega
  have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hfn1 : c.mem.readLE (j * 96 + 66080 + 8 * n) 8 = fn := by
    rw [← hfn]; simp only [recFn, rd, recAt, B]; congr 1; omega
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [rsp] at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.mul_zero, Nat.add_zero] at hfn1
    simp only [recTake, if_true, ite_true] at *
    janus64_run [hph, hnd', hrs', hn', hmul, hmul2, hfn1]
  · simp only [recTake, hn0, if_false] at hcw ⊢
    have hfn2 : cm.readLE (j * 96 + 66048 + n * 8 + 32) 8 = fn := by
      rw [← hfn1]; congr 1; omega
    janus64_run [hph, hnd', hrs', hn', hmul, hmul2, hfn1, hfn2]

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with an empty top record of the frame: the model pops it. -/
theorem seg_rec_pop (c : State) (j : Nat) (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hal : rsp c % 8 = 0) (hsp : rsp c + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp c)
    (hacc : c.mem.accessible (rsp c - 8) 104 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (rsp c + 32) 8 = 0) (hnd : ndef c.mem = j + 1) (hj : j < 8)
    (hrs : recSp c.mem j = c.mem.readLE (rsp c) 8) (hn : recN c.mem j = 0) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x37e)) c (fun e =>
      e.mem = ((c.mem.writeLE (j * 96 + 66064) 8 1).writeLE 65544 8 j) ∧ Same c e) := by
  have hnd' : c.mem.readLE 65544 8 = j + 1 := hnd
  have hrs' : c.mem.readLE (j * 96 + 66048) 8 = c.mem.readLE (rsp c) 8 := by
    rw [← hrs]; simp only [recSp, rd, recAt, B]; congr 1; omega
  have hn' : c.mem.readLE (j * 96 + 66072) 8 = 0 := by
    rw [← hn]; simp only [recN, rd, recAt, B]; congr 1; omega
  have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [rsp] at *
  simp only [eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus64_run [hph, hnd', hrs', hn', hmul, hmul2]
  unfold Same; simp [setRegF]

set_option maxHeartbeats 0 in
/-- `LH` in the record phase with no record of the frame on top: the loop ends. A panic or
`Goexit` goes to the unwinding state (`RP` with `RSP` the frame's entry `RSP` + 8); `deferreturn`
returns to its caller. -/
theorem seg_fin (c : State) (mode : DeferMode) (bound : Nat) (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hal : rsp c % 8 = 0) (hsp : rsp c + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp c)
    (hacc : c.mem.accessible (rsp c - 8) 104 true = true) (hB : c.mem.accessible B 0x1000 true = true)
    (hph : c.mem.readLE (rsp c + 32) 8 = 0)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ j < 8 ∧ recSp c.mem j ≠ c.mem.readLE (rsp c) 8)
    (hmode : c.mem.readLE (rsp c + 24) 8 = modeCode mode)
    (hbound : c.mem.readLE (rsp c + 8) 8 = bound) (hbd : bound + 8 < 2 ^ 64)
    (hlrb : mode = .ret → c.mem.readLE (rsp c + 96) 8 < 2 ^ 47 ∧ c.mem.accessible (rsp c + 96) 8 false = true) :
    ReachesRet qE (if mode = .ret then BitVec.ofNat 64 (c.mem.readLE (rsp c + 96) 8) else BitVec.ofNat 64 RPa) c
      (fun d => d.mem = c.mem ∧ d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧ d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧
      (if mode = .ret then d.regs 4 = c.regs 4 + 104#64 else d.regs 4 = BitVec.ofNat 64 (bound + 8))) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := c
  dsimp only at *
  simp only [rsp] at *
  simp only [eLH, E, Nat.reduceAdd] at hpc
  subst hpc
  have hb8 : BitVec.ofNat 64 bound + 8#64 = BitVec.ofNat 64 (bound + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hxl := rl64 cm (BitVec.toNat (cr 4))
  rcases hend with hend | ⟨j, hnd, hj, hrs⟩
  · have hnd' : cm.readLE 65544 8 = 0 := hend
    cases mode
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus64_run [hph, hnd', hmode, hbound]
      exact hb8
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus64_run [hph, hnd', hmode, hbound]
      exact hb8
    · obtain ⟨hl, hla⟩ := hlrb rfl
      simp only [modeCode] at hmode; simp only [reduceIte]
      janus64_run [hph, hnd', hmode]
  · have hnd' : cm.readLE 65544 8 = j + 1 := hnd
    have hrs' : ¬ cm.readLE (j * 96 + 66048) 8 = cm.readLE (BitVec.toNat (cr 4)) 8 := by
      intro h; apply hrs; simp only [recSp, rd, recAt, B]; rw [← h]; congr 1; omega
    have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    have hyl := rl64 cm (j * 96 + 66048)
    cases mode
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus64_run [hph, hnd', hmode, hbound, hmul, hmul2, hrs']
      exact hb8
    · simp only [modeCode] at hmode; simp only [reduceIte, reduceCtorEq]
      janus64_run [hph, hnd', hmode, hbound, hmul, hmul2, hrs']
      exact hb8
    · obtain ⟨hl, hla⟩ := hlrb rfl
      simp only [modeCode] at hmode; simp only [reduceIte]
      janus64_run [hph, hnd', hmode, hmul, hmul2, hrs']

theorem and2 (v : Nat) (h : v / 2 % 2 = 0) : BitVec.setWidth 32 (BitVec.ofNat 64 v) &&& 2#32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  show (v % 2 ^ 64 % 2 ^ 32) &&& 2 = 0
  have h1 : (v % 2 ^ 64 % 2 ^ 32) / 2 % 2 = 0 := by omega
  have h0 : Nat.testBit (v % 2 ^ 64 % 2 ^ 32) 1 = false := by
    rw [Nat.testBit_succ, Nat.testBit_zero]; simp [Nat.shiftRight_eq_div_pow]; omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have h2 : (2 : Nat) = 2 ^ 1 := rfl
  rw [h2, Nat.testBit_two_pow]
  by_cases hi : 1 = i
  · subst hi; rw [h0]; simp
  · simp [hi]

set_option maxHeartbeats 0 in
/-- `RP` after a deferred call (or a nested panic) with nothing recovered: back to `LH`. -/
theorem seg_rp_lh (u : State) (hpc : u.rip = BitVec.ofNat 64 RPa)
    (hal : rsp u % 8 = 0) (hsp : rsp u + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp u)
    (hacc : u.mem.accessible (rsp u - 8) 104 true = true) (hB : u.mem.accessible B 0x1000 true = true)
    (hcase : u.mem.readLE (rsp u + 24) 8 ≠ 0 ∨
      (u.mem.readLE (rsp u + 24) 8 = 0 ∧ ∃ k, npan u.mem = k + 1 ∧ k < 8 ∧
        rd u.mem (panAt k + 24) / 2 % 2 = 0)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) u (fun c => c.mem = u.mem ∧ Same u c) := by
  have hB' : u.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := u
  dsimp only at *
  simp only [rsp] at *
  simp only [RPa, eLH, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  rcases hcase with hm | ⟨hm, k, hk, hk8, hf⟩
  · janus64_run
    unfold Same; simp [setRegF]
  · have hk' : cm.readLE 65536 8 = k + 1 := hk
    have hmul : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hsh : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.shiftLeft_eq]; omega
    have hf' : cm.readLE (65792 + 32 * k + 24) 8 / 2 % 2 = 0 := hf
    have hf2 := and2 _ hf'
    janus64_run [hm, hk', hmul, hsh, hf2]
    unfold Same; simp [setRegF]

theorem and2' (v : Nat) (h : v / 2 % 2 = 1) : ¬ BitVec.setWidth 32 (BitVec.ofNat 64 v) &&& 2#32 = 0#32 := by
  intro hz
  have := congrArg BitVec.toNat hz
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  change (v % 2 ^ 64 % 2 ^ 32) &&& 2 = 0 at this
  have h0 := congrArg (fun x => Nat.testBit x 1) this
  simp only [Nat.testBit_and] at h0
  have h2 : (2 : Nat) = 2 ^ 1 := rfl
  rw [h2, Nat.testBit_two_pow] at h0
  simp at h0
  rw [Nat.testBit_succ, Nat.testBit_zero] at h0
  simp [Nat.shiftRight_eq_div_pow] at h0
  omega

set_option maxHeartbeats 0 in
/-- `RP` after a deferred call that recovered the panic: down to the start of `DROP`. -/
theorem seg_rp_rec (u : State) (k : Nat) (hpc : u.rip = BitVec.ofNat 64 RPa)
    (hal : rsp u % 8 = 0) (hsp : rsp u + 104 ≤ 2 ^ 48) (h8 : 8 ≤ rsp u)
    (hacc : u.mem.accessible (rsp u - 8) 104 true = true) (hB : u.mem.accessible B 0x1000 true = true)
    (hmode : u.mem.readLE (rsp u + 24) 8 = 0)
    (hk : npan u.mem = k + 1) (hk8 : k < 8) (hf : rd u.mem (panAt k + 24) / 2 % 2 = 1) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x3c8)) u (fun d => d.mem = u.mem ∧ Same u d ∧
      d.regs 8 = BitVec.ofNat 64 B ∧ d.regs 6 = BitVec.ofNat 64 (u.mem.readLE (rsp u) 8)) := by
  have hB' : u.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := u
  dsimp only at *
  simp only [rsp] at *
  simp only [RPa, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  have hk' : cm.readLE 65536 8 = k + 1 := hk
  have hmul : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hsh : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq]; omega
  have hf' : cm.readLE (65792 + 32 * k + 24) 8 / 2 % 2 = 1 := hf
  have hf2 := and2' _ hf'
  janus64_run [hmode, hk', hmul, hsh, hf2]
  unfold Same; simp [setRegF, B]

set_option maxHeartbeats 0 in
/-- The `DROP` loop. -/
theorem seg_drop (fsp : Nat) (hfsp : fsp < 2 ^ 64) : ∀ k (d : State), d.rip = BitVec.ofNat 64 (E + 0x3c8) →
    d.regs 8 = BitVec.ofNat 64 B → d.regs 6 = BitVec.ofNat 64 fsp → npan d.mem = k → k ≤ 8 →
    d.mem.accessible B 0x1000 true = true →
    ReachesRet qE (BitVec.ofNat 64 (E + 0x3f3)) d (fun d' => Same d d' ∧
      d'.regs 8 = BitVec.ofNat 64 B ∧ d'.regs 6 = BitVec.ofNat 64 fsp ∧
      MemFrame d.mem d'.mem [(B, B + 8)] ∧ npan d'.mem = dropCount d.mem fsp k)
  | 0, d, hpc, h8, h6, hk, _, hB => by
    have hk' : d.mem.readLE 65536 8 = 0 := hk
    have hB' : d.mem.accessible 65536 4096 true = true := hB
    obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := d
    dsimp only at *
    simp only [E, B, Nat.reduceAdd] at hpc h8 ⊢
    subst hpc
    janus64_run [hk', h8, h6]
    refine ⟨by unfold Same; simp [setRegF], MemFrame.refl _ _, rfl⟩
  | k + 1, d, hpc, h8, h6, hk, hk8, hB => by
    have hk' : d.mem.readLE 65536 8 = k + 1 := hk
    have hB' : d.mem.accessible 65536 4096 true = true := hB
    have hmul : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
    have hsh : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.shiftLeft_eq]; omega
    have hyl := rl64 d.mem (65792 + 32 * k + 16)
    by_cases hs : rd d.mem (panAt k + 16) ≤ fsp
    · have hs' : d.mem.readLE (65792 + 32 * k + 16) 8 ≤ fsp := by
        rw [show 65792 + 32 * k + 16 = panAt k + 16 by simp [panAt, B]]; exact hs
      have ih := seg_drop fsp hfsp k
      obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := d
      dsimp only at *
      simp only [E, B, Nat.reduceAdd] at hpc h8 ⊢
      subst hpc
      janus64_run [hk', h8, h6, hmul, hsh, hs'] until [0x3003c8]
      refine reachesRet_mono (ih _ rfl (by simp [setRegF, h8]) (by simp [setRegF, h6])
        (by show (cm.writeLE 65536 8 k).readLE 65536 8 = k; rw [Janus.Arm64.Memory.readLE_writeLE_self]
            exact Nat.mod_eq_of_lt (by omega)) (by omega) (by simpa using hB)) ?_
      rintro d' ⟨h1', h2', h3', h4', h5'⟩
      refine ⟨?_, h2', h3', ?_, ?_⟩
      · unfold Same at h1' ⊢; simpa [setRegF] using h1'
      · exact (MemFrame.of_writeLE cm k (List.mem_singleton.2 rfl) (by simp) (by simp)).trans h4'
          fun a n h => ⟨h, h⟩
      · rw [h5', Janus.Contracts.PanicSat.dropCount_w k (by omega)]
        simp only [dropCount, if_pos hs]
    · have hs' : ¬ d.mem.readLE (65792 + 32 * k + 16) 8 ≤ fsp := by
        rw [show 65792 + 32 * k + 16 = panAt k + 16 by simp [panAt, B]]; exact hs
      obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := d
      dsimp only at *
      simp only [E, B, Nat.reduceAdd] at hpc h8 ⊢
      subst hpc
      janus64_run [hk', h8, h6, hmul, hsh, hs']
      refine ⟨by unfold Same; simp [setRegF], MemFrame.refl _ _, ?_⟩
      simp only [dropCount, if_neg hs]

set_option maxHeartbeats 0 in
/-- After `DROP`: the model records the open-coded defers still pending (`saved`) and resumes the
frame at its `deferreturn` call. -/
theorem seg_dropped (d : State) (fsp bound resume ph ba sa : Nat) (hpc : d.rip = BitVec.ofNat 64 (E + 0x3f3))
    (h8 : d.regs 8 = BitVec.ofNat 64 B) (h6 : d.regs 6 = BitVec.ofNat 64 fsp)
    (hal : rsp d % 8 = 0) (hsp : rsp d + 104 ≤ 2 ^ 48) (h8' : 8 ≤ rsp d)
    (hacc : d.mem.accessible (rsp d - 8) 104 true = true) (hB : d.mem.accessible B 0x1000 true = true)
    (hres : d.mem.readLE (rsp d + 16) 8 = resume) (hres48 : resume < 2 ^ 47)
    (hbd : d.mem.readLE (rsp d + 8) 8 = bound) (hbd8 : 8 ≤ bound) (hbd64 : bound < 2 ^ 64)
    (hph : d.mem.readLE (rsp d + 32) 8 = ph) (hba : d.mem.readLE (rsp d + 40) 8 = ba)
    (hsa : d.mem.readLE (rsp d + 48) 8 = sa)
    (hbaa : ph ≠ 0 → ba + 1 ≤ 2 ^ 48 ∧ d.mem.accessible ba 1 false = true ∧ (ba + 1 ≤ B ∨ B + 0x1000 ≤ ba))
    (hfsp : fsp < 2 ^ 64) (hph64 : ph < 2 ^ 64) (hsa64 : sa < 2 ^ 64) (hbyte : d.mem.readLE ba 1 < 256)
    (hspB : rsp d + 104 ≤ B ∨ B + 0x1000 ≤ rsp d) :
    ReachesRet qE (BitVec.ofNat 64 resume) d (fun d' => d'.regs 4 = BitVec.ofNat 64 fsp ∧
      d'.regs 5 = BitVec.ofNat 64 (bound - 8) ∧ d'.regs 14 = d.regs 14 ∧ d'.xmm 15 = d.xmm 15 ∧ d'.df = d.df ∧
      MemFrame d.mem d'.mem [(B + 0x10, B + 0x28)] ∧
      (if ph ≠ 0 ∧ d.mem.readLE ba 1 ≠ 0 then
        rd d'.mem (B + 0x10) = 1 ∧ rd d'.mem (B + 0x18) = ba ∧ rd d'.mem (B + 0x20) = sa
       else rd d'.mem (B + 0x10) = 0)) := by
  have hB' : d.mem.accessible 65536 4096 true = true := hB
  have hb8 : BitVec.ofNat 64 bound - 8#64 = BitVec.ofNat 64 (bound - 8) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨cr, cpc, cfl, cx, cm, cy, cfs, cdf, cmx⟩ := d
  dsimp only at *
  simp only [rsp] at *
  simp only [E, B, Nat.reduceAdd] at hpc h8 hspB hbaa ⊢
  subst hpc
  by_cases hp0 : ph = 0
  · subst hp0
    janus64_run [h8, h6, hres, hph, hbd, hb8]
    repeat' (first | janus_frame | with_reducible apply And.intro)
    all_goals (first | (simp_all; done) | skip)
  · obtain ⟨hb1, hb2, hb3⟩ := hbaa hp0
    by_cases hbz : cm.readLE ba 1 = 0
    · have hbzv : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (cm.readLE ba 1)))) = 0#32 := by
        rw [hbz]; decide
      janus64_run [h8, h6, hres, hph, hbd, hb8, hba, hsa, hbz, hbzv]
      repeat' (first | janus_frame | with_reducible apply And.intro)
      all_goals (first | (simp_all; done) | skip)
    · have hbnz := nz8 (cm.readLE ba 1) hbyte (by omega)
      janus64_run [h8, h6, hres, hph, hbd, hb8, hba, hsa, hbnz]
      repeat' (first | janus_frame | with_reducible apply And.intro)
      all_goals (first | (simp_all; done) | skip)

end Janus.Contracts.PanicSatAmd64

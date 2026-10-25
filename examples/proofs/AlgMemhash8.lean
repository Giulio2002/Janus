import Extracted

/-!
# `runtime.memhash8` meets the `MemhashN … H d 1` contract

**Guarantee.** For every hash model `H` satisfying its laws, all stack bounds `d'` (the callee's) and `d` with
`8 ≤ d'` and `d' + 48 ≤ d`, and every code at `runtime.memhash`'s address that meets the `Memhash`
contract with bound `d'`, the machine code of Go 1.26's `runtime.memhash8(p, h)` satisfies
`Janus.Contracts.Hash.MemhashN … H d 1`: it returns `H.mem h 1 v` for the byte `v` at `p`, keeps
`SP`, `X18`, `X28`, `X29`, `FPCR`, changes memory only in `H.priv` and its window, and `H.Env`
holds again.

**What the code does.** The stack check, a 48-byte frame (`X30` at `SP - 48`, `X29` at `SP - 56`), `X2 = 1`,
`CALL runtime.memhash`, the epilogue. The callee runs at `SP - 48`; its window
`[SP - 48 - d', SP - 56)` and spill slots `[SP - 40, SP - 16)` lie inside the caller's.

**Assumptions.** `H.Laws` (the environment survives the frame pushes, which are outside `H.priv`) and the
`Memhash` contract of the callee; nothing about how `memhash` hashes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash

namespace Proof

/-! ## Calls from a frame (arm64)

The function pushes its frame record (`X30` at `SP - F`, `X29` at `SP - F - 8`) and calls a
callee with `SP - F`. These lemmas move the contract's precondition at the entry `s` to the call
site `S` (`EqPre`/`HPre` for the callee's bound `d'` with `d' + F ≤ d`), and the callee's frame
back to the caller's. -/

/-- A range inside `rs` and a range outside `rs` are apart. -/
theorem inRanges_apart {a k b j : Nat} {rs : List (Nat × Nat)} (hi : InRanges a k rs)
    (ho : Outside b j rs) : b + j ≤ a ∨ a + k ≤ b := by
  obtain ⟨r, hr, h1, h2⟩ := hi; have := MemFrame.outside_mem ho hr; omega

/-- The callee's window lies inside the caller's. -/
theorem sub_win {s S : State} {d n d' n' F : Nat} (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - F) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) {a k : Nat}
    (h : Outside a k (calleeStack s d n)) : Outside a k (calleeStack S d' n') := by
  simp only [calleeStack, outside_cons, outside_nil, and_true, hsp] at h ⊢
  omega

theorem eqPre_call {s S : State} {d n d' n' F : Nat} (hp : EqPre d n s) (hF : F % 16 = 0)
    (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hm : MemFrame s.mem S.mem (calleeStack s d n)) (hlr : (S.regs 30).toNat % 4 = 0)
    (hlr' : (S.regs 30).toNat < 2 ^ 48) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : EqPre d' n' S := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨l1, l2, al, dsp, d8, top, acc⟩, go⟩ := hp
  simp only [regG, stackguard0Offset, stackguard0] at g1 g2 g3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, sub_win hd dsp hsp hn (by rw [hg]; exact go)⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hm.accessible]; exact g2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp]
    rw [hm.readLE _ _ go]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hm.accessible]; exact Memory.accessible_mono _ acc (by omega) (by omega)

theorem hPre_call {H : HashModel} (hl : H.Laws) {s S : State} {d n d' n' F : Nat} (hp : HPre H d n s)
    (hF : F % 16 = 0) (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F)
    (hg : S.regs 28 = s.regs 28) (hm : MemFrame s.mem S.mem (calleeStack s d n))
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : HPre H d' n' S := by
  obtain ⟨he, hgd, hc, hout, go, gp⟩ := hp
  have hc' := hc
  obtain ⟨-, -, -, dsp, -, top, -⟩ := hc'
  obtain ⟨h1, h2, h3⟩ := eqPre_call ⟨hgd, hc, go⟩ hF hd hd8 hsp hg hm hlr hlr' hn
  refine ⟨?_, h1, h2, hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega), h3, by rw [hg]; exact gp⟩
  rw [hg]
  refine hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => ?_)
  have := inRanges_apart ha hout
  simp only [calleeStack, outside_cons, outside_nil, and_true]; omega

/-- The callee's frame (with the private ranges `P`) after the caller's frame pushes is the
caller's frame. -/
theorem frame_ret {s S : State} {m : Memory} {P : List (Nat × Nat)} {d n d' n' F : Nat}
    (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat) (hsp : S.sp.toNat = s.sp.toNat - F)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) (hm : MemFrame s.mem S.mem (calleeStack s d n))
    (h2 : MemFrame S.mem m (P ++ calleeStack S d' n')) : MemFrame s.mem m (P ++ calleeStack s d n) :=
  hm.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h.2, h.1, sub_win hd hd1 hsp hn h.2⟩

/-- An `EqRet`-shaped return whose memory keeps `H.Env` is an `HRet` return. -/
theorem hRet_intro {H : HashModel} {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hf : MemFrame s.mem s'.mem (H.priv ++ calleeStack s d nargs)) (he : H.Env s'.mem (s.regs 28))
    (hp : P s'.regs)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) : HRet H d nargs s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, ?_, hf, he, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 hex hep ⊢
  subst hsp hpc hdz htp hfc hex hep
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d d' : Nat)
    (hd' : 8 ≤ d') (hd : d' + 48 ≤ d)
    (hm : Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d') :
    MemhashN (Extracted.program.link impl) Extracted.entry H d 1 := by
  intro s hpc ⟨hpre, ⟨hi1, hi2, hi3⟩⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 48) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 56) 8 H.priv := hout.of_sub (by omega) (by omega)
  janus_run until [Extracted.program.contractAddr "runtime.memhash"]

  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  refine ReachesRet.call hm rfl ⟨hPre_call (F := 48) hl hpre (by decide) hd hd' hsp
    (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), ?_⟩ ?_
  · refine ⟨by simpa [setReg] using hi1, by simpa [setReg, hmf.accessible] using hi2, ?_⟩
    exact sub_win hd hd1 hsp (.inr (by decide)) hi3
  intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, henv, hres⟩
  subst hs'
  have hfr0 := hfr
  simp only [calleeStack, hsp] at hfr
  janus_run
  refine hRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
    (by simp [setReg]) rfl rfl rfl (frame_ret hd hd1 hsp (.inr (by decide)) hmf hfr0)
    (by simpa [setReg] using henv) ?_
  have hx := hmf.readLE _ _ hi3
  simp only [setReg_apply, Map.keepABI] at hres ⊢
  simp only [Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, hx] at hres ⊢
  simpa using hres


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.HashSat

/-- `runtime.memhash`'s address, with `HashSat.seedCode` (the hash is the seed, model `H0`)
placed there directly (it is straight-line). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memhash"
def seg : Segment := { name := "memhash", base := cAddr, words := seedCode }
def implAt : List Segment := [seg]

theorem model (d : Nat) : Memhash (Extracted.program.link implAt) cAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_eval_nat hC : cAddr
  rw [hC] at hpc
  janus_run
  exact seed_hRet he (by simp [setReg, seed_mod])

/-- The witness call state: `MemSat.wstate` (goroutine `wg`, stack `wsp`, return address `wret`,
memory `EqHashModel.wmem`) at the entry, with `memhash8(VAL, 7)`. -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 1 then 7 else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : HPre H0 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 1 := by
  refine ⟨⟨wmem_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [CallOK, Input, varlenSize, calleeStack, H0_priv, outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together: the model `H0` (its laws), the bounds
`d' = 16`, `d = 64`, the model code at `runtime.memhash`, and a call state. -/
theorem nonvacuous : ∃ (impl : List Segment) (H : HashModel) (d d' : Nat), H.Laws ∧ 8 ≤ d' ∧
    d' + 48 ≤ d ∧
    Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d' ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat 1) :=
  ⟨implAt, H0, 64, 16, H0_laws, by decide, by decide, model 16, s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns the contract's hash. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => HRet H0 64 2 s0 s' fun r => (r 0).toNat = H0.mem (s0.regs 1).toNat 1 (s0.mem.readLE (s0.regs 0).toNat 1)) :=
  correctness implAt H0 H0_laws 64 16 (by decide) (by decide) (model 16) s0 rfl pre

end Witness

end Proof

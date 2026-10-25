import Extracted

/-!
# `runtime.c128hash` meets the `Chash … binary64 8` contract

**Guarantee.** For every hash model `H` satisfying its laws, stack bounds with `8 ≤ d'` and `d' + 32 ≤ d`,
and every code at `runtime.f64hash` meeting `Fhash … H d' binary64 8`, the machine code of Go 1.26's
`runtime.c128hash(p, h)` satisfies `Janus.Contracts.Hash.Chash … H d binary64 8`: some `h1` is
`FHashIs` of the real part (at `p`) with seed `h`, and the result is `FHashIs` of the imaginary
part (at `p + 8`) with seed `h1`.

**What the code does.** A 32-byte frame; `p` is spilled to `40(RSP)` (`SP + 8`, the caller's spill slot), a nil check
reads its first byte, `f64hash(p, h)`, then `p` is reloaded and `f64hash(p + 8, h1)`. Between the
calls the first callee may change `H.priv`: the second call's guard word and the imaginary part
are outside `H.priv` (`HPre`, `Chash`), so they are read unchanged (`hPre_call2`).

**Assumptions.** `H.Laws` and the callee's `Fhash` contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash Janus.Float

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

/-- `EqPre` at a later call site whose memory has the same accessible ranges and the same guard
word as the entry's (a second call, after the first changed the runtime's memory). -/
theorem eqPre_call2 {s S : State} {d n d' n' F : Nat} (hp : EqPre d n s) (hF : F % 16 = 0)
    (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hacc : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w)
    (hgd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : EqPre d' n' S := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨l1, l2, al, dsp, d8, top, acc⟩, go⟩ := hp
  simp only [regG, stackguard0Offset, stackguard0] at g1 g2 g3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, sub_win hd dsp hsp hn (by rw [hg]; exact go)⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact g2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp, hgd]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Memory.accessible_mono _ acc (by omega) (by omega)

theorem hPre_call2 {H : HashModel} {s S : State} {d n d' n' F : Nat} (hp : HPre H d n s)
    (he : H.Env S.mem (S.regs 28)) (hF : F % 16 = 0) (hd : d' + F ≤ d) (hd8 : 8 ≤ d')
    (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hacc : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w)
    (hgd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : HPre H d' n' S := by
  obtain ⟨-, hgd0, hc, hout, go, gp⟩ := hp
  have hc' := hc
  obtain ⟨-, -, -, dsp, -, top, -⟩ := hc'
  obtain ⟨h1, h2, h3⟩ := eqPre_call2 ⟨hgd0, hc, go⟩ hF hd hd8 hsp hg hacc hgd hlr hlr' hn
  exact ⟨he, h1, h2, hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega), h3, by rw [hg]; exact gp⟩

theorem env_of_frame {H : HashModel} (hl : H.Laws) {s : State} {m : Memory} {g : W64} {d n : Nat}
    (he : H.Env s.mem g) (hout : Outside (s.sp.toNat - d) (d + 8 + 8 * n) H.priv)
    (hd1 : d ≤ s.sp.toNat) (hm : MemFrame s.mem m (calleeStack s d n)) : H.Env m g :=
  hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    have := inRanges_apart ha hout
    simp only [calleeStack, outside_cons, outside_nil, and_true]; omega)

set_option maxHeartbeats 2000000 in
theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d d' : Nat)
    (hd' : 8 ≤ d') (hd : d' + 32 ≤ d)
    (hf : Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d' binary64 8) :
    Chash (Extracted.program.link impl) Extracted.entry H d binary64 8 := by
  intro s hpc ⟨hpre, hfc, ⟨hi1, hi2, hi3⟩, hip⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 32) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 40) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho3 : Outside (s.sp.toNat + 8) 8 H.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem (((s.mem.writeLE (s.sp.toNat - 32) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 40) 8 (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat) (calleeStack s d 2) :=
    ((MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp) (by simp)
  have hi3' := hi3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at hi3'
  have hi4 : Outside (s.regs 0).toNat 8 (calleeStack s d 2) := hi3.of_sub (by omega) (by omega)
  have hi4' : Outside ((s.regs 0).toNat + 8) 8 (calleeStack s d 2) := hi3.of_sub (by omega) (by omega)
  have hip4' : Outside ((s.regs 0).toNat + 8) 8 H.priv := hip.of_sub (by omega) (by omega)
  janus_run until [Extracted.program.contractAddr "runtime.f64hash"]
  refine ReachesRet.call hf rfl ⟨hPre_call (F := 32) hl hpre (by decide) hd hd' hsp
    (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), rfl, ?_⟩ ?_
  · refine ⟨?_, ?_, sub_win hd hd1 hsp (.inr (by decide)) hi4⟩
    · simp only [setReg_apply, Nat.reduceEqDiff, reduceIte]; omega
    simp only [setReg_apply, Nat.reduceEqDiff, reduceIte]
    rw [hmf.accessible]; exact Memory.accessible_mono _ hi2 (Nat.le_refl _) (by omega)
  intro s1 hpc1 ⟨r1, v1, fl1, fs1, m1, hs1, hfr1, henv1, hres1⟩
  subst hs1
  have hfr1' := hfr1
  simp only [calleeStack, hsp] at hfr1
  janus_run until [Extracted.program.contractAddr "runtime.f64hash"]
  have hA4 : (s.regs 0 + 8#64).toNat = (s.regs 0).toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hacc : ∀ a k w, m1.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hfr1'.accessible, hmf.accessible]
  have hgd : m1.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hfr1'.readLE _ _ (by
      simp only [outside_append]
      exact ⟨by simpa [setReg] using hgp, sub_win hd hd1 hsp (.inr (by decide)) (by simpa [setReg] using hgo)⟩),
      hmf.readLE _ _ hgo]
  have hm1x : ∀ a k, Outside a k (H.priv ++ calleeStack s d 2) → m1.readLE a k = s.mem.readLE a k :=
    fun a k h => by
      simp only [outside_append] at h
      rw [hfr1'.readLE _ _ (by simp only [outside_append]; exact ⟨h.1, sub_win hd hd1 hsp (.inr (by decide)) h.2⟩),
        hmf.readLE _ _ h.2]
  refine ReachesRet.call hf rfl ⟨hPre_call2 (F := 32) hpre (by simpa [setReg, Map.keepABI] using henv1) (by decide) hd hd'
    hsp (by simp [setReg, Map.keepABI]) hacc hgd (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), rfl, ?_⟩ ?_
  · simp only [Input, setReg_apply, Nat.reduceEqDiff, reduceIte, hA4]
    refine ⟨by omega, ?_, sub_win hd hd1 hsp (.inr (by decide)) hi4'⟩
    rw [hacc]; exact Memory.accessible_mono _ hi2 (by omega) (by omega)
  intro s2 hpc2 ⟨r2, v2, fl2, fs2, m2, hs2, hfr2, henv2, hres2⟩
  subst hs2
  have hfr2' := hfr2
  simp only [calleeStack, hsp] at hfr2
  janus_run
  have hF1 : MemFrame s.mem m1 (H.priv ++ calleeStack s d 2) := hmf.trans hfr1' fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h.2, h.1, sub_win hd hd1 hsp (.inr (by decide)) h.2⟩
  have hF2 : MemFrame s.mem m2 (H.priv ++ calleeStack s d 2) := hF1.trans hfr2' fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h, h.1, sub_win hd hd1 hsp (.inr (by decide)) h.2⟩
  refine hRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
    (by simp [setReg]) rfl rfl hfc.symm hF2 (by simpa [setReg, Map.keepABI] using henv2) ?_
  refine ⟨(r1 0).toNat, ?_, ?_⟩
  · simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte] at hres1
    rw [hmf.readLE _ _ hi4] at hres1
    exact hres1
  · simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, hA4] at hres2 ⊢
    rw [hm1x _ _ (by simp only [outside_append]; exact ⟨hip4', hi4'⟩)] at hres2
    exact hres2


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.HashSat

/-- `HashSat.f64hashCode` (model `H0`) at `A0`, reached from `runtime.f64hash`'s address by a
branch. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.f64hash"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := f64hashCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model (d : Nat) : Fhash (Extracted.program.link implAt) cAddr H0 d binary64 8 := by
  have hA : Fhash (Extracted.program.link implAt) A0 H0 d binary64 8 := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (f64hash_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness call state: `MemSat.wstate` at the entry, with `c128hash(VAL, 7)`, `FPCR = 0`. -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 1 then 7 else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : HPre H0 64 2 s0 ∧ s0.fpcr = 0 ∧ Input s0 64 2 (s0.regs 0).toNat (2 * 8) ∧
    Outside (s0.regs 0).toNat (2 * 8) H0.priv := by
  refine ⟨⟨wmem_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, H0_priv, outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together (bounds `d' = 32`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (H : HashModel) (d d' : Nat), H.Laws ∧ 8 ≤ d' ∧
    d' + 32 ≤ d ∧
    Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d' binary64 8 ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧
      (HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat (2 * 8) ∧
        Outside (s.regs 0).toNat (2 * 8) H.priv) :=
  ⟨implAt, H0, 64, 32, H0_laws, by decide, by decide, model 32, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => HRet H0 64 2 s0 s' fun r => ∃ h1,
      FHashIs H0 binary64 8 (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 1).toNat h1 ∧
      FHashIs H0 binary64 8 (s0.mem.readLE ((s0.regs 0).toNat + 8) 8) h1 (r 0).toNat) :=
  correctness implAt H0 H0_laws 64 32 (by decide) (by decide) (model 32) s0 rfl pre

end Witness

end Proof

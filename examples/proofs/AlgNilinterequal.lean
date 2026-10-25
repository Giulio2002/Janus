import Extracted

/-!
# `runtime.nilinterequal` meets the `Nilinterequal` contract

**Guarantee.** For every interface model `R` satisfying its laws with `8 ≤ R.depth` and `R.depth + 48 ≤ d`, and
every code at `runtime.efaceeq`'s address meeting `Iface.Efaceeq` for `R`, the machine code of Go
1.26's `runtime.nilinterequal(a, b)` satisfies `Janus.Contracts.Mem.Nilinterequal … R d`: the low
byte of `X0` is `ta == tb && efaceEqual R m ta xa xb` of the `any` values at `a` and `b`, memory
changes only in `R.priv` and the window, and `R.Env` holds again.

**What the code does.** The stack check, a 48-byte frame, `LDP` of both values; different type words give `false`;
equal ones call `efaceeq(ta, xa, xb)` from `SP - 48`. The comparison is transported from the
call-site memory (after the frame pushes) to the entry's by `EqFrame` (the contract's frame
condition over the callee window).

**Assumptions.** `R.Laws`, `8 ≤ R.depth` (what `efaceeq`'s `CallOK` needs) and the callee's `Efaceeq` contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Mem Janus.Contracts.Iface

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

theorem rtPre_call {R : IfaceModel} (hl : R.Laws) {s S : State} {d F : Nat} (hp : IfacePre R d s)
    (hF : F % 16 = 0) (hd : R.depth + F ≤ d) (hd8 : 8 ≤ R.depth) (hsp : S.sp.toNat = s.sp.toNat - F)
    (hg : S.regs 28 = s.regs 28) (hm : MemFrame s.mem S.mem (calleeStack s d 2))
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hn : 16 + 8 * 3 ≤ F) :
    RTPre R 3 S := by
  obtain ⟨he, hgd, hc, hout, go⟩ := hp
  have hc' := hc
  obtain ⟨-, -, -, dsp, -, top, -⟩ := hc'
  obtain ⟨h1, h2, -⟩ := eqPre_call ⟨hgd, hc, go⟩ hF hd hd8 hsp hg hm hlr hlr' (.inr hn)
  refine ⟨?_, h1, h2, hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega)⟩
  rw [hg]
  refine hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => ?_)
  have := inRanges_apart ha hout
  simp only [calleeStack, outside_cons, outside_nil, and_true]; omega

theorem iRet_intro {R : IfaceModel} {d : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hf : MemFrame s.mem s'.mem (R.priv ++ calleeStack s d 2)) (he : R.Env s'.mem (s.regs 28))
    (hp : P s'.regs)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) : IfaceRet R d s s' P := by
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

theorem toNat_ofNat_readLE8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  have := m.readLE_lt a 8
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa using this)

theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (d : Nat)
    (hR : 8 ≤ R.depth) (hd : R.depth + 48 ≤ d)
    (he : Efaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.efaceeq") R) :
    Nilinterequal (Extracted.program.link impl) Extracted.entry R d := by
  intro s hpc ⟨hpre, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩, hok⟩
  have hpre' := hpre
  obtain ⟨henv, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, hgo⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 48) 8 R.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 56) 8 R.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  have ha3' := ha3
  have hb3' := hb3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at ha3' hb3'
  janus_run until [Extracted.program.contractAddr "runtime.efaceeq"]
  · have heq := hbr
    obtain ⟨hok1, hfrm⟩ := hok heq.symm
    refine ReachesRet.call he rfl ⟨rtPre_call (F := 48) hl hpre (by decide) hd hR hsp
      (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (by decide), ?_⟩ ?_
    · simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8]
      exact Iface.EqFrame.eqOK hfrm hok1 hmf
    intro s' hpc' ⟨r, v, fl, m, hs', hfr, henv, hres⟩
    subst hs'
    have hfr0 := hfr
    simp only [rtWrites, List.append_nil] at hfr0
    have hF : MemFrame s.mem m (R.priv ++ calleeStack s d 2) := hmf.trans hfr0 fun a k h => by
      simp only [outside_append] at h ⊢
      exact ⟨h.2, h.1, sub_win hd hd1 hsp (.inr (by decide)) h.2⟩
    simp only [rtWrites, List.append_nil, calleeStack, hsp] at hfr
    janus_run
    refine iRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
      (by simp [setReg]) rfl rfl rfl hF
      (by simpa [setReg] using henv) ?_
    simp only [BoolRes, heq, beq_self_eq_true, Bool.true_and]
    simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8] at hres ⊢
    rw [Iface.EqFrame.efaceEqual hfrm hmf] at hres
    rw [← heq] at hres ⊢
    exact hres
  · have hne : ¬ s.mem.readLE (s.regs 1).toNat 8 = s.mem.readLE (s.regs 0).toNat 8 := by
      assumption
    refine iRet_intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      (hmf.mono fun a k h => by simp only [outside_append] at h; exact h.2) ?_ ?_
    · exact hl.env_frame _ _ _ henv (Agrees.of_memFrame hmf fun a ha => by
        have := inRanges_apart ha hout
        simp only [calleeStack, outside_cons, outside_nil, and_true]; omega)
    have : (s.mem.readLE (s.regs 0).toNat 8 == s.mem.readLE (s.regs 1).toNat 8) = false :=
      beq_false_of_ne (fun h => hne h.symm)
    simp [BoolRes, setReg, this]


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MemSat

/-- `IfaceSat.efaceeqCode` (model `R0`) at `A0`, reached from `runtime.efaceeq`'s address by a
branch. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.efaceeq"
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := efaceeqCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : Iface.Efaceeq (Extracted.program.link implAt) cAddr R0 := by
  have hA : Iface.Efaceeq (Extracted.program.link implAt) A0 R0 := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) efaceeq_impl
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness call state: `MemSat.wstate` at the entry, with `nilinterequal(EFV, EFV)` (the `any` value `EFV = (TD, VAL)`, twice). -/
def r : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 EFV else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

/-- The witness comparison of two `TD`-values at `VAL` does not depend on the window (as
`MemSat.wstate_eqFrame`, for the stack bound 112). -/
theorem eqFrame :
    EqFrame R0 TD EqHashModel.wmem VAL VAL (calleeStack s0 112 2) := by
  have hsz : tySize EqHashModel.wmem TD = 8 := by decide
  have hout : ∀ a n, a + n ≤ 0x31000 → Outside a n (calleeStack s0 112 2) := fun a n h => by
    simp only [calleeStack, s0, MemSat.wstate, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]; omega
  refine EqFrame.of_regular (g := s0.regs 28) R0_laws (EqHashModel.wmem_env0 (s0.regs 28)) (Or.inl rfl)
    (by decide) (by decide) (by rw [hsz]; decide) (by rw [hsz]; decide) (by rw [hsz]; exact hout _ _ (by decide))
    (by rw [hsz]; exact hout _ _ (by decide)) fun a n ⟨rg, hr, h1, h2⟩ => hout a n ?_
  simp only [R0_priv, List.mem_singleton] at hr; subst hr; simp only at h2; omega

theorem pre : IfacePre R0 112 s0 ∧ IfaceInput s0 112 (s0.regs 0).toNat ∧ IfaceInput s0 112 (s0.regs 1).toNat ∧
    (s0.mem.readLE (s0.regs 0).toNat 8 = s0.mem.readLE (s0.regs 1).toNat 8 →
      Iface.EqOK R0 s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.mem.readLE ((s0.regs 0).toNat + 8) 8)
        (s0.mem.readLE ((s0.regs 1).toNat + 8) 8) ∧
      EqFrame R0 (s0.mem.readLE (s0.regs 0).toNat 8) s0.mem (s0.mem.readLE ((s0.regs 0).toNat + 8) 8)
        (s0.mem.readLE ((s0.regs 1).toNat + 8) 8) (calleeStack s0 112 2)) := by
  have hp : IfacePre R0 112 s0 := by
    refine ⟨EqHashModel.wmem_env0 (s0.regs 28), ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩ <;>
      simp only [CallOK, calleeStack, R0_priv, outside_cons, outside_nil] <;> decide
  have hi : IfaceInput s0 112 (s0.regs 0).toNat := by
    simp only [IfaceInput, Input, calleeStack, outside_cons, outside_nil]; decide
  have em : s0.mem = EqHashModel.wmem := rfl
  have e0 : (s0.regs 0).toNat = EFV := by simp [s0, r, MemSat.wstate, EFV]
  have e1 : (s0.regs 1).toNat = EFV := by simp [s0, r, MemSat.wstate, EFV]
  refine ⟨hp, hi, hi, fun _ => ?_⟩
  rw [em, e0, e1]
  have ht : EqHashModel.wmem.readLE EFV 8 = TD := by decide
  have hv : EqHashModel.wmem.readLE (EFV + 8) 8 = VAL := by decide
  rw [ht, hv]
  exact ⟨wmem_eqOK, by rw [← em]; exact eqFrame⟩

/-- All hypotheses of `correctness` hold together (the model `R0`, `R0.depth = 64`, `d = 112`). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (d : Nat), R.Laws ∧ 8 ≤ R.depth ∧
    R.depth + 48 ≤ d ∧
    Iface.Efaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.efaceeq") R ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (IfacePre R0 d s ∧ IfaceInput s d (s.regs 0).toNat ∧ IfaceInput s d (s.regs 1).toNat ∧
    (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8 →
      Iface.EqOK R0 s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
        (s.mem.readLE ((s.regs 1).toNat + 8) 8) ∧
      EqFrame R0 (s.mem.readLE (s.regs 0).toNat 8) s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8)
        (s.mem.readLE ((s.regs 1).toNat + 8) 8) (calleeStack s d 2))) :=
  ⟨implAt, R0, 112, R0_laws, by decide, by decide, model, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => IfaceRet R0 112 s0 s' fun r => BoolRes r
      (s0.mem.readLE (s0.regs 0).toNat 8 == s0.mem.readLE (s0.regs 1).toNat 8 &&
        Iface.efaceEqual R0 s0.mem (s0.mem.readLE (s0.regs 0).toNat 8)
          (s0.mem.readLE ((s0.regs 0).toNat + 8) 8) (s0.mem.readLE ((s0.regs 1).toNat + 8) 8))) :=
  correctness implAt R0 R0_laws 112 (by decide) (by decide) model s0 rfl pre

end Witness

end Proof

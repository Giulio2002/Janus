import Janus
import Extracted

/-! `example.com/basic.DeferTwice()` on amd64: two heap defer records in a loop
(`runtime.deferproc`) run at the exit (`runtime.deferreturn`); with their contracts
(`Janus.Contracts.PanicAmd64`, pinned) the call returns obeying the ABI and never panics.
Example 6 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => PanicCallerOK P s 32 8)
      (fun _ => goClass P)
      (fun s s' => MemFrame s.mem s'.mem
          (P.priv ++ [((s.regs regSP).toNat - (P.depth + 32), (s.regs regSP).toNat + 8)]) ∧
        P.Env s'.mem)
      (fun _ _ _ => False) := by
  intro ret hret s hs hc
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal
  have h32 : (18446744073709551584 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 32 := by
    omega
  have h32' : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  refine GoReturns.of_reaches ?_
  janus64_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine Reaches.call (Summary.withExit hdp hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv
    apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setRegF, keepABI_apply, MapAmd64.keepX15]; try omega)
  all_goals try (simp only [h32, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
  rintro s1 hpc1 ⟨r1, x1, y1, f1, m1, _, _, hs1, hfr1, henv1⟩
  subst hs1
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h32'] at hfr1
  have hi1 : m1.readLE ((s.regs 4).toNat - 16) 8 = 0 := by
    rw [hfr1.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
  janus64_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine Reaches.call (Summary.withExit hdp hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv1
    apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setRegF, keepABI_apply, MapAmd64.keepX15]; try omega)
  all_goals try (simp only [h32, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
  rintro s2 hpc2 ⟨r2, x2, y2, f2, m2, _, _, hs2, hfr2, henv2⟩
  subst hs2
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h32'] at hfr2
  janus64_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine Reaches.call (Summary.withExit hdr hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv2
    apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + 32)) (hi := (s.regs 4).toNat + 8)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setRegF, keepABI_apply, MapAmd64.keepX15]; try omega)
  all_goals try (simp only [h32, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
  rintro s3 hpc3 ⟨r3, x3, y3, f3, m3, _, _, hs3, hfr3, henv3⟩
  subst hs3
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h32'] at hfr3
  janus64_run
  exact ⟨by janus_frame, henv3⟩

/-! ## Non-vacuity: the model `P0`, a `RET` at `runtime.deferproc` and at `runtime.deferreturn`,
an admissible return address and a call state satisfying the precondition; `DeferTwice` returns. -/

namespace Witness

open Janus.Contracts.PanicSat (P0 P0_laws P0_priv P0_depth P0_env)
open Janus.Contracts.PanicSatAmd64 (panicRet_of wg wsp)

def aProc : Nat := Extracted.program.contractAddr "runtime.deferproc"
def aRet : Nat := Extracted.program.contractAddr "runtime.deferreturn"

def implAt : List Janus.Amd64.Segment :=
  [{ name := "deferproc", base := aProc, bytes := [0xc3] },
   { name := "deferreturn", base := aRet, bytes := [0xc3] }]

def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem ret_model (n a : Nat) (ha : a = aProc ∨ a = aRet) :
    Summary (Extracted.program.link implAt) a (PanicPre P0 n) (PanicRet P0 n) := by
  rw [linked_eq]
  intro s hpc ⟨henv, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩
  rcases ha with rfl | rfl <;> janus64_run <;>
  exact panicRet_of P0 n s _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) henv

def ret : Nat := 0x200000

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- Memory: the model's runtime range writable, a stack `[0x40000, 0x50000)` holding the return
address `ret` at `[wsp]`, the goroutine readable. -/
def wmem : Janus.Arm64.Memory :=
  ⟨fun a => if a = wsp + 2 then 0x20 else 0,
    [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

theorem pre : PanicCallerOK P0 s0 32 8 := by
  refine ⟨show wmem.accessible 0x10000 0x1000 true = true by decide, ⟨by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide

theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (ret : Nat)
    (s : Janus.Amd64.State), P.Laws ∧
    DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P ∧
    DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    PanicCallerOK P s 32 8 :=
  ⟨implAt, P0, ret, s0, P0_laws, ret_model 1 _ (.inl rfl), ret_model 0 _ (.inr rfl), hret, setup, pre⟩

theorem returns : GoReturns ((Extracted.program.link implAt).withExit ret) (goClass P0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (MemFrame s0.mem s'.mem
          (P0.priv ++ [((s0.regs regSP).toNat - (P0.depth + 32), (s0.regs regSP).toNat + 8)]) ∧
          P0.Env s'.mem)
    | .panicked _ _ => False :=
  correctness implAt P0 P0_laws (ret_model 1 _ (.inl rfl)) (ret_model 0 _ (.inr rfl)) ret hret s0
    setup pre

end Witness

end Proof

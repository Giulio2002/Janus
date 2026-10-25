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
  rintro s1 hpc1 ⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩
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
  rintro s2 hpc2 ⟨r2, x2, y2, f2, m2, hs2, hfr2, henv2⟩
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
  rintro s3 hpc3 ⟨r3, x3, y3, f3, m3, hs3, hfr3, henv3⟩
  subst hs3
  simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h32'] at hfr3
  janus64_run
  exact ⟨by janus_frame, henv3⟩

end Proof

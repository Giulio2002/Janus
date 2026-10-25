import Extracted

/-!
# `DeferTwice()` runs two heap-allocated defers (arm64)

**Guarantee (example 6 of docs/COVERAGE.md R6).** `DeferTwice` is
`for i := 0; i < 2; i++ { defer func() {}() }`. A defer inside a loop is never open-coded: each
iteration calls `runtime.deferproc` (a heap `_defer` record) and the function's exit calls
`runtime.deferreturn`, which runs the recorded calls. For every panic-runtime model `P` satisfying
its laws, every implementation of `runtime.deferproc` and `runtime.deferreturn` meeting their
contracts (`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), every admissible return
address and every call state in which the runtime is usable and has `P.depth` bytes of stack
below the 32-byte frame (`PanicCallerOK`), the call **returns** (obeying the ABI) — both
`deferproc` calls and the `deferreturn` call return — and memory changes only in the runtime's
memory and the stack window. It never panics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (hdp : DeferprocContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferproc") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry []
      (fun s => PanicCallerOK P s 32 0)
      (fun _ => goClass P)
      (fun s s' => MemFrame s.mem s'.mem (P.priv ++ [(s.sp.toNat - (P.depth + 32), s.sp.toNat)]) ∧
        P.Env s'.mem)
      (fun _ _ _ => False) := by
  intro ret hret s hs hc
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  refine GoReturns.of_reaches ?_
  -- first iteration: deferproc
  janus_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine Reaches.call (Summary.withExit hdp hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv
    apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat + 0)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setReg]; try omega)
  rintro s1 hpc1 ⟨j1, f1, v1, m1, hs1, hfr1, henv1⟩
  subst hs1
  have h32 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
  simp only [calleeStack, h32] at hfr1
  -- second iteration: deferproc again
  janus_run until [Extracted.program.contractAddr "runtime.deferproc"]
  refine Reaches.call (Summary.withExit hdp hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv1
    apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat + 0)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setReg, retState, callRegs_apply]; try omega)
  rintro s2 hpc2 ⟨j2, f2, v2, m2, hs2, hfr2, henv2⟩
  subst hs2
  simp only [calleeStack, h32] at hfr2
  -- the exit: deferreturn
  janus_run until [Extracted.program.contractAddr "runtime.deferreturn"]
  refine Reaches.call (Summary.withExit hdr hret) rfl
    (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_) ?_
  · simp only [List.cons_append, List.nil_append]; janus_frame
  · apply hl.env_frame _ _ henv2
    apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + 32)) (hi := s.sp.toNat + 0)
    · janus_frame
    · exact Outside.of_sub hout (by omega) (by omega)
  all_goals try (simp [setReg, retState, callRegs_apply]; try omega)
  rintro s3 hpc3 ⟨j3, f3, v3, m3, hs3, hfr3, henv3⟩
  subst hs3
  simp only [calleeStack, h32] at hfr3
  janus_run
  exact ⟨by janus_frame, henv3⟩

end Proof

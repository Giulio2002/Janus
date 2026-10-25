import Extracted

/-!
# `RecoverSet(x uint64, e any) (r uint64)`: `recover` turns a panic into a return (arm64)

**Guarantee (example 3 of docs/COVERAGE.md R6).** `RecoverSet` is
`defer func() { if recover() != nil { r = 7 } }(); if x > 10 { panic(e) }; return x`, with an
open-coded defer. For every panic-runtime model `P` satisfying its laws, every implementation of
`runtime.gopanic`, `runtime.gorecover` and `runtime.deferreturn` meeting their contracts
(`Janus.Contracts.Panic`, pinned to the Go 1.26 runtime's code), and every Go call state in which
no panic is active, the runtime is usable with enough stack (`PanicCallerOK`), and `e` is not nil:

* if `x ≤ 10` the call returns `x` — the deferred closure runs at the exit, its `recover()` returns
  `nil` (no panic), and it leaves `r` alone;
* if `x > 10` the call **returns `7`**: `panic(e)` enters `runtime.gopanic`, which runs the deferred
  closure; its `recover()` returns `e`, so it sets the named result `r = 7`; the runtime resumes
  the frame at its `deferreturn` call, which returns, and the function returns `r`.

It never panics. The `gopanic` contract is instantiated with `RecoverSet`'s funcdata: the
`deferBits` byte at `SP + 39`, the closure slot at `SP + 64`, the `deferreturn` call at
`entry + 0x84`; the deferred closure `RecoverSet.func1` is not a wrapper.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Proof

theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (hpan : GopanicRecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P
      39 64 (Extracted.entry + 0x84))
    (hrec : GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P)
    (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x24))
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s (P.depth + 112) 32 ∧ P.Calm s.mem (s.regs 28).toNat ∧
        etyp.toNat ≠ 0)
      (fun _ => goClass P)
      (fun _ s' => (s'.regs 0).toNat = if x.toNat ≤ 10 then x.toNat else 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · -- normal path: the exit calls the closure, whose recover() returns nil
    janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
    refine Reaches.call (Summary.withExit hrec hret) rfl ⟨?_, ?_, ?_⟩ ?_
    rotate_left 3
    · rintro s1 hpc1 ⟨⟨j1, f1, v1, m1, hs1, hfr1, henv1⟩, hcalm1, -⟩
      obtain ⟨h0, h1, -⟩ := hcalm1 (hl.calm_frame _ _ _ hcalm
        (Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112))) (hi := s.sp.toNat + 32)
          (by janus_frame) (Outside.of_sub hout (by omega) (by omega))))
      subst hs1
      simp only [calleeStack] at hfr1
      simp only [retState, callRegs_apply, List.getD_nil] at h0 h1
      janus_run
      all_goals first | (simp [hx]; done) | (exfalso; simp_all)
    · refine PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henv
        apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112)))
          (hi := s.sp.toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals (simp [setReg]; try omega)
    · have h120 : (18446744073709551496 + s.sp.toNat) % 18446744073709551616 = s.sp.toNat - 120 := by
        omega
      simp [setReg, h120]
      exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Memory.accessible_mono _ hst (by omega) (by omega))
    · simp [setReg]; omega
  · sorry

end Proof

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

set_option maxHeartbeats 0 in
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
  · -- panic path: gopanic runs the closure, whose recover() returns e; it sets r = 7
    have hx' : 10 < x.toNat := by omega
    janus_run until [Extracted.program.contractAddr "runtime.gopanic"]
    have h80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
      rw [BitVec.toNat_sub]; simp; omega
    have e39 : s.sp.toNat - 80 + 39 = s.sp.toNat - 41 := by omega
    have e64 : s.sp.toNat - 80 + 64 = s.sp.toNat - 16 := by omega
    have e32 : (s.sp.toNat - 32) % 256 ^ 8 = s.sp.toNat - 32 :=
      Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                           rw [this]; omega)
    refine GopanicRecoverContract.reaches hpan hret rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    all_goals (try simp only [h80])
    all_goals (try simp only [e39, e64])
    · refine PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henv
        apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112)))
          (hi := s.sp.toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals (simp [setReg, h80]; try omega)
    · simp [setReg]; exact hne
    · rw [Memory.readLE_writeLE_self]
    · omega
    · simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hst (by omega) (by omega)
    · exact Outside.of_sub hout (by omega) (by omega)
    · omega
    · simp only [Memory.accessible_writeLE]
      exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Memory.accessible_mono _ hst (by omega) (by omega))
    all_goals (try simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint,
      Memory.readLE_writeLE_self, Memory.accessible_writeLE, e32])
    · omega
    · exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Memory.accessible_mono _ hst (by omega) (by omega))
    · decide
    intro c ⟨hcpc, h26, h28, h18, h29, hcal, hclo, hchi, h30a, h30b, hpk, henvc, hb0, hfrc, hcont⟩
    dsimp only at hcpc h26 h28 h18 hclo hchi hpk hb0 hfrc hcont
    simp only [h80, e39, e64, setReg_apply, reduceIte, Nat.reduceEqDiff] at hcpc h26 h28 h18 hclo hchi hpk hb0 hfrc hcont
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, e32] at hcpc h26
    have hcode : (588944 : Nat) % 256 ^ 8 = 588944 := by decide
    rw [hcode] at hcpc
    obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
    dsimp only at hcpc h26 h28 h18 h29 hcal hclo hchi h30a h30b hpk henvc hb0 hfrc hcont
    subst hcpc
    have hgb : (cr 28).toNat + 16 + 8 ≤ 2 ^ 48 := by rw [h28]; omega
    have hga : cm.accessible ((cr 28).toNat + 16) 8 false = true := by
      rw [h28, hfrc.accessible]; simp only [Memory.accessible_writeLE]; exact hg2
    have hgv : cm.readLE ((cr 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      rw [h28, hfrc.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨hgo, by omega, by omega⟩)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    have hwin' : cm.accessible (s.sp.toNat - (P.depth + (P.depth + 112)))
        (P.depth + (P.depth + 112) + 32) true = true := by
      rw [hfrc.accessible]; simp only [Memory.accessible_writeLE]; exact hst
    -- the deferred closure, run until it returns into the runtime
    have hcl : ReachesRet (Extracted.program.link impl) (cr 30)
        ⟨cr, csp, BitVec.ofNat 64 588944, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ (fun c' =>
          c'.sp = csp ∧ c'.regs 28 = cr 28 ∧ c'.regs 18 = cr 18 ∧ P.Env c'.mem ∧
          P.Recovered c'.mem (s.regs 28).toNat ∧
          MemFrame cm c'.mem (P.priv ++ [(csp.toNat - 32 - P.depth, csp.toNat),
            (s.sp.toNat - 40, s.sp.toNat - 32)]) ∧
          c'.mem.readLE (s.sp.toNat - 40) 8 = 7) := by
      have hcr : cr = setReg (setReg (setReg cr 26 (BitVec.ofNat 64 (s.sp.toNat - 32))) 28 (s.regs 28))
          29 (csp - 8) := by
        funext i; simp only [setReg]; split
        · subst_vars; exact h29
        · split
          · subst_vars; exact h28
          · split
            · subst_vars; exact h26
            · rfl
      rw [hcr]
      janus_run until [Extracted.program.contractAddr "runtime.gorecover"]
      refine ReachesRet.call hrec rfl
        ⟨PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_, ?_, ?_⟩ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henvc
        apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112)))
          (hi := s.sp.toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals try (simp [setReg]; try omega)
      · exact Janus.Contracts.IfaceModel.acc_read_of_write
          (Memory.accessible_mono _ hwin' (by omega) (by omega))
      intro G' hpcG hpost _ hpanI
      obtain ⟨j2, f2, v2, m2, hs2, hfr2, henv2⟩ := hpost
      have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      have hsegf : segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36 = 588980 := by
        decide
      obtain ⟨hr0, hr1, hrec2⟩ := hpanI ⟨etyp.toNat, edata.toNat⟩ (cr 30).toNat
        (hl.panicking_frame _ _ _ _ _ (by simpa [setReg] using hpk) (by
          apply Map.Agrees.of_window (lo := s.sp.toNat - (P.depth + (P.depth + 112)))
            (hi := s.sp.toNat + 32)
          · janus_frame
          · exact Outside.of_sub hout (by omega) (by omega)))
        (by simpa [setReg, hsegf] using hw)
        (by
          try simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
          rw [show (18446744073709551576 + csp.toNat) % 18446744073709551616 + 8 = csp.toNat - 32 by
            omega]
          simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
          rw [h64]; exact Nat.mod_eq_of_lt (cr 30).isLt)
      subst hs2
      have h32 : (csp - 32#64).toNat = csp.toNat - 32 := by rw [BitVec.toNat_sub]; simp; omega
      simp only [calleeStack, h32, retState, callRegs_apply, List.getD_nil, setReg_apply, reduceIte,
        Nat.reduceEqDiff] at hfr2 hr0 hr1 hrec2 henv2
      have hj0 : j2 0 ≠ 0 := fun h => hne (by rw [← hr0, h]; rfl)
      janus_run
      have hag7 : Map.Agrees m2 (m2.writeLE (s.sp.toNat - 40) 8 7) P.priv :=
        Map.Agrees.of_window (lo := s.sp.toNat - 40) (hi := s.sp.toNat - 32) (by janus_frame)
          (Outside.of_sub hout (by omega) (by omega))
      refine ⟨hl.env_frame _ _ henv2 hag7, hl.recovered_frame _ _ _ hrec2 hag7, ?_⟩
      try simp only [List.cons_append, List.nil_append]
      janus_frame
    obtain ⟨k2, c', hst2, hpc2, hsp2, h282, h182, henv3, hrec3, hfr3, hr7⟩ := hcl
    refine Reaches.of_steps (hst2.withExit hret.fetch_none) ?_
    have hagc' : Map.Agrees cm c'.mem [(csp.toNat, s.sp.toNat - 80)] := by
      refine Map.Agrees.of_memFrame hfr3 fun a ⟨r, hr, h1, h2⟩ => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [outside_append]
      exact ⟨Outside.of_sub hout (by omega) (by omega),
        by simp only [outside_cons, outside_nil, and_true]; omega⟩
    obtain ⟨k3, d, hst3, hdpc, hdsp, hd28, hd18, hd29, hdfr, hdenv, hdcalm⟩ :=
      hcont c' hpc2 hsp2 h282 h182 hagc' henv3 hrec3
    refine Reaches.of_steps (hst3.withExit hret.fetch_none) ?_
    obtain ⟨dr, dsp, dpc, dfl, dm, ddz, dv, dtp, dfc, dfs⟩ := d
    dsimp only at hdpc hdsp hd28 hd18 hd29 hdfr hdenv hdcalm
    rw [show Extracted.entry + 132 = 588884 from rfl] at hdpc
    subst hdpc hdsp
    have hdr' : dr = setReg (setReg (setReg dr 18 (s.regs 18)) 28 (s.regs 28)) 29 (s.sp - 80#64 - 8) := by
      funext i; simp only [setReg]; split
      · subst_vars; exact hd29
      · split
        · subst_vars; exact hd28
        · split
          · subst_vars; exact hd18
          · rfl
    rw [hdr']
    janus_run until [Extracted.program.contractAddr "runtime.deferreturn"]
    refine Reaches.call (Summary.withExit hdr hret) rfl
      (PanicPre.of_within hc ?_ hdenv ?_ ?_ ?_ rfl ?_ ?_) ?_
    · simp only [List.cons_append, List.nil_append]; janus_frame
    all_goals try (simp [setReg]; try omega)
    rintro D hpcD ⟨j4, f4, v4, m4, hsD, hfrD, henvD⟩
    subst hsD
    have h80' : (s.sp - 80#64).toNat = s.sp.toNat - 80 := h80
    simp only [calleeStack, h80'] at hfrD
    janus_run
    rw [hr7, if_neg hx]

end Proof
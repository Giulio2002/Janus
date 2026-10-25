import Janus
import Extracted

/-! `example.com/basic.RecoverSet(x, e any) (r uint64)` on amd64: for `x ≤ 10` it returns `x`
(the deferred closure's `recover()` returns `nil`); for `x > 10`, `panic(e)` enters
`runtime.gopanic`, which runs the open-coded deferred closure; its `recover()` returns `e`, so it
sets `r = 7`; the runtime resumes the frame at its `deferreturn` call, which returns, and the call
returns `7`. Example 3 of docs/COVERAGE.md R6; contracts `Janus.Contracts.PanicAmd64` (pinned),
instantiated with the funcdata (`deferBits` at `RSP + 23`, slot at `RSP + 48`, `deferreturn` at
`entry + 0x86`, the body `RSP` being `RSP + 8` at `gopanic`'s entry). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.MapAmd64 (keepABI_apply)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (hpan : GopanicRecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P 23 48 (Extracted.entry + 0x86))
    (hrec : GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P)
    (hw : ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b))
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s (P.depth + 96) 32 ∧ P.Calm s.mem (s.regs 14).toNat ∧
        etyp.toNat ≠ 0)
      (fun _ => goClass P)
      (fun _ s' => (s'.regs 0).toNat = if x.toNat ≤ 10 then x.toNat else 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · janus64_run until [Extracted.program.contractAddr "runtime.gorecover"]
    have h96 : (18446744073709551520 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 96 := by
      omega
    have h80 : (18446744073709551536 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 80 := by
      omega
    refine Reaches.call (Summary.withExit hrec hret) rfl
      ⟨PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩ ?_
    rotate_left 11
    · intro s1 hpc1 hpost
      obtain ⟨⟨r1, x1, y1, f1, m1, hs1, hfr1, henv1⟩, hcalm1, -⟩ := hpost
      obtain ⟨h0, h3, -⟩ := hcalm1 (hl.calm_frame _ _ _ (by simpa [setRegF] using hcalm)
        (Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
          (hi := (s.regs 4).toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega))))
      subst hs1
      have h96' : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
        rw [BitVec.toNat_sub]; simp; omega
      simp only [keepABI_apply, reduceIte, Nat.reduceEqDiff] at h0 h3
      simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h96'] at hfr1
      janus64_run
      all_goals first | (simp [hx]; done) | (exfalso; simp_all)
    · simp only [List.cons_append, List.nil_append]; janus_frame
    · apply hl.env_frame _ _ henv
      apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
        (hi := (s.regs 4).toNat + 32)
      · janus_frame
      · exact Outside.of_sub hout (by omega) (by omega)
    all_goals try (simp [setRegF, h96, h80]; try omega)
    all_goals try (simp only [h96, h80, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
    · exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
  · have hx' : 10 < x.toNat := by omega
    janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
    have h72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
      rw [BitVec.toNat_sub]; simp; omega
    have e23 : (s.regs 4).toNat - 72 + 8 + 23 = (s.regs 4).toNat - 41 := by omega
    have e48 : (s.regs 4).toNat - 72 + 8 + 48 = (s.regs 4).toNat - 16 := by omega
    have e32 : ((s.regs 4).toNat - 32) % 256 ^ 8 = (s.regs 4).toNat - 32 :=
      Nat.mod_eq_of_lt (by have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
                           rw [this]; omega)
    refine GopanicRecoverContract.reaches hpan hret rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    all_goals (try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h72, e23, e48])
    · refine PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henv
        apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
          (hi := (s.regs 4).toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals try (simp [setRegF, h72]; try omega)
      all_goals try (simp only [h72, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
    · exact hne
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
    · omega
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
    · exact Outside.of_sub hout (by omega) (by omega)
    · omega
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    all_goals (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.accessible_writeLE, e32])
    · omega
    · exact Janus.Contracts.IfaceModel.acc_read_of_write
        (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    · decide
    intro c ⟨hcpc, h2c, h14c, hxc, hdfc, halc, hloc, hhic, hrac, hpk, henvc, hb0, hfrc, h5c, hcont⟩
    dsimp only at hcpc h2c h14c hloc hhic hpk hb0 hfrc h5c hcont
    simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h72, e23, e48] at hcpc h2c h14c hloc hhic hpk hb0 hfrc h5c hcont
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, e32] at hcpc h2c
    rw [show (4741376 : Nat) % 256 ^ 8 = 4741376 by decide] at hcpc
    obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := c
    dsimp only at hcpc h2c h14c hxc hdfc halc hloc hhic hrac hpk henvc hb0 hfrc h5c hcont
    subst hcpc hdfc
    have hgb : (cr 14).toNat + 16 + 8 ≤ 2 ^ 48 := by rw [h14c]; omega
    have hga : cm.accessible ((cr 14).toNat + 16) 8 false = true := by
      rw [h14c, hfrc.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hgr
    have hwin' : cm.accessible ((s.regs 4).toNat - (P.depth + (P.depth + 96)))
        (P.depth + (P.depth + 96) + 32) true = true := by
      rw [hfrc.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hst
    have hcl : Janus.Amd64.Tactic.ReachesRet (Extracted.program.link impl)
        (BitVec.ofNat 64 (cm.readLE (cr 4).toNat 8))
        ⟨cr, BitVec.ofNat 64 4741376, cfl, cxm, cm, cyh, cfs, false, cmx⟩ (fun c' =>
          c'.regs 4 = cr 4 + 8 ∧ c'.regs 14 = cr 14 ∧ c'.regs 5 = cr 5 ∧ c'.xmm 15 = 0 ∧
          c'.df = false ∧ P.Env c'.mem ∧ P.Recovered c'.mem (s.regs 14).toNat ∧
          MemFrame cm c'.mem (P.priv ++ [((cr 4).toNat - 24 - P.depth, (cr 4).toNat),
            ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)]) ∧
          c'.mem.readLE ((s.regs 4).toNat - 40) 8 = 7) := by
      have hcr : cr = setRegF (setRegF (setRegF cr 2 (BitVec.ofNat 64 ((s.regs 4).toNat - 32))) 5
          (s.regs 4 - 8#64)) 14 (s.regs 14) := by
        funext i; simp only [setRegF]; split
        · subst_vars; exact h14c
        · split
          · subst_vars; exact h5c
          · split
            · subst_vars; exact h2c
            · rfl
      rw [hcr]
      janus64_run until [Extracted.program.contractAddr "runtime.gorecover"]
      have hc24 : (cr 4 - 24#64).toNat = (cr 4).toNat - 24 := by rw [BitVec.toNat_sub]; simp; omega
      have hc8 : (cr 4 - 8#64).toNat = (cr 4).toNat - 8 := by rw [BitVec.toNat_sub]; simp; omega
      refine Janus.Amd64.Tactic.ReachesRet.call hrec rfl
        ⟨PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩ ?_
      · simp only [List.cons_append, List.nil_append]; janus_frame
      · apply hl.env_frame _ _ henvc
        apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
          (hi := (s.regs 4).toNat + 32)
        · janus_frame
        · exact Outside.of_sub hout (by omega) (by omega)
      all_goals try (simp [setRegF, hc24, hc8]; try omega)
      all_goals try (simp only [hc24, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
      · exact Janus.Contracts.IfaceModel.acc_read_of_write
          (Janus.Arm64.Memory.accessible_mono _ hwin' (by omega) (by omega))
      intro G' hpcG hpost _ hpanI
      obtain ⟨r2, x2, y2, f2, m2, hs2, hfr2, henv2⟩ := hpost
      have hsegf : segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x1b = 4741403 := by
        decide
      have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      obtain ⟨hr0, hr1, hrec2⟩ := hpanI ⟨etyp.toNat, edata.toNat⟩ (cm.readLE (cr 4).toNat 8)
        (hl.panicking_frame _ _ _ _ _ (by simpa [setRegF] using hpk) (by
          apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
            (hi := (s.regs 4).toNat + 32)
          · janus_frame
          · exact Outside.of_sub hout (by omega) (by omega)))
        (by try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hc24]
            try simp only [Janus.Arm64.Memory.readLE_writeLE_self]
            rw [show (4741403 : Nat) % 256 ^ 8 = 4741403 by decide, ← hsegf]; exact hw)
        (by try simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hc8]
            rw [show (cr 4).toNat - 8 + 8 = (cr 4).toNat by omega]
            simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
      subst hs2
      simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, hc24,
        keepABI_apply] at hfr2 hr0 hr1 hrec2 henv2
      have hj0 : r2 0 ≠ 0 := fun h => hne (by rw [← hr0, h]; rfl)
      janus64_run
      all_goals first
        | (exfalso; exact hj0 (BitVec.eq_of_toNat_eq (by simpa using ‹(r2 0).toNat = 0›)))
        | (have hag7 : Spec.Map.Agrees m2 (Janus.Arm64.Memory.writeLE m2 ((s.regs 4).toNat - 40) 8 7)
              P.priv :=
             Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - 40) (hi := (s.regs 4).toNat - 32)
               (by janus_frame) (Outside.of_sub hout (by omega) (by omega))
           refine ⟨?_, hxc, hl.env_frame _ _ henv2 hag7, hl.recovered_frame _ _ _ hrec2 hag7, ?_⟩
           · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_sub]; simp; omega
           · try simp only [List.cons_append, List.nil_append]
             janus_frame)
    obtain ⟨k2, c', hst2, hpc2, h42, h142, h52, hx2, hdf2, henv3, hrec3, hfr3, hr7⟩ := hcl
    refine Reaches.of_steps (hst2.withExit hret.fetch_none) ?_
    have hagc' : Spec.Map.Agrees cm c'.mem [((cr 4).toNat, (s.regs 4).toNat - 72 + 8)] := by
      refine Spec.Map.Agrees.of_memFrame hfr3 fun a ⟨r, hr, h1, h2⟩ => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [outside_append]
      exact ⟨Outside.of_sub hout (by omega) (by omega),
        by simp only [outside_cons, outside_nil, and_true]; omega⟩
    have hrip2 : c'.rip.toNat = cm.readLE (cr 4).toNat 8 := by
      rw [hpc2, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)
    obtain ⟨k3, d, hst3, hdpc, hd4, hd5, hd14, hdx, hddf, hdfr, hdenv, hdcalm⟩ :=
      hcont c' hrip2 h42 h142 (by rw [h52]) hx2 hdf2 hagc' henv3 hrec3
    refine Reaches.of_steps (hst3.withExit hret.fetch_none) ?_
    obtain ⟨dr, drip, dfl, dxm, dm, dyh, dfs, ddf, dmx⟩ := d
    dsimp only at hdpc hd4 hd5 hd14 hdx hddf hdfr hdenv hdcalm
    rw [show Extracted.entry + 134 = 4741318 from rfl] at hdpc
    subst hdpc hddf
    have hdr' : dr = setRegF (setRegF (setRegF dr 4 (s.regs 4 - 72#64 + 8)) 5 (s.regs 4 - 8#64))
        14 (s.regs 14) := by
      funext i; simp only [setRegF]; split
      · subst_vars; exact hd14
      · split
        · subst_vars; rw [hd5]
        · split
          · subst_vars; exact hd4
          · rfl
    rw [hdr']
    janus64_run until [Extracted.program.contractAddr "runtime.deferreturn"]
    refine Reaches.call (Summary.withExit hdr hret) rfl
      (PanicPre.of_within hc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [List.cons_append, List.nil_append]; janus_frame
    · apply hl.env_frame _ _ hdenv
      apply Spec.Map.Agrees.of_window (lo := (s.regs 4).toNat - (P.depth + (P.depth + 96)))
        (hi := (s.regs 4).toNat + 32)
      · janus_frame
      · exact Outside.of_sub hout (by omega) (by omega)
    all_goals try (simp [setRegF, h72]; try omega)
    all_goals try (simp only [h72, Janus.Arm64.Memory.readLE_writeLE_self]; decide)
    rintro D hpcD ⟨r4, x4, y4, f4, m4, hsD, hfrD, henvD⟩
    subst hsD
    simp only [MapAmd64.calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, h72] at hfrD
    janus64_run
    exact ⟨hdx, by rw [if_neg hx]⟩

end Proof
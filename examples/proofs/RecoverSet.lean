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

/-! Code addresses are evaluated from the extraction (`janus_eval%`), so a relinked binary needs
no edit: the deferred closure's entry, its return point after `BL runtime.gorecover`, and the
`deferreturn` call the runtime resumes at. -/
local macro "func1A" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1"))
local macro "recoverRet" : term =>
  `(janus_eval% (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36))
local macro "resumeA" : term => `(janus_eval% (Extracted.entry + 0x84))

set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (P : PanicRuntime) (hl : P.Laws)
    (hpan : GopanicRecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gopanic") P
      39 64 (Extracted.entry + 0x84))
    (hrec : GorecoverContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gorecover") P)
    (hdr : DeferreturnContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.deferreturn") P)
    (x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x, etyp, edata]
      (fun s => PanicCallerOK P s (P.depth + 112) 32 ∧ P.Calm s.mem (s.regs 28).toNat ∧
        etyp.toNat ≠ 0 ∧ ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x24))
      (fun _ => goClass P)
      (fun _ s' => (s'.regs 0).toNat = if x.toNat ≤ 10 then x.toNat else 7)
      (fun _ _ _ => False) := by
  intro ret hret s hs ⟨hc, hcalm, hne, hw⟩
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
    have hcode : (func1A : Nat) % 256 ^ 8 = func1A := by decide
    rw [hcode] at hcpc
    obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs, cex, cep⟩ := c
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
        ⟨cr, csp, BitVec.ofNat 64 func1A, cfl, cm, cdz, cv, ctp, cfc, cfs, cex, cep⟩ (fun c' =>
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
      have hsegf : segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 36 = recoverRet := by
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
    rw [show Extracted.entry + 132 = resumeA from rfl] at hdpc
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


/-! ## Non-vacuity

The model `PanicSat.P0` (laws proved, no wrappers), model code at the three contract addresses —
`gopanic` (the `PanicSat` model with `RecoverSet`'s funcdata: `deferBits` at `SP + 39`, the slot at
`SP + 64`, resuming at `entry + 0x84`), `gorecover` (the `PanicSat` model) and a `RET` for
`deferreturn` — each proved to meet its contract for `P0`, an admissible return address and a
call state satisfying the precondition: so `correctness` applies (`nonvacuous`), and for
`x = 42`, `e = (1, 0)` the call returns `7` (`returns`). -/

namespace Witness

open Janus.Contracts.PanicSat

def gAddr : Nat := Extracted.program.contractAddr "runtime.gopanic"
def rAddr : Nat := Extracted.program.contractAddr "runtime.gorecover"
def dAddr : Nat := Extracted.program.contractAddr "runtime.deferreturn"

/-- `PanicSat.gopanicCode` with this frame's offsets (`#39`, `#64`) and resume address. -/
def gopanicCode' : List Nat :=
  [0x910003e9, 0xf940213a, 0xf940034b, 0xd10083ff, 0xf9000be9, 0x39009d3f, 0xd281000e, 0xf2a0002e,
   0xf90001c0, 0xf90005c1, 0x100000ed, 0xf90009cd, 0xd280002c, 0xf9000dcc, 0xf90011df, 0xd10023fd,
   0xd63f0160, 0xf9400be9, 0x9100013f, 0xd10023fd, 0xd281000e, 0xf2a0002e, 0xf9000ddf, janus_eval% (0xd2800000 + (Extracted.entry + 0x84) % 0x10000 * 32 + 12),
   janus_eval% (0xf2a00000 + (Extracted.entry + 0x84) / 0x10000 % 0x10000 * 32 + 12), 0xd61f0180]

def implAt : List Segment :=
  [{ name := "gopanic", base := gAddr, words := gopanicCode' },
   { name := "gorecover", base := rAddr, words := gorecoverCode },
   { name := "deferreturn", base := dAddr, words := retCode }]

def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem gopanic_model' : GopanicRecoverContract (Extracted.program.link implAt) gAddr P0 39 64
    resumeA := by
  rw [linked_eq]
  intro s hpc ⟨⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩, hx0, hbits, hb1, hb2, hb3,
    hs1, hs2, hf1, hf2, hc1, hc2⟩
  simp only [P0_env, P0_depth, P0_priv, outside_cons, outside_nil, and_true] at henv hwin hacc hout hb3 hst
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  simp only [PANREC] at hrd
  have hspl := s.sp.isLt
  show ReachesRet _ _ s _
  janus_run
  refine ⟨by omega, (by simp only [P0_depth]; omega), by omega, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [P0, PANREC, Nat.reduceAdd, Memory.readLE_writeLE_of_disjoint,
      Memory.readLE_writeLE_self]
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    exact ⟨trivial, by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 0).isLt,
      by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 1).isLt, trivial⟩
  · simp only [P0_env, Memory.accessible_writeLE]; exact henv
  · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
    janus_frame
  · intro c' hpc' hsp' h28' h18' hag henv' hrec
    obtain ⟨r', sp', pc', fl', m', dz', vr', tp', fc', fs'⟩ := c'
    simp only at hpc' hsp' h28' h18' hag henv' hrec ⊢
    subst hpc' hsp'
    have hwin' : m'.accessible (s.sp.toNat - 32) 32 true = true := by
      rw [hag.1]; simp only [Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hacc (by omega) (by omega)
    have hpr' : m'.accessible 67584 2048 true = true := by
      rw [hag.1]; simp only [Memory.accessible_writeLE]; exact hrd
    have hv : m'.readLE (s.sp.toNat - 16) 8 = s.sp.toNat := by
      rw [hag.readLE ⟨(s.sp.toNat - 32, s.sp.toNat), by simp, by omega, by omega⟩]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h64]; exact Nat.mod_eq_of_lt s.sp.isLt
    show ReachesRet _ _ _ _
    janus_run
    have hsp0 : BitVec.ofNat 64 (m'.readLE (s.sp.toNat - 16) 8) = s.sp := by
      rw [hv]; exact BitVec.ofNat_toNat _ _
    refine ⟨hsp0, h28', h18', by rw [hsp0], ?_, ?_, ?_⟩
    · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
      janus_frame
    · simp only [P0_env, Memory.accessible_writeLE] at henv' ⊢; exact henv'
    · show (m'.writeLE (PANREC + 24) 8 0).readLE (PANREC + 24) 8 = 0
      rw [Memory.readLE_writeLE_self]

theorem gopanic_model : GopanicRecoverContract (Extracted.program.link implAt) gAddr P0 39 64
    (Extracted.entry + 0x84) := gopanic_model'

theorem gorecover_model : GorecoverContract (Extracted.program.link implAt) rAddr P0 := by
  rw [linked_eq]
  intro s hpc ⟨⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩, hfp, hfp'⟩
  simp only [P0_env] at henv
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  have hr : s.mem.accessible PANREC 0x800 false = true := Janus.Contracts.IfaceModel.acc_read_of_write hrd
  simp only [PANREC] at hrd hr
  janus_run
  · -- the active flag is clear: `nil`
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) henv, fun h => h, fun v rp hp _ _ => ?_⟩
    have := hp.1; simp only [PANREC, Nat.reduceAdd] at this; omega
  · -- the recorded return point matches `[x29 + 8]`: return the value, set the recovered flag
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (by simp only [P0_priv, calleeStack, P0_depth, List.cons_append, List.nil_append]; janus_frame)
      (by simp only [P0_env, Memory.accessible_writeLE]; exact henv), fun hc => ?_,
      fun v rp hp _ _ => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, h2, h3, -⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h2 h3
      have hl1 := Memory.readLE_lt s.mem 67584 8
      have hl2 := Memory.readLE_lt s.mem 67592 8
      refine ⟨by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setReg]; omega),
        by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setReg]; omega), ?_⟩
      · show (s.mem.writeLE (PANREC + 32) 8 1).readLE (PANREC + 32) 8 = 1
        rw [Memory.readLE_writeLE_self]
  · -- the return point does not match: `nil`
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) henv, fun hc => ?_, fun v rp hp _ hfp8 => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, -, -, h4⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h4
      exact absurd (h4.trans hfp8.symm) (by assumption)

theorem ret_model : DeferreturnContract (Extracted.program.link implAt) dAddr P0 := by
  rw [linked_eq]
  intro s hpc ⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩
  janus_run
  exact panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) henv

def ret : Nat := 0x200000

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else if i = 0 then 42#64 else if i = 1 then 1#64
      else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry
    [42#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, rfl, fun i h => ?_⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK P0 s0 (P0.depth + 112) 32 ∧ P0.Calm s0.mem (s0.regs 28).toNat ∧
    (1#64 : BitVec 64).toNat ≠ 0 := by
  refine ⟨⟨show wmem.accessible 0x10000 0x1000 true = true by decide, ⟨by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    by show wmem.readLE (PANREC + 24) 8 = 0; simp only [PANREC]; decide, by decide⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide

theorem nonvacuous : ∃ (impl : List Segment) (P : PanicRuntime) (ret : Nat) (s : State), P.Laws ∧
    GopanicRecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P 39 64 (Extracted.entry + 0x84) ∧
    GorecoverContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gorecover") P ∧
    DeferreturnContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.deferreturn") P ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [42#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s (P.depth + 112) 32 ∧ P.Calm s.mem (s.regs 28).toNat ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      ¬ P.wrapper (segAddr Extracted.program "example.com/basic.RecoverSet.func1" + 0x24)) :=
  ⟨implAt, P0, ret, s0, P0_laws, gopanic_model, gorecover_model, ret_model, hret, setup, ⟨pre.1, pre.2.1, pre.2.2, id⟩⟩

theorem returns : GoReturns ((Extracted.program.link implAt).withExit ret) (goClass P0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧
        (s'.regs 0).toNat = if (42#64 : BitVec 64).toNat ≤ 10 then (42#64 : BitVec 64).toNat else 7
    | .panicked _ _ => False :=
  correctness implAt P0 P0_laws gopanic_model gorecover_model ret_model 42#64 1#64 0#64 ret hret s0
    setup ⟨pre.1, pre.2.1, pre.2.2, id⟩

end Witness

end Proof

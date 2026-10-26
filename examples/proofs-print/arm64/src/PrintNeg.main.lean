/-!
# `print(-17)`: a negative `int` (arm64)

```go
func PrintNeg() { print(-17) }
```

Lowered to `printlock(); printint(-17); printunlock()`: `printint` prints `-` and calls `printuint`
on the magnitude, which formats it with `internal/strconv.formatBase10`; all executed by the model
from the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every
call state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`,
the call returns and the trace gains what one `write(2, "-17")` may append (all of it, a prefix,
or nothing). **`full_output`**: if fd 2 grew by 3 bytes, it grew by exactly `"-17"`.
-/
-- BODY
/-! ## `PrintNeg` -/

theorem fmtInt_neg17 : Janus.Spec.Print.fmtInt (-17#64) = Janus.Spec.Print.ofString "-17" := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    EnsuresK (P.link impl) E Extracted.entry []
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.ofString "-17"] es) := by
  intro ret hret s k hs ⟨hpr, hd, hdo⟩
  dsimp only [PrintReady] at hpr
  obtain ⟨⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hg0, hgl, hgm, hwb, h_rd_wb, hm1, hm2, h_rd_dy, h_rd_c,
    hlk31, hpk, hbi, hbi2, hbl, how, h_rd_ow, hdl, hfree, hin1, hin2, ho1, ho2, ho3, ho4, ho5, ho6,
    ho7, ho8, ho9, ho10, hsep1, hsep2, hsep3, hsep4, hsep5, hsep6⟩ := hpr
  simp only [sep_cons, sep_nil, and_true, gM, gWritebuf, mLocks, mDying, mPrintlock] at *
  obtain ⟨a1, a2, a3, a4, a6, a7, a8, a9, aD⟩ := hsep1
  obtain ⟨b1, b2, b3, b5, b6, b7, b8, bD⟩ := hsep2
  obtain ⟨d1, d2, dD1⟩ := hsep3
  obtain ⟨d3, d4, dD2⟩ := hsep4
  obtain ⟨d5, d6, dD3⟩ := hsep5
  obtain ⟨e1, e2⟩ := hsep6
  janus_intro hs
  janus_data hd [hw, hm2, hbi, hbl]
  -- the read-only data it prints from, outside `rt`
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_ow : OW
  simp only [h_pk, h_bi, h_bl, h_ow] at *
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_ow : OW
  janus_eval_nat h_sm : SM
  have hsmo : Outside SM 200 rt := hdo.of_dataRead (by rw [h_sm]; decide +kernel)
  rw [h_sm] at hsmo
  apply ReturnsK.of_reaches
  janus_run until [segAddr P "runtime.printlock"]
  refine Reaches.call (Summary.withExit (printlock_free impl rt 1024 hl) hret) rfl ?_ (fun s1 hr1 hpost1 => ?_)
  · refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?nl, ?in1, ?in2, ?_, ?_, ?_, ?_, ?_, ?_, ?sep⟩
    case nl => simp only [lockHeld] at hfree ⊢; janus_simp; exact hfree
    case in1 => janus_simp; exact hin1
    case in2 => janus_simp; exact hin2
    case sep =>
      simp only [sep_cons, sep_nil, and_true]
      janus_simp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apart_mono
    all_goals kobl
  · obtain ⟨junk1, f1, v1, m1, rfl, hfr1, h_rd_c1, h_rd_l1, hheld1⟩ := hpost1
    revert hfr1 h_rd_c1 h_rd_l1 hheld1
    janus_simp
    intro hfr1 h_rd_c1 h_rd_l1 hheld1
    janus_run until [segAddr P "runtime.printint"]
    apply ReturnsK.to_reaches
    apply printint_k impl hmm E ret hret _ k (s.sp.toNat - 32) (s.regs 28).toNat
      (s.mem.readLE ((s.regs 28).toNat + 48) 8) (-17#64)
    case hk =>
      rintro S2 K2 ⟨junk2, f2, v2, m2, es1, rfl, hfr2, h_rd_c2, h_rd_l2, hbi2', rfl, hem1⟩
      dsimp only at hfr2 h_rd_c2 h_rd_l2 hbi2'
      simp only [h_bi, h_bl] at hfr2 hbi2'
      apply ReturnsK.of_reaches
      janus_run until [segAddr P "runtime.printunlock"]
      refine Reaches.call (Summary.withExit (printunlock_last impl rt 1024 hu) hret) rfl ?_
        (fun s5 hr5 hpost5 => ?_)
      · refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?hl, ?in1, ?in2, ?_, ?_, ?_, ?_, ?_, ?_, ?sep⟩
        case hl => simp only [lockHeld]; janus_simp; exact hheld1
        case in1 => janus_simp; exact hin1
        case in2 => janus_simp; exact hin2
        case sep =>
          simp only [sep_cons, sep_nil, and_true]
          janus_simp
          refine ⟨?_, ?_, ?_, ?_⟩ <;> apart_mono
        all_goals kobl
      · obtain ⟨junk5, f5, v5, m5, rfl, hfr5, h_rd_c5, h_rd_l5, hkey5⟩ := hpost5
        revert hfr5 h_rd_c5 h_rd_l5 hkey5
        janus_simp
        intro hfr5 h_rd_c5 h_rd_l5 hkey5
        janus_run
        refine ⟨es1, rfl, ?_⟩
        rw [← fmtInt_neg17]
        exact hem1
    all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_sm]
    all_goals try (intro j hj; janus_simp; first | done | exact readLE_of_dataRead hd (by rw [← h_sm]; exact smalls_data j hj))
    case hsp => apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals kobl

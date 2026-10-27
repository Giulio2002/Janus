import PrintProofs.Amd64.FnPrintint
import PrintProofs.Amd64.FnLock
import PrintProofs.Amd64.FnWitness

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

/-!
# `print(-17)` (amd64)

```go
func PrintNeg() { print(-17) }
```

Lowered to `printlock(); printint(-17); printunlock()` (no newline), all executed by the model from
the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every call
state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`, the call
returns and the trace gains what one `write(2, "-17")` may append (all of it, a prefix, or
nothing). **`full_output`**: if fd 2 grew by 3 bytes, it grew by exactly `"-17"`.
-/

namespace PrintFn.Neg

/-! ## `PrintNeg` -/

theorem fmtInt_neg17 : Janus.Spec.Print.fmtInt (-17#64) = Janus.Spec.Print.ofString "-17" := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    Amd64.Kernel.EnsuresK (P.link impl) E PrintCode.entryPrintNeg []
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 8 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.ofString "-17"] es) := by
  intro ret hret s k hs ⟨hpr, hd, hdo⟩
  dsimp only [Amd64.Print.PrintReady] at hpr
  obtain ⟨hb, ha, hw, hal, hgp, hg2, hg3, hg0, hg1, hgm, hwb, h_rd_wb, hfs1, hfsu, hfs2, h_rd_tl, hm1,
    hm2, h_rd_dy, h_rd_c, hlk31, hpk, hbi, hbi2, hbl, how, h_rd_ow, hdl, hfree, hin1, hin2, ho1, ho2,
    ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, ho11, hsep1, hsep2, hsep3, hsep4, hsep5, hsep6, hsep7⟩ := hpr
  simp only [sep_cons, sep_nil, and_true, gM, gWritebuf, mLocks, mDying, mPrintlock] at *
  obtain ⟨a1, a2, a3, a4, a6, a7, a8, a9, aD, a10⟩ := hsep1
  obtain ⟨b1, b2, b3, b5, b6, b7, b8, bD, b9⟩ := hsep2
  obtain ⟨d1, d2, dD1⟩ := hsep3
  obtain ⟨d3, d4, dD2⟩ := hsep4
  obtain ⟨d5, d6, dD3⟩ := hsep5
  obtain ⟨e1, e2⟩ := hsep6
  obtain ⟨d7, d8, dD4⟩ := hsep7
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  janus64_data hd [hw, hm2, hbi, hbl]
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
  janus64_run until [segAddr P "runtime.printlock"]
  refine Reaches.call (Summary.withExit (printlock_free impl rt 1024 hl) hret) rfl ?_ (fun s1 hr1 hpost1 => ?_)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?nl, ?in1, ?in2, ?_, ?_, ?_, ?_, ?_, ?_, ?sep⟩
    case nl => simp only [lockHeld] at hfree ⊢; janus64_simp; exact hfree
    case in1 => janus64_simp; exact hin1
    case in2 => janus64_simp; exact hin2
    case sep =>
      simp only [sep_cons, sep_nil, and_true]
      janus64_simp
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apart_mono
    all_goals first | kobl64 | (janus64_simp; exact Outside.of_sub ho1 (by omega) (by omega))
  · obtain ⟨junk1, f1, x1, yh1, m1, zh1, kr1, rfl, hfr1, h_rd_c1, h_rd_l1, hheld1⟩ := hpost1
    revert hfr1 h_rd_c1 h_rd_l1 hheld1
    janus64_simp
    intro hfr1 h_rd_c1 h_rd_l1 hheld1
    janus64_run until [segAddr P "runtime.printint"]
    apply Amd64.Print.ReturnsK.to_reaches
    apply printint_k impl hmm E ret hret _ k ((s.regs 4).toNat - 24) (s.regs 14).toNat
      (s.mem.readLE ((s.regs 14).toNat + 48) 8) (-17#64)
    case hk =>
      rintro S2 K2 ⟨junk2, f2, x2, yh2, m2, zh2, kr2, es1, rfl, hfr2, h_rd_c2, h_rd_l2, hbi2', rfl, hem1⟩
      dsimp only at hfr2 h_rd_c2 h_rd_l2 hbi2'
      simp only [h_bi, h_bl] at hfr2 hbi2'
      apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run until [segAddr P "runtime.printunlock"]
      refine Reaches.call (Summary.withExit (printunlock_last impl rt 1024 hu) hret) rfl ?_
        (fun s5 hr5 hpost5 => ?_)
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?hl, ?in1, ?in2, ?_, ?_, ?_, ?_, ?_, ?_, ?sep⟩
        case hl => simp only [lockHeld]; janus64_simp; exact hheld1
        case in1 => janus64_simp; exact hin1
        case in2 => janus64_simp; exact hin2
        case sep =>
          simp only [sep_cons, sep_nil, and_true]
          janus64_simp
          refine ⟨?_, ?_, ?_, ?_⟩ <;> apart_mono
        all_goals first | kobl64 | (janus64_simp; exact Outside.of_sub ho1 (by omega) (by omega))
      · obtain ⟨junk5, f5, x5, yh5, m5, zh5, kr5, rfl, hfr5, h_rd_c5, h_rd_l5, hkey5⟩ := hpost5
        revert hfr5 h_rd_c5 h_rd_l5 hkey5
        janus64_simp
        intro hfr5 h_rd_c5 h_rd_l5 hkey5
        janus64_run
        refine ⟨es1, rfl, ?_⟩
        rw [← fmtInt_neg17]
        exact hem1
    case hpc => dsimp only; rfl
    case hsp => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; omega
    case hx0 => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; rfl
    all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_sm]
    all_goals try (intro j hj; janus64_simp; first | done | exact readLE_of_dataRead hd (by rw [← h_sm]; exact smalls_data j hj))
    all_goals kobl64

/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    Amd64.Kernel.EnsuresK (P.link impl) E PrintCode.entryPrintNeg []
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 8 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧
        DataOutside P rt)
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (Janus.Spec.Print.ofString "-17").length →
        k'.output 2 = k.output 2 ++ (Janus.Spec.Print.ofString "-17")) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h

namespace Witness

open PrintFn.Witness

theorem setup : GoABI.CallSetup ((P.link implAt).withExit ret) PrintCode.entryPrintNeg [] (wstate PrintCode.entryPrintNeg fun _ => 0) :=
  ⟨rfl, by decide +kernel, rfl, by decide, by intro i h; simp at h, rfl⟩

/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    GoABI.RetAddr (P.link impl) ret ∧ GoABI.CallSetup ((P.link impl).withExit ret) PrintCode.entryPrintNeg [] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 8 256 s ∧ Amd64.Program.DataLoaded P s.mem ∧ DataOutside P rt) :=
  ⟨implAt, wrt, ret, wstate PrintCode.entryPrintNeg fun _ => 0, lock2_model wrt 1024, unlock2_model wrt 1024, memmove_model,
    hret, setup, ready _ _ 8 (Or.inl rfl), wmem_data, wrt_data⟩

/-- So the guarantee is reached: from the witness state, for every kernel, `print(-17)` returns
and the trace gains what `write(2, "-17")` may append. -/
theorem returns (E : KEnv) (k : Kern) :
    Amd64.Kernel.ReturnsK ((P.link implAt).withExit ret) E
      (fun s' k' => ABIReturn (wstate PrintCode.entryPrintNeg fun _ => 0) s' ∧
        ∃ es, k' = k.appendTrace es ∧ Emits 2 [Janus.Spec.Print.ofString "-17"] es)
      (fun _ _ => False) (wstate PrintCode.entryPrintNeg fun _ => 0) k :=
  correctness implAt wrt E (lock2_model wrt 1024) (unlock2_model wrt 1024) memmove_model ret hret _ k setup
    ⟨ready _ _ 8 (Or.inl rfl), wmem_data, wrt_data⟩

end Witness


end PrintFn.Neg

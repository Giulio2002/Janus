import PrintProofs.Arm64.FnPrintbool
import PrintProofs.Arm64.FnPrintnl
import PrintProofs.Arm64.FnLock
import PrintProofs.Arm64.FnWitness

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

/-!
# `println(b)` for a `bool` (arm64)

```go
func PrintBool(b bool) { println(b) }
```

Lowered to `printlock(); printbool(b); printnl(); printunlock()`, all executed by the model from
the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every call
state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`, the call
returns and the trace gains what one `write(2, b)` per piece of `fmtBool b` (`"true"`/`"false"`),
`"\n"` may append. **`full_output`**: if fd 2 grew by as many bytes as the pieces hold, it grew by
exactly `fmtBool b ++ "\n"`.
-/

namespace PrintFn.Bool

/-! ## `PrintBool` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (b : Bool) :
    EnsuresK (P.link impl) E PrintCode.entryPrintBool [BitVec.ofNat 64 b.toNat]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.fmtBool b, [10#8]] es) := by
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
  janus_eval_nat h_tr : TR
  janus_eval_nat h_fa : FA
  janus_eval_nat h_nl : NL
  have htro : Outside TR 4 rt := hdo.of_dataRead (by rw [h_tr]; decide +kernel)
  have hfao : Outside FA 5 rt := hdo.of_dataRead (by rw [h_fa]; decide +kernel)
  have hnlo : Outside NL 1 rt := hdo.of_dataRead (by rw [h_nl]; decide +kernel)
  rw [h_tr] at htro; rw [h_fa] at hfao; rw [h_nl] at hnlo
  have hbl1 : b.toNat < 2 := by cases b <;> decide
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
  · obtain ⟨junk1, f1, v1, m1, ex1, ep1, rfl, hfr1, h_rd_c1, h_rd_l1, hheld1⟩ := hpost1
    revert hfr1 h_rd_c1 h_rd_l1 hheld1
    janus_simp
    intro hfr1 h_rd_c1 h_rd_l1 hheld1
    janus_run until [segAddr P "runtime.printbool"]
    apply ReturnsK.to_reaches
    apply printbool_k impl hmm E ret hret _ k (s.sp.toNat - 32) (s.regs 28).toNat
      (s.mem.readLE ((s.regs 28).toNat + 48) 8) b
    case hk =>
      rintro S2 K2 ⟨junk2, f2, v2, m2, ex2, ep2, es1, rfl, hfr2, h_rd_c2, h_rd_l2, hbi2', rfl, hem1⟩
      dsimp only at hfr2 h_rd_c2 h_rd_l2 hbi2'
      simp only [h_bi, h_bl] at hfr2 hbi2'
      apply ReturnsK.of_reaches
      janus_run until [segAddr P "runtime.printnl"]
      apply ReturnsK.to_reaches
      apply printnl_k impl hmm E ret hret _ _ (s.sp.toNat - 32) (s.regs 28).toNat
        (s.mem.readLE ((s.regs 28).toNat + 48) 8)
      case hk =>
        rintro SN KN ⟨junkN, fN, vN, mN, exN, epN, esN, rfl, hfrN, h_rd_cN, h_rd_lN, hbiN', rfl, hemN⟩
        dsimp only at hfrN h_rd_cN h_rd_lN hbiN'
        simp only [h_bi, h_bl] at hfrN hbiN'
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
        · obtain ⟨junk5, f5, v5, m5, ex5, ep5, rfl, hfr5, h_rd_c5, h_rd_l5, hkey5⟩ := hpost5
          revert hfr5 h_rd_c5 h_rd_l5 hkey5
          janus_simp
          intro hfr5 h_rd_c5 h_rd_l5 hkey5
          janus_run
          refine ⟨es1 ++ esN, by simp only [Kern.appendTrace_append, List.append_assoc], ?_⟩
          dsimp only at hem1 hemN
          have hn3 : readBytes m2 NL 1 = [10#8] := by
            rw [h_nl, show readBytes m2 _ 1 = readBytes s.mem _ 1 by readbytes_frame]
            exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
          rw [hn3] at hemN
          refine Emits.append (bs := [Janus.Spec.Print.fmtBool b]) ?_ hemN
          unfold Janus.Spec.Print.fmtBool
          cases b
          · have h : readBytes m1 FA 5 = Janus.Spec.Print.ofString "false" := by
              rw [h_fa, show readBytes m1 _ 5 = readBytes s.mem _ 5 by readbytes_frame]
              exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
            simpa [h] using hem1
          · have h : readBytes m1 TR 4 = Janus.Spec.Print.ofString "true" := by
              rw [h_tr, show readBytes m1 _ 4 = readBytes s.mem _ 4 by readbytes_frame]
              exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
            simpa [h] using hem1
      all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_nl]
      all_goals kobl
    all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_tr, h_fa]
    case hsp => apply BitVec.eq_of_toNat_eq; simp; omega
    case hx0 => simp [setReg, callRegs, Nat.mod_eq_of_lt (show b.toNat < 256 by omega)]
    all_goals kobl

/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (b : Bool) :
    EnsuresK (P.link impl) E PrintCode.entryPrintBool [BitVec.ofNat 64 b.toNat]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (Janus.Spec.Print.fmtBool b ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (Janus.Spec.Print.fmtBool b ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm b ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h

namespace Witness

open PrintFn.Witness

theorem setup : CallSetup ((P.link implAt).withExit ret) PrintCode.entryPrintBool [BitVec.ofNat 64 true.toNat] (wstate PrintCode.entryPrintBool (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0)) :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    RetAddr (P.link impl) ret ∧ CallSetup ((P.link impl).withExit ret) PrintCode.entryPrintBool [BitVec.ofNat 64 true.toNat] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧ DataOutside P rt) :=
  ⟨implAt, wrt, ret, wstate PrintCode.entryPrintBool (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0), lock2_model wrt 1024, unlock2_model wrt 1024, memmove_model,
    hret, setup, ⟨ready _ _ 16 (Or.inl rfl), wmem_data, wrt_data⟩⟩

/-- So the guarantee is reached: from the witness state, for every kernel, `println(true)` returns and the trace gains what the two writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    ReturnsK ((P.link implAt).withExit ret) E
      (fun s' k' => FFI.ABIReturnC (wstate PrintCode.entryPrintBool (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧ Emits 2 [Janus.Spec.Print.fmtBool true, [10#8]] es)
      (fun _ _ => False) (wstate PrintCode.entryPrintBool (fun i => if i = 0 then BitVec.ofNat 64 true.toNat else 0)) k :=
  correctness implAt wrt E (lock2_model wrt 1024) (unlock2_model wrt 1024) memmove_model true ret hret _ k setup
    (⟨ready _ _ 16 (Or.inl rfl), wmem_data, wrt_data⟩)

end Witness


end PrintFn.Bool

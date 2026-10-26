/-!
# `println("x =", x)` for a `uint64` (arm64)

```go
func PrintX(x uint64) { println("x =", x) }
```

The compiler lowers it to `printlock(); printstring("x = "); printuint(x); printnl();
printunlock()`. Every one of those runtime functions is executed by the model from the binary
(`printlock`/`printunlock`, `printstring`, `printuint` and `internal/strconv.formatBase10`,
`printnl`, `gwrite`, `recordForPanic`, `writeErr`/`write`/`write1` down to the `SVC #0`); the
contracts are `runtime.lock2`/`runtime.unlock2` (`Print.Lock2Contract`, `Print.Unlock2Contract`: the
mutex `debuglock`, taken when the M's print count is 0) and `runtime.memmove`
(`Print.MemmoveContract`: the copy into `printBacklog`). The kernel is the environment of
`Kernel.EnsuresK`: each `write(2, …)` may write any prefix of its buffer or fail.

**Guarantee (`correctness`).** From every Go call state ready to print (`Print.PrintReady`:
single-threaded, outside any other print, the stack window `[SP-1088, SP+16)` and the M/`g`/global
fields the print path touches, apart and outside the runtime-owned ranges `rt`), with the
program's read-only data loaded and outside `rt`, the call returns and the trace gains exactly
what one `write(2, b)` per piece `b` of `"x = "`, `decimal(x)`, `"\n"` may append
(`Print.Emits`). **`full_output`**: if the output of fd 2 grew by as many bytes as the three pieces
hold, it grew by exactly `"x = " ++ decimal(x) ++ "\n"`.
-/
-- BODY
/-! ## `PrintX` -/

/-- The string `"x = "` (`ADRP`+`ADD` at `PrintX+0x20`). -/
def XS : Nat := adrpLdTarget (Extracted.entry + 0x20) (segWord P "example.com/print.PrintX" 8)
  (segWord P "example.com/print.PrintX" 9) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (x : BitVec 64) :
    EnsuresK (P.link impl) E Extracted.entry [x]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun _ k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [Janus.Spec.Print.ofString "x = ", Janus.Spec.Print.decimal x.toNat, [10#8]] es) := by
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
  janus_eval_nat h_xs : XS
  janus_eval_nat h_nl : NL
  janus_eval_nat h_sm : SM
  have hxo : Outside XS 4 rt := hdo.of_dataRead (by rw [h_xs]; decide +kernel)
  have hnlo : Outside NL 1 rt := hdo.of_dataRead (by rw [h_nl]; decide +kernel)
  have hsmo : Outside SM 200 rt := hdo.of_dataRead (by rw [h_sm]; decide +kernel)
  rw [h_xs] at hxo; rw [h_nl] at hnlo; rw [h_sm] at hsmo
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
    janus_run until [segAddr P "runtime.printstring"]
    apply ReturnsK.to_reaches
    apply printstring_k impl hmm E ret hret _ k (s.sp.toNat - 32) (s.regs 28).toNat
      (s.mem.readLE ((s.regs 28).toNat + 48) 8) XS 4
    case hk =>
      rintro S2 K2 ⟨junk2, f2, v2, m2, es1, rfl, hfr2, h_rd_c2, h_rd_l2, hbi2', rfl, hem1⟩
      dsimp only at hfr2 h_rd_c2 h_rd_l2 hbi2'
      simp only [h_bi, h_bl] at hfr2 hbi2'
      apply ReturnsK.of_reaches
      janus_run until [segAddr P "runtime.printuint"]
      apply ReturnsK.to_reaches
      apply printuint_k impl hmm E ret hret _ _ (s.sp.toNat - 32) (s.regs 28).toNat
        (s.mem.readLE ((s.regs 28).toNat + 48) 8) x.toNat
      case hk =>
        rintro S3 K3 ⟨junk3, f3, v3, m3, es2, rfl, hfr3, h_rd_c3, h_rd_l3, hbi3', rfl, hem2⟩
        dsimp only at hfr3 h_rd_c3 h_rd_l3 hbi3'
        simp only [h_bi, h_bl] at hfr3 hbi3'
        apply ReturnsK.of_reaches
        janus_run until [segAddr P "runtime.printnl"]
        apply ReturnsK.to_reaches
        apply printnl_k impl hmm E ret hret _ _ (s.sp.toNat - 32) (s.regs 28).toNat
          (s.mem.readLE ((s.regs 28).toNat + 48) 8)
        case hk =>
          rintro S4 K4 ⟨junk4, f4, v4, m4, es3, rfl, hfr4, h_rd_c4, h_rd_l4, hbi4', rfl, hem3⟩
          dsimp only at hfr4 h_rd_c4 h_rd_l4 hbi4'
          simp only [h_bi, h_bl] at hfr4 hbi4'
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
            refine ⟨es1 ++ es2 ++ es3, by simp only [Kern.appendTrace_append, List.append_assoc], ?_⟩
            dsimp only at hem1 hem3
            have hx1 : readBytes m1 XS 4 = Janus.Spec.Print.ofString "x = " := by
              rw [h_xs, show readBytes m1 _ 4 = readBytes s.mem _ 4 by readbytes_frame]
              exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
            have hn3 : readBytes m3 NL 1 = [10#8] := by
              rw [h_nl, show readBytes m3 _ 1 = readBytes s.mem _ 1 by readbytes_frame]
              exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
            rw [hx1] at hem1
            rw [hn3] at hem3
            exact (hem1.append hem2).append hem3
        all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_nl]
        all_goals kobl
      all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_sm]
      all_goals try (intro j hj; janus_simp; first | done | exact readLE_of_dataRead hd (by rw [← h_sm]; exact smalls_data j hj))
      all_goals kobl
    case hsp => apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_xs]
    all_goals kobl

/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (x : BitVec 64) :
    EnsuresK (P.link impl) E Extracted.entry [x]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt)
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (Janus.Spec.Print.ofString "x = " ++ Janus.Spec.Print.decimal x.toNat ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (Janus.Spec.Print.ofString "x = " ++ Janus.Spec.Print.decimal x.toNat ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm x ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h

namespace Witness

theorem setup : CallSetup ((P.link implAt).withExit ret) Extracted.entry [42#64] (wstate (fun i => if i = 0 then 42#64 else 0)) :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    RetAddr (P.link impl) ret ∧ CallSetup ((P.link impl).withExit ret) Extracted.entry [42#64] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 16 256 s ∧ P.DataLoaded s.mem ∧ DataOutside P rt) :=
  ⟨implAt, wrt, ret, wstate (fun i => if i = 0 then 42#64 else 0), lock2_model wrt 1024, unlock2_model wrt 1024, memmove_model,
    hret, setup, ⟨ready _ 16 (Or.inl rfl), wmem_data, wrt_data⟩⟩

/-- So the guarantee is reached: from the witness state, for every kernel, `println("x =", 42)` returns and the trace gains what the three writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    ReturnsK ((P.link implAt).withExit ret) E
      (fun s' k' => FFI.ABIReturnC (wstate (fun i => if i = 0 then 42#64 else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧
          Emits 2 [Janus.Spec.Print.ofString "x = ", Janus.Spec.Print.decimal 42, [10#8]] es)
      (fun _ _ => False) (wstate (fun i => if i = 0 then 42#64 else 0)) k :=
  correctness implAt wrt E (lock2_model wrt 1024) (unlock2_model wrt 1024) memmove_model 42#64 ret hret _ k setup
    (⟨ready _ 16 (Or.inl rfl), wmem_data, wrt_data⟩)

end Witness

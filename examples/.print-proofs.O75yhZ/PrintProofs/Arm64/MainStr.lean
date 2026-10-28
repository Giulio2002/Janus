import PrintProofs.Arm64.FnPrintstring
import PrintProofs.Arm64.FnPrintnl
import PrintProofs.Arm64.FnLock
import PrintProofs.Arm64.FnWitness

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

/-!
# `println(s)` for a `string` (arm64)

```go
func PrintStr(s string) { println(s) }
```

Lowered to `printlock(); printstring(s); printnl(); printunlock()`, all executed by the model from
the binary (contracts and kernel as in `PrintX`). **Guarantee (`correctness`)**: from every call
state ready to print (`Print.PrintReady`), with the read-only data loaded and outside `rt`, and a
string `(ptr, len)` (`len < 2^31`) whose bytes are readable, outside `rt` and apart from the stack
window, the M's fields and the print backlog, the call returns and the trace gains what one
`write(2, b)` per piece of `s` (its bytes in memory at the call), `"\n"` may append.
**`full_output`**: if fd 2 grew by `len + 1` bytes, it grew by exactly the bytes of `s` and `"\n"`.
-/

namespace PrintFn.Str

/-! ## `PrintStr` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (ptr len : BitVec 64) :
    EnsuresK (P.link impl) E PrintCode.entryPrintStr [ptr, len]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt ∧ s.mem.accessible ptr.toNat len.toNat false = true ∧
        ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat < 2 ^ 31 ∧ Outside ptr.toNat len.toNat rt ∧
        Sep ptr.toNat len.toNat [(s.sp.toNat - 1088, 1112),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)])
      (fun s k _ k' => ∃ es, k' = k.appendTrace es ∧
        Emits 2 [readBytes s.mem ptr.toNat len.toNat, [10#8]] es) := by
  intro ret hret s k hs ⟨hpr, hd, hdo, hbuf, hpl, hl31, hpo, hpsep⟩
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
  obtain ⟨ap1, ap2, ap3, ap4⟩ := hpsep
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
  janus_eval_nat h_nl : NL
  have hnlo : Outside NL 1 rt := hdo.of_dataRead (by rw [h_nl]; decide +kernel)
  rw [h_nl] at hnlo
  have ap1' := ap1.symm; have ap2' := ap2.symm; have ap3' := ap3.symm; have ap4' := ap4.symm
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
    janus_run until [segAddr P "runtime.printstring"]
    apply ReturnsK.to_reaches
    apply printstring_k impl hmm E ret hret _ k (s.sp.toNat - 32) (s.regs 28).toNat
      (s.mem.readLE ((s.regs 28).toNat + 48) 8) ptr.toNat len.toNat
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
        rintro S3 K3 ⟨junk3, f3, v3, m3, ex3, ep3, es2, rfl, hfr3, h_rd_c3, h_rd_l3, hbi3', rfl, hem2⟩
        dsimp only at hfr3 h_rd_c3 h_rd_l3 hbi3'
        simp only [h_bi, h_bl] at hfr3 hbi3'
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
          refine ⟨es1 ++ es2, by simp only [Kern.appendTrace_append, List.append_assoc], ?_⟩
          dsimp only at hem1 hem2
          have hs1 : readBytes m1 ptr.toNat len.toNat = readBytes s.mem ptr.toNat len.toNat := by
            readbytes_frame
          have hn3 : readBytes m2 NL 1 = [10#8] := by
            rw [h_nl, show readBytes m2 _ 1 = readBytes s.mem _ 1 by readbytes_frame]
            exact readBytes_data hd _ _ _ (by decide +kernel) (by decide +kernel)
          rw [hs1] at hem1
          rw [hn3] at hem2
          exact Emits.append (bs := [readBytes s.mem ptr.toNat len.toNat]) hem1 hem2
      all_goals try simp only [h_pk, h_bi, h_bl, h_ow, h_nl]
      all_goals kobl
    case hsp => apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals try simp only [h_pk, h_bi, h_bl, h_ow]
    all_goals kobl

/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/
theorem full_output (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (ptr len : BitVec 64) :
    EnsuresK (P.link impl) E PrintCode.entryPrintStr [ptr, len]
      (fun s _ => PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ P.DataLoaded s.mem ∧
        DataOutside P rt ∧ s.mem.accessible ptr.toNat len.toNat false = true ∧
        ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat < 2 ^ 31 ∧ Outside ptr.toNat len.toNat rt ∧
        Sep ptr.toNat len.toNat [(s.sp.toNat - 1088, 1112),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)])
      (fun s k _ k' => (k'.output 2).length = (k.output 2).length + (readBytes s.mem ptr.toNat len.toNat ++ [10#8]).length →
        k'.output 2 = k.output 2 ++ (readBytes s.mem ptr.toNat len.toNat ++ [10#8])) := by
  intro ret hret s k hs hpre
  refine (correctness impl rt E hl hu hmm ptr len ret hret s k hs hpre).mono ?_ (fun _ _ h => h)
  rintro s' k' ⟨habi, es, rfl, hem⟩
  refine ⟨habi, fun hlen => ?_⟩
  have h := hem.full (k := k) (by simpa [List.append_assoc] using hlen)
  simpa [List.append_assoc] using h

namespace Witness

open PrintFn.Witness

theorem str_facts :
    (wstate PrintCode.entryPrintStr fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0).mem.accessible
        (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat false = true ∧
      (BitVec.ofNat 64 NL : BitVec 64).toNat + (1#64 : BitVec 64).toNat ≤ 2 ^ 48 ∧
      (1#64 : BitVec 64).toNat < 2 ^ 31 ∧
      Outside (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat wrt ∧
      Sep (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat
        [((wstate PrintCode.entryPrintStr fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0).sp.toNat - 1088, 1112),
        ((wstate PrintCode.entryPrintStr fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0).mem.readLE
          (((wstate PrintCode.entryPrintStr fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0).regs 28).toNat + 48) 8 + 264, 16),
        (BI, 8), (BL, 512)] := by
  simp only [sep_cons, sep_nil, and_true, wrt, outside_cons, outside_nil, Apart]
  repeat' apply And.intro
  all_goals decide +kernel

theorem setup : CallSetup ((P.link implAt).withExit ret) PrintCode.entryPrintStr [BitVec.ofNat 64 NL, 1#64] (wstate PrintCode.entryPrintStr (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0)) :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

/-- All hypotheses of `correctness` hold together: the witness code at the three contract
addresses, the ranges `wrt`, an admissible return address and a call state ready to print. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (ret : Nat) (s : State),
    Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt 1024 ∧
    Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt 1024 ∧
    MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove") ∧
    RetAddr (P.link impl) ret ∧ CallSetup ((P.link impl).withExit ret) PrintCode.entryPrintStr [BitVec.ofNat 64 NL, 1#64] s ∧
    (PrintReady ⟨PK, BI, BL, OW, DL⟩ rt 1088 24 256 s ∧ P.DataLoaded s.mem ∧
      DataOutside P rt ∧ s.mem.accessible (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat false = true ∧
      (BitVec.ofNat 64 NL : BitVec 64).toNat + (1#64 : BitVec 64).toNat ≤ 2 ^ 48 ∧ (1#64 : BitVec 64).toNat < 2 ^ 31 ∧
      Outside (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat rt ∧
      Sep (BitVec.ofNat 64 NL : BitVec 64).toNat (1#64 : BitVec 64).toNat [(s.sp.toNat - 1088, 1112),
        (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), (BI, 8), (BL, 512)]) :=
  ⟨implAt, wrt, ret, wstate PrintCode.entryPrintStr (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0), lock2_model wrt 1024, unlock2_model wrt 1024, memmove_model,
    hret, setup, ⟨ready _ _ 24 (Or.inr rfl), wmem_data, wrt_data, str_facts⟩⟩

/-- So the guarantee is reached: from the witness state, for every kernel, `println(s)` for the one-byte string at the program's `"\n"` returns and the trace gains what the two writes may append. -/
theorem returns (E : KEnv) (k : Kern) :
    ReturnsK ((P.link implAt).withExit ret) E
      (fun s' k' => FFI.ABIReturnC (wstate PrintCode.entryPrintStr (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0)) s' ∧
        ∃ es, k' = k.appendTrace es ∧
          Emits 2 [readBytes wmem NL 1, [10#8]] es)
      (fun _ _ => False) (wstate PrintCode.entryPrintStr (fun i => if i = 0 then BitVec.ofNat 64 NL else if i = 1 then 1#64 else 0)) k :=
  correctness implAt wrt E (lock2_model wrt 1024) (unlock2_model wrt 1024) memmove_model (BitVec.ofNat 64 NL) 1#64 ret hret _ k setup
    (⟨ready _ _ 24 (Or.inr rfl), wmem_data, wrt_data, str_facts⟩)

end Witness


end PrintFn.Str

import PrintProofs.Amd64.FnPrintstring

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## `printbool(b)` -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem printbool_k (impl : List Amd64.Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP : Nat) (bv : Bool)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr P "runtime.printbool"))
    (hsp : S.regs 4 = BitVec.ofNat 64 SP) (hg : S.regs 14 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 bv.toNat) (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (hra : S.mem.readLE SP 8 < 2 ^ 47) (hx15 : S.xmm 15 = 0)
    (hal : SP % 8 = 0) (hb : 232 ≤ SP) (ha : SP + 8 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 232) 240 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 200 < SP)
    (hgm : S.mem.accessible (G + 48) 8 false = true)
    (hwb : S.mem.accessible (G + 232) 16 false = true) (h_rd_wb : S.mem.readLE (G + 232) 8 = 0)
    (hfs1 : 8 ≤ S.fsBase.toNat) (hfs2 : S.mem.accessible (S.fsBase.toNat - 8) 8 false = true)
    (h_rd_tl : S.mem.readLE (S.fsBase.toNat - 8) 8 = G)
    (hm1 : MP + 280 ≤ 2 ^ 48) (hm2 : S.mem.accessible (MP + 264) 16 true = true)
    (h_rd_dy : S.mem.readLE (MP + 268) 4 = 0)
    (hc1 : 1 ≤ S.mem.readLE (MP + 279) 1) (hc2 : S.mem.readLE (MP + 279) 1 ≤ 125)
    (hl31m : S.mem.readLE (MP + 264) 4 + 1 < 2 ^ 31)
    (hpk : S.mem.accessible PK 4 false = true) (hbi : S.mem.accessible BI 8 true = true)
    (hbi2 : S.mem.readLE BI 8 < 512) (hbl : S.mem.accessible BL 512 true = true)
    (how : S.mem.accessible OW 8 false = true) (h_rd_ow : S.mem.readLE OW 8 = 0)
    (a1 : Apart (SP - 232) 240 (G + 16) 8) (a2 : Apart (SP - 232) 240 (G + 48) 8)
    (a3 : Apart (SP - 232) 240 (G + 232) 16) (a4 : Apart (SP - 232) 240 (MP + 264) 16)
    (a7 : Apart (SP - 232) 240 BI 8) (a8 : Apart (SP - 232) 240 BL 512)
    (a9 : Apart (SP - 232) 240 OW 8) (a10 : Apart (SP - 232) 240 (S.fsBase.toNat - 8) 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b5 : Apart (MP + 264) 16 PK 4) (b6 : Apart (MP + 264) 16 BI 8)
    (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (b9 : Apart (MP + 264) 16 (S.fsBase.toNat - 8) 8)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (d7 : Apart (S.fsBase.toNat - 8) 8 BI 8) (d8 : Apart (S.fsBase.toNat - 8) 8 BL 512)
    (a6 : Apart (SP - 232) 240 PK 4) (b3 : Apart (MP + 264) 16 (G + 232) 16)
    (hplT : TR + 4 ≤ 2 ^ 48) (hbufT : S.mem.accessible TR 4 false = true)
    (a5T : Apart (SP - 232) 240 TR 4) (b4T : Apart (MP + 264) 16 TR 4)
    (c1T : Apart TR 4 BI 8) (c2T : Apart TR 4 BL 512)
    (hplF : FA + 5 ≤ 2 ^ 48) (hbufF : S.mem.accessible FA 5 false = true)
    (a5F : Apart (SP - 232) 240 FA 5) (b4F : Apart (MP + 264) 16 FA 5)
    (c1F : Apart FA 5 BI 8) (c2F : Apart FA 5 BL 512)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 232, SP), (SP + 8, SP + 8), (MP + 264, MP + 268), (MP + 279, MP + 280),
      (BI, BI + 8), (BL, BL + 512)] MP [if bv then readBytes S.mem TR 4 else readBytes S.mem FA 5] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printbool_k
  have hspl : SP < 2 ^ 64 := by omega
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_tr : TR
  janus_eval_nat h_fa : FA
  simp only [h_tr, h_fa] at *
  janus_eval_nat h_tr : TR
  janus_eval_nat h_fa : FA
  apply Amd64.Kernel.ReturnsK.of_reaches
  cases bv
  · janus64_run [hmpE, h_tr, h_fa, Bool.toNat_false, Bool.toNat_true] until [segAddr P "runtime.printstring"]
    apply Amd64.Print.ReturnsK.to_reaches
    apply printstring_k impl hmm E ret hret _ K (SP - 32) G MP FA 5
    case hk =>
      rintro S' K' ⟨junk, f, x, yh, m, es, rfl, hf, h_rd_c, h_rd_l, hbi', rfl, hem⟩
      apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run [hmpE] until [segAddr P "runtime.printbool" + 0x3d]
      janus64_step
      apply Amd64.Print.ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, _, es, by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, callRegs64_apply, hx15], ?fr, ?_, ?_, ?_, rfl, ?_⟩
      case fr =>
        simp only [h_bi, h_bl] at hf ⊢
        refine MemFrame.trans (rs := [(SP - 232, SP)]) ?_ hf ?_
        · janus_frame
        · intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp; first | assumption | (rw [h_bi]; assumption) | (rw [h_bi] at hbi'; assumption)
      · exact emits_congr hem (by dsimp only; readbytes_frame)
    case hpc => dsimp only; rfl
    case hsp => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals try simp only [h_tr, h_fa]
    all_goals kobl64
  · janus64_run [hmpE, h_tr, h_fa, Bool.toNat_false, Bool.toNat_true] until [segAddr P "runtime.printstring"]
    apply Amd64.Print.ReturnsK.to_reaches
    apply printstring_k impl hmm E ret hret _ K (SP - 32) G MP TR 4
    case hk =>
      rintro S' K' ⟨junk, f, x, yh, m, es, rfl, hf, h_rd_c, h_rd_l, hbi', rfl, hem⟩
      apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run [hmpE] until [segAddr P "runtime.printbool" + 0x3d]
      janus64_step
      apply Amd64.Print.ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, _, es, by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, callRegs64_apply, hx15], ?fr, ?_, ?_, ?_, rfl, ?_⟩
      case fr =>
        simp only [h_bi, h_bl] at hf ⊢
        refine MemFrame.trans (rs := [(SP - 232, SP)]) ?_ hf ?_
        · janus_frame
        · intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp; first | assumption | (rw [h_bi]; assumption) | (rw [h_bi] at hbi'; assumption)
      · exact emits_congr hem (by dsimp only; readbytes_frame)
    case hpc => dsimp only; rfl
    case hsp => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals try simp only [h_tr, h_fa]
    all_goals kobl64

end PrintFn

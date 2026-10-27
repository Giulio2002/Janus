import PrintProofs.Amd64.FnFormatBase10
import PrintProofs.Amd64.FnGwrite

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem printuint_k (impl : List Amd64.Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP u : Nat)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr P "runtime.printuint"))
    (hsp : S.regs 4 = BitVec.ofNat 64 SP) (hg : S.regs 14 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 u) (hul : u < 2 ^ 64) (hmpE : S.mem.readLE (G + 48) 8 = MP)
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
    (a6 : Apart (SP - 232) 240 PK 4)
    (a7 : Apart (SP - 232) 240 BI 8) (a8 : Apart (SP - 232) 240 BL 512)
    (a9 : Apart (SP - 232) 240 OW 8) (a10 : Apart (SP - 232) 240 (S.fsBase.toNat - 8) 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b5 : Apart (MP + 264) 16 PK 4)
    (b6 : Apart (MP + 264) 16 BI 8)
    (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (b9 : Apart (MP + 264) 16 (S.fsBase.toNat - 8) 8)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (d7 : Apart (S.fsBase.toNat - 8) 8 BI 8) (d8 : Apart (S.fsBase.toNat - 8) 8 BL 512)
    (hsm : S.mem.accessible SM 200 false = true)
    (h_rdsm : ∀ j, j < 200 → S.mem.readLE (SM + j) 1 = smallsByte j)
    (aS : Apart (SP - 232) 240 SM 200)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 232, SP), (MP + 264, MP + 268), (MP + 279, MP + 280),
      (BI, BI + 8), (BL, BL + 512)] MP [Janus.Spec.Print.decimal u] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printuint_k
  have hspl : SP < 2 ^ 64 := by omega
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_sm : SM
  apply Amd64.Kernel.ReturnsK.of_reaches
  rw [h_sm] at hsm h_rdsm aS
  janus64_run [hmpE, h_sm] until [segAddr P "internal/strconv.formatBase10"]
  refine Reaches.call (Summary.withExit (formatBase10 impl) hret) rfl ?_ (fun s' hr hpost => ?_)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (intro j hj; janus64_simp; first | done | exact h_rdsm j hj)
    all_goals try kobl64
    all_goals try (janus64_simp; first | done | apart_mono | (unfold Apart at *; omega))
  · obtain ⟨i, junk, f, x, yh, m, zh, kr, rfl, hi, hfm, hrb⟩ := hpost
    revert hi hfm hrb
    janus64_simp
    intro hi hfm hrb
    have hi19 : i < 20 := by
      have := congrArg List.length hrb
      simp only [length_readBytes] at this
      have := Janus.Spec.Print.length_decimal_pos u
      omega
    have e1 := sshr_sub_and_bv i 20 hi19 (by decide)
    have e2 := neg_sub_20 i (by omega)
    have e1' : BitVec.ofNat 64 i &&& (BitVec.ofNat 64 i - 20#64).sshiftRight 63 = BitVec.ofNat 64 i := by
      rw [BitVec.and_comm]; exact e1
    janus64_run [hmpE, e1, e2] until [segAddr P "runtime.gwrite"]
    apply Amd64.Print.ReturnsK.to_reaches
    apply gwrite_k impl hmm E ret hret _ K (SP - 72) G MP (SP - 28 + i) (20 - i) (20 - i)
    case hk =>
      rintro S' K' ⟨junk', f', x', yh', m', zh', kr', es, rfl, hf', h_rd_c, h_rd_l, hbi', rfl, hem⟩
      simp only [h_bi, h_bl] at hf' hbi'
      have hfa1 : MemFrame S.mem m [(SP - 232, SP)] :=
        MemFrame.trans (rs := [(SP - 80, SP)]) (by janus_frame) hfm (by
          intro a' n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      have hfa1' : MemFrame S.mem (Arm64.Memory.writeLE m (SP - 72) 8 4483988) [(SP - 232, SP)] :=
        hfa1.writeLE _ (r := (SP - 232, SP)) (by simp) (by omega) (by omega)
      have hfa : MemFrame S.mem m' [(SP - 232, SP), (MP + 264, MP + 268), (MP + 279, MP + 280),
          (BI, BI + 8), (BL, BL + 512)] :=
        MemFrame.trans (rs := [(SP - 232, SP)]) hfa1' hf' (by
          intro a' n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; simp only [h_bi, h_bl] at h ⊢; unfold Apart at a4 a7 a8; omega)
      have h_rbp : m'.readLE (SP - 8) 8 = (S.regs 5).toNat := by
        unfold Apart at a4 a7 a8
        simp only [h_bi, h_bl] at *
        rw [hf'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          hfm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by have := (S.regs 5).isLt; simpa using this)
      apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run [hmpE] until [segAddr P "runtime.printuint" + 0x59]
      janus64_step
      apply Amd64.Print.ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, _, _, _, es, by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, callRegs64_apply, hx15, h_rbp], by simp only [h_bi, h_bl] at hfa ⊢; exact hfa, ?_, ?_, ?_, rfl, ?_⟩
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp; first | assumption | (rw [h_bi]; assumption) | (rw [h_bi] at hbi'; assumption)
      · have h := hem
        dsimp only at h
        rw [readBytes_writeLE (by omega), hrb] at h
        exact h
    case hpc => dsimp only; rfl
    case hsp => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; omega
    all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff, or_true, ite_true]; first | exact hg | rfl | (rw [e1']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega))
    all_goals first | kobl64 | skip

end PrintFn

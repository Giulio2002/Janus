import PrintProofs.Arm64.FnFormatBase10
import PrintProofs.Arm64.FnGwrite

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-! ## `printint(v)` -/

/-- The spectre mask of `printint`'s index `i - 1` (`i ≤ 20`). -/
theorem and_sshr_21 (x : Nat) (h1 : 1 ≤ x) (hx : x < 21) :
    BitVec.ofNat 64 x - 1#64 &&& (BitVec.ofNat 64 x - 21#64).sshiftRight 63 = BitVec.ofNat 64 (x - 1) := by
  have e1 : BitVec.ofNat 64 x - 1#64 = BitVec.ofNat 64 (x - 1) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  have e2 : BitVec.ofNat 64 x - 21#64 = BitVec.ofNat 64 (x - 1) - BitVec.ofNat 64 20 := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e1, e2]
  exact and_sshr_lt_bv (x - 1) 20 (by omega) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem printint_k (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP : Nat) (v : BitVec 64)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr P "runtime.printint"))
    (hsp : S.sp = BitVec.ofNat 64 SP) (hg : S.regs 28 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = v)
    (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hal : SP % 16 = 0) (hb : 248 ≤ SP) (ha : SP + 16 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 248) 264 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 208 < SP)
    (hgm : S.mem.accessible (G + 48) 8 false = true)
    (hwb : S.mem.accessible (G + 232) 16 false = true) (h_rd_wb : S.mem.readLE (G + 232) 8 = 0)
    (hm1 : MP + 280 ≤ 2 ^ 48) (hm2 : S.mem.accessible (MP + 264) 16 true = true)
    (h_rd_dy : S.mem.readLE (MP + 268) 4 = 0)
    (hc1 : 1 ≤ S.mem.readLE (MP + 279) 1) (hc2 : S.mem.readLE (MP + 279) 1 ≤ 125)
    (hpk : S.mem.accessible PK 4 false = true) (hbi : S.mem.accessible BI 8 true = true)
    (hbi2 : S.mem.readLE BI 8 < 512) (hbl : S.mem.accessible BL 512 true = true)
    (how : S.mem.accessible OW 8 false = true) (h_rd_ow : S.mem.readLE OW 8 = 0)
    (a1 : Apart (SP - 248) 264 (G + 16) 8) (a2 : Apart (SP - 248) 264 (G + 48) 8)
    (a3 : Apart (SP - 248) 264 (G + 232) 16) (a4 : Apart (SP - 248) 264 (MP + 264) 16)
    (a6 : Apart (SP - 248) 264 PK 4) (a7 : Apart (SP - 248) 264 BI 8) (a8 : Apart (SP - 248) 264 BL 512) (a9 : Apart (SP - 248) 264 OW 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b5 : Apart (MP + 264) 16 PK 4)
    (b6 : Apart (MP + 264) 16 BI 8) (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (hsm : S.mem.accessible SM 200 false = true)
    (h_rdsm : ∀ j, j < 200 → S.mem.readLE (SM + j) 1 = smallsByte j)
    (aS : Apart (SP - 248) 264 SM 200)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 248, SP - 8), (SP + 8, SP + 16), (MP + 264, MP + 268), (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] MP [Janus.Spec.Print.fmtInt v] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printint_k
  have hspl : SP < 2 ^ 64 := by omega
  janus_eval_nat h_bi : BI
  janus_eval_nat h_sm : SM
  rw [h_sm] at hsm h_rdsm aS
  apply ReturnsK.of_reaches
  janus_run [hmpE] until [segAddr P "internal/strconv.formatBase10"]
  refine Reaches.call (Summary.withExit (formatBase10 impl) hret) rfl ?_ (fun s' hr hpost => ?_)
  · refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try kobl
    all_goals try (rw [h_sm])
    all_goals try kobl
    all_goals try (intro j hj; janus_simp; first | done | exact h_rdsm j hj)
  · obtain ⟨i, junk, f, v', m, ex, ep, rfl, hi, hfm, hrb⟩ := hpost
    revert hi hfm hrb
    janus_simp
    intro hi hfm hrb
    rw [cneg_toNat] at hrb
    have hi19 : i < 20 := by
      have := congrArg List.length hrb
      simp only [length_readBytes] at this
      have := Janus.Spec.Print.length_decimal_pos v.toInt.natAbs
      omega
    have hv := v.isLt
    have hi1 : 1 ≤ i := by
      have := congrArg List.length hrb
      simp only [length_readBytes] at this
      have := length_decimal_le 18 v.toInt.natAbs (by
        rw [BitVec.toInt_eq_toNat_cond]; split <;> omega)
      omega
    by_cases hs : v.toNat < 2 ^ 63
    · janus_run [hmpE, and_sshr_20, getLsbD63, hs] until [segAddr P "runtime.gwrite"]
      apply ReturnsK.to_reaches
      apply gwrite_k impl hmm E ret hret _ K (SP - 80) G MP (SP - 28 + i) (20 - i) (20 - i)
      case hk =>
        rintro S' K' ⟨junk', f', v'', m', ex', ep', es, rfl, hf', h_rd_c, h_rd_l, hbi', rfl, hem⟩
        dsimp only at hf' h_rd_c h_rd_l hbi'
        apply ReturnsK.of_reaches
        janus_run [hmpE] until [segAddr P "runtime.printint" + 0x9c]
        janus_step
        apply ReturnsK.to_reaches
        apply hk
        refine ⟨_, _, _, _, _, _, es, by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_, rfl, ?_⟩
        · janus_simp
        · janus_simp
        · janus_simp; assumption
        · have h := hem
          dsimp only at h
          rw [hrb] at h
          unfold Janus.Spec.Print.fmtInt
          rw [if_neg (by rw [BitVec.toInt_eq_toNat_cond]; split <;> omega), List.nil_append]
          exact h
      all_goals kobl
    · janus_run [hmpE, and_sshr_20, and_sshr_21, getLsbD63, hs] until [segAddr P "runtime.gwrite"]
      apply ReturnsK.to_reaches
      apply gwrite_k impl hmm E ret hret _ K (SP - 80) G MP (SP - 28 + (i - 1)) (20 - (i - 1)) (20 - (i - 1))
      case hk =>
        rintro S' K' ⟨junk', f', v'', m', ex', ep', es, rfl, hf', h_rd_c, h_rd_l, hbi', rfl, hem⟩
        dsimp only at hf' h_rd_c h_rd_l hbi'
        apply ReturnsK.of_reaches
        janus_run [hmpE] until [segAddr P "runtime.printint" + 0x9c]
        janus_step
        apply ReturnsK.to_reaches
        apply hk
        refine ⟨_, _, _, _, _, _, es, by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_, rfl, ?_⟩
        · janus_simp
        · janus_simp
        · janus_simp; assumption
        · have h := hem
          dsimp only at h
          rw [show 20 - (i - 1) = 20 - i + 1 by omega, readBytes_one_write,
            show SP - 28 + (i - 1) + 1 = SP - 28 + i by omega, hrb] at h
          unfold Janus.Spec.Print.fmtInt
          rw [if_pos (by rw [BitVec.toInt_eq_toNat_cond]; split <;> omega),
            show Janus.Spec.Print.ofString "-" = [45#8] by decide +kernel]
          exact h
      all_goals kobl

end PrintFn

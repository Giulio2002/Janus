/-! ## `printuint(v)` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem printuint_k (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP u : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr P "runtime.printuint"))
    (hsp : S.sp = BitVec.ofNat 64 SP) (hg : S.regs 28 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 u) (hul : u < 2 ^ 64)
    (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hal : SP % 16 = 0) (hb : 248 ≤ SP) (ha : SP + 8 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 248) 256 true = true)
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
    (a1 : Apart (SP - 248) 256 (G + 16) 8) (a2 : Apart (SP - 248) 256 (G + 48) 8)
    (a3 : Apart (SP - 248) 256 (G + 232) 16) (a4 : Apart (SP - 248) 256 (MP + 264) 16)
    (a6 : Apart (SP - 248) 256 PK 4) (a7 : Apart (SP - 248) 256 BI 8) (a8 : Apart (SP - 248) 256 BL 512) (a9 : Apart (SP - 248) 256 OW 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b5 : Apart (MP + 264) 16 PK 4)
    (b6 : Apart (MP + 264) 16 BI 8) (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (hsm : S.mem.accessible SM 200 false = true)
    (h_rdsm : ∀ j, j < 200 → S.mem.readLE (SM + j) 1 = smallsByte j)
    (aS : Apart (SP - 248) 256 SM 200)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 248, SP - 8), (SP + 8, SP + 8), (MP + 264, MP + 268), (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] MP [Janus.Spec.Print.decimal u] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printuint_k
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
  · obtain ⟨i, junk, f, v, m, rfl, hi, hfm, hrb⟩ := hpost
    revert hi hfm hrb
    janus_simp
    intro hi hfm hrb
    have hi19 : i < 20 := by
      have := congrArg List.length hrb
      simp only [length_readBytes] at this
      have := Janus.Spec.Print.length_decimal_pos u
      omega
    janus_run [hmpE, and_sshr_20] until [segAddr P "runtime.gwrite"]
    apply ReturnsK.to_reaches
    apply gwrite_k impl hmm E ret hret _ K (SP - 80) G MP (SP - 28 + i) (20 - i) (20 - i)
    case hk =>
      rintro S' K' ⟨junk', f', v', m', es, rfl, hf', h_rd_c, h_rd_l, hbi', rfl, hem⟩
      apply ReturnsK.of_reaches
      janus_run [hmpE] until [segAddr P "runtime.printuint" + 0x6c]
      janus_step
      apply ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, es, by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_, rfl, ?_⟩
      · janus_simp
      · janus_simp
      · janus_simp; assumption
      · have h := hem
        dsimp only at h
        rw [hrb] at h
        exact h
    all_goals kobl

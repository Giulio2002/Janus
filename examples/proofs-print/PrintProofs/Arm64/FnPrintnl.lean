import PrintProofs.Arm64.FnPrintstring

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-! ## `printnl()` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem printnl_k (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr P "runtime.printnl"))
    (hsp : S.sp = BitVec.ofNat 64 SP) (hg : S.regs 28 = BitVec.ofNat 64 G)
    (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hal : SP % 16 = 0) (hb : 264 ≤ SP) (ha : SP + 8 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 264) 272 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 224 < SP)
    (hgm : S.mem.accessible (G + 48) 8 false = true)
    (hwb : S.mem.accessible (G + 232) 16 false = true) (h_rd_wb : S.mem.readLE (G + 232) 8 = 0)
    (hm1 : MP + 280 ≤ 2 ^ 48) (hm2 : S.mem.accessible (MP + 264) 16 true = true)
    (h_rd_dy : S.mem.readLE (MP + 268) 4 = 0)
    (hc1 : 1 ≤ S.mem.readLE (MP + 279) 1) (hc2 : S.mem.readLE (MP + 279) 1 ≤ 125)
    (hpk : S.mem.accessible PK 4 false = true) (hbi : S.mem.accessible BI 8 true = true)
    (hbi2 : S.mem.readLE BI 8 < 512) (hbl : S.mem.accessible BL 512 true = true)
    (how : S.mem.accessible OW 8 false = true) (h_rd_ow : S.mem.readLE OW 8 = 0)
    (a1 : Apart (SP - 264) 272 (G + 16) 8) (a2 : Apart (SP - 264) 272 (G + 48) 8)
    (a3 : Apart (SP - 264) 272 (G + 232) 16) (a4 : Apart (SP - 264) 272 (MP + 264) 16)
    (a6 : Apart (SP - 264) 272 PK 4) (a7 : Apart (SP - 264) 272 BI 8) (a8 : Apart (SP - 264) 272 BL 512) (a9 : Apart (SP - 264) 272 OW 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b5 : Apart (MP + 264) 16 PK 4)
    (b6 : Apart (MP + 264) 16 BI 8) (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (hpl : NL + 1 ≤ 2 ^ 48) (hl31 : 1 < 2 ^ 31)
    (hbuf : S.mem.accessible NL 1 false = true)
    (a5 : Apart (SP - 264) 272 NL 1) (b4 : Apart (MP + 264) 16 NL 1)
    (c1 : Apart NL 1 BI 8) (c2 : Apart NL 1 BL 512)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 264, SP - 8), (SP + 8, SP + 8), (MP + 264, MP + 268), (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] MP [readBytes S.mem NL 1] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printnl_k
  have hspl : SP < 2 ^ 64 := by omega
  janus_eval_nat h_bi : BI
  janus_eval_nat h_nl : NL
  apply ReturnsK.of_reaches
  janus_run [hmpE, h_nl] until [segAddr P "runtime.printstring"]
  apply ReturnsK.to_reaches
  apply printstring_k impl hmm E ret hret _ K (SP - 32) G MP NL 1
  case hk =>
    rintro S' K' ⟨junk, f, v, m, ex, ep, es, rfl, hf, h_rd_c, h_rd_l, hbi', rfl, hem⟩
    apply ReturnsK.of_reaches
    janus_run [hmpE] until [segAddr P "runtime.printnl" + 0x30]
    janus_step
    apply ReturnsK.to_reaches
    apply hk
    refine ⟨_, _, _, _, _, _, es, by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_, rfl, ?_⟩
    · janus_simp
    · janus_simp
    · janus_simp; (first | with_reducible assumption | assumption)
    · exact emits_congr hem (by dsimp only; readbytes_frame)
  all_goals kobl

end PrintFn

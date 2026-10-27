import PrintProofs.Amd64.FnGwrite

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## `printstring(s)` -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem printstring_k (impl : List Amd64.Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP ptr len : Nat)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr P "runtime.printstring"))
    (hsp : S.regs 4 = BitVec.ofNat 64 SP) (hg : S.regs 14 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 ptr) (hx3 : S.regs 3 = BitVec.ofNat 64 len) (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (hra : S.mem.readLE SP 8 < 2 ^ 47) (hx15 : S.xmm 15 = 0)
    (hal : SP % 8 = 0) (hb : 200 ≤ SP) (ha : SP + 16 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 200) 216 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 168 < SP)
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
    (hpl : ptr + len ≤ 2 ^ 48) (hl31 : len < 2 ^ 31)
    (hbuf : S.mem.accessible ptr len false = true)
    (a1 : Apart (SP - 200) 216 (G + 16) 8) (a2 : Apart (SP - 200) 216 (G + 48) 8)
    (a3 : Apart (SP - 200) 216 (G + 232) 16) (a4 : Apart (SP - 200) 216 (MP + 264) 16)
    (a5 : Apart (SP - 200) 216 ptr len) (a6 : Apart (SP - 200) 216 PK 4)
    (a7 : Apart (SP - 200) 216 BI 8) (a8 : Apart (SP - 200) 216 BL 512)
    (a9 : Apart (SP - 200) 216 OW 8) (a10 : Apart (SP - 200) 216 (S.fsBase.toNat - 8) 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b4 : Apart (MP + 264) 16 ptr len)
    (b5 : Apart (MP + 264) 16 PK 4) (b6 : Apart (MP + 264) 16 BI 8)
    (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (b9 : Apart (MP + 264) 16 (S.fsBase.toNat - 8) 8)
    (c1 : Apart ptr len BI 8) (c2 : Apart ptr len BL 512)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
    (d7 : Apart (S.fsBase.toNat - 8) 8 BI 8) (d8 : Apart (S.fsBase.toNat - 8) 8 BL 512)
    (Q : State → Kern → Prop) (X : Nat → Kern → Prop)
    (hk : ∀ S' K', PPost [(SP - 200, SP), (SP + 8, SP + 16), (MP + 264, MP + 268), (MP + 279, MP + 280),
      (BI, BI + 8), (BL, BL + 512)] MP [readBytes S.mem ptr len] S K S' K' →
      ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF printstring_k
  have hspl : SP < 2 ^ 64 := by omega
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_run [hmpE] until [segAddr P "runtime.gwrite"]
  apply Amd64.Print.ReturnsK.to_reaches
  apply gwrite_k impl hmm E ret hret _ K (SP - 56) G MP ptr len len
  case hk =>
    rintro S' K' ⟨junk, f, x, yh, m, zh, kr, es, rfl, hf, h_rd_c, h_rd_l, hbi', rfl, hem⟩
    apply Amd64.Kernel.ReturnsK.of_reaches
    janus64_run [hmpE] until [segAddr P "runtime.printstring" + 0x2f]
    janus64_step
    apply Amd64.Print.ReturnsK.to_reaches
    apply hk
    refine ⟨_, _, _, _, _, _, _, es, by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, callRegs64_apply, hx15], by simp only [h_bi, h_bl] at hf ⊢; janus_frame, ?_, ?_, ?_, rfl, ?_⟩
    · dsimp only; janus64_simp
    · dsimp only; janus64_simp
    · dsimp only; janus64_simp; first | assumption | (rw [h_bi]; assumption) | (rw [h_bi] at hbi'; assumption)
    · exact emits_congr hem (by dsimp only; readbytes_frame)
  case hpc => dsimp only; rfl
  case hsp => dsimp only; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; omega
  all_goals kobl64

end PrintFn

/-- What a print function guarantees (amd64), from its call state `S`, `K` to its return state
`S'`, `K'`: the return (`retState64`), memory changed only in `W`, the M's print count and
`m.locks` as they were, the backlog index in range, and the trace extended by what one
`write(2, b)` per piece `b` of `bs` may append. -/
@[reducible] def PPost (W : List (Nat × Nat)) (MP : Nat) (bs : List Bytes) (S : State) (K : Kern)
    (S' : State) (K' : Kern) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (es : List Event),
    S' = retState64 S junk [] f x yh m ∧ MemFrame S.mem m W ∧
    m.readLE (MP + 279) 1 = S.mem.readLE (MP + 279) 1 ∧
    m.readLE (MP + 264) 4 = S.mem.readLE (MP + 264) 4 ∧ m.readLE BI 8 < 512 ∧
    K' = K.appendTrace es ∧ Emits 2 bs es

/-! ## `gwrite(b)`: one `write(2, b)` (kernel level) -/

/-- What `gwrite(b)` guarantees (see `PPost`): memory changed only in its stack window
`[SP - 144, SP)`, its argument spill slots, the M's `locks` and print count, the backlog and its
index. -/
def GwPost (SP MP ptr len : Nat) (S : State) (K : Kern) (S' : State) (K' : Kern) : Prop :=
  PPost [(SP - 144, SP), (SP + 8, SP + 24), (MP + 264, MP + 268), (MP + 279, MP + 280), (BI, BI + 8),
    (BL, BL + 512)] MP [readBytes S.mem ptr len] S K S' K'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem gwrite_k (impl : List Amd64.Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP ptr len cap : Nat)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr P "runtime.gwrite"))
    (hsp : S.regs 4 = BitVec.ofNat 64 SP) (hg : S.regs 14 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 ptr) (hx3 : S.regs 3 = BitVec.ofNat 64 len)
    (hx1 : S.regs 1 = BitVec.ofNat 64 cap) (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (hra : S.mem.readLE SP 8 < 2 ^ 47) (hx15 : S.xmm 15 = 0)
    (hal : SP % 8 = 0) (hb : 144 ≤ SP) (ha : SP + 24 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 144) 168 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 112 < SP)
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
    (hpl : ptr + len ≤ 2 ^ 48) (hlc : len ≤ cap) (hcap : cap < 2 ^ 48) (hl31 : len < 2 ^ 31)
    (hbuf : S.mem.accessible ptr len false = true)
    (a1 : Apart (SP - 144) 168 (G + 16) 8) (a2 : Apart (SP - 144) 168 (G + 48) 8)
    (a3 : Apart (SP - 144) 168 (G + 232) 16) (a4 : Apart (SP - 144) 168 (MP + 264) 16)
    (a5 : Apart (SP - 144) 168 ptr len) (a6 : Apart (SP - 144) 168 PK 4)
    (a7 : Apart (SP - 144) 168 BI 8) (a8 : Apart (SP - 144) 168 BL 512)
    (a9 : Apart (SP - 144) 168 OW 8) (a10 : Apart (SP - 144) 168 (S.fsBase.toNat - 8) 8)
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
    (hk : ∀ S' K', GwPost SP MP ptr len S K S' K' → ReturnsK ((P.link impl).withExit ret) E Q X S' K') :
    ReturnsK ((P.link impl).withExit ret) E Q X S K := by
  -- PROOF gwrite_k
  have hspl : SP < 2 ^ 64 := by omega
  have hl32 : len % 4294967296 = len := Nat.mod_eq_of_lt (by omega)
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_ow : OW
  simp only [h_pk, h_bi, h_bl, h_ow] at *
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  janus_eval_nat h_ow : OW
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31] until [segAddr P "runtime.gwrite" + 0xd9, segAddr P "runtime.gwrite" + 0xef, segAddr P "runtime.gwrite" + 0xf5]
    calls [recordForPanic impl hmm]
  -- the return without a write (`len(b) = 0`)
  · janus64_step
    apply Amd64.Print.ReturnsK.to_reaches
    apply hk
    refine ⟨_, _, _, _, _, [], by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl], by janus_frame, ?_, ?_, ?_,
      (Kern.appendTrace_nil K).symm, emits_fail _⟩
    all_goals (dsimp only; janus64_simp; try omega)
    rw [h_bi]; assumption
  -- the `write(2, b, len)` system call in `write1`
  refine ⟨.syscall, by kernel_site64, Or.inl ⟨⟨.write, by simp [sysOf, Sys.ofAmd64, setRegF], by decide, ?_⟩, ?_⟩⟩
  · simp [Safe, Buf, Amd64.Kernel.argsOf, setRegF, Nat.mod_eq_of_lt (show ptr < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    simp only [hl32, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    right; janus64_disch
  · rintro s' k' ⟨sc, m', r, r11, hsc, heff, rfl⟩
    simp [sysOf, Sys.ofAmd64, setRegF] at hsc
    subst hsc
    simp only [Effect, Amd64.Kernel.argsOf, setRegF] at heff
    obtain ⟨rfl, ⟨c, hc, rfl, rfl⟩ | ⟨⟨he1, he2⟩, rfl⟩⟩ := heff
    all_goals name_reads
    · apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31] until
        [segAddr P "runtime.gwrite" + 0xd9, segAddr P "runtime.gwrite" + 0xef, segAddr P "runtime.gwrite" + 0xf5]
      janus64_step
      apply Amd64.Print.ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, _, [_], by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, setXmmF, hx15], by simp only [h_bi, h_bl]; janus_frame, ?_, ?_, ?_, rfl, ?_⟩
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp; rw [h_bi]; assumption
      · simp [Nat.mod_eq_of_lt (show ptr < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega),
          hl32, setRegF] at hc ⊢
        exact emits_of_eq (n := len) (by readbytes_frame) (by omega)
    · apply Amd64.Kernel.ReturnsK.of_reaches
      janus64_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31] until
        [segAddr P "runtime.gwrite" + 0xd9, segAddr P "runtime.gwrite" + 0xef, segAddr P "runtime.gwrite" + 0xf5]
      janus64_step
      apply Amd64.Print.ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, _, [], by ret_state64 [hsp, hg, Nat.mod_eq_of_lt hspl, setXmmF, hx15], by simp only [h_bi, h_bl]; janus_frame, ?_, ?_, ?_,
        (Kern.appendTrace_nil _).symm, emits_fail _⟩
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp
      · dsimp only; janus64_simp; rw [h_bi]; assumption

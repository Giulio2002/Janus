/-- What a print function guarantees, from its call state `S`, `K` to its return state `S'`, `K'`:
the return (`retState`), memory changed only in `W` (its stack window and arguments, the M's
`locks` and print count, the backlog and its index), the M's print count and `m.locks` as they were,
the backlog index in range, and the trace extended by what one `write(2, b)` per piece `b` of `bs`
may append. -/
@[reducible] def PPost (W : List (Nat × Nat)) (MP : Nat) (bs : List Bytes) (S : State) (K : Kern)
    (S' : State) (K' : Kern) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (es : List Event),
    S' = retState S junk [] f v m ∧ MemFrame S.mem m W ∧
    m.readLE (MP + 279) 1 = S.mem.readLE (MP + 279) 1 ∧
    m.readLE (MP + 264) 4 = S.mem.readLE (MP + 264) 4 ∧ m.readLE BI 8 < 512 ∧
    K' = K.appendTrace es ∧ Emits 2 bs es

/-! ## `gwrite(b)`: one `write(2, b)` (kernel level) -/

/-- What `gwrite(b)` guarantees, from the call state `S`, `K` to the return state `S'`, `K'`:
the return (`retState`), memory changed only in `gwW`, the M's print count and `m.locks` as they
were, the backlog index in range, and the trace extended by what one `write(2, b)` may append. -/
def GwPost (SP MP ptr len : Nat) (S : State) (K : Kern) (S' : State) (K' : Kern) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (es : List Event),
    S' = retState S junk [] f v m ∧
    MemFrame S.mem m [(SP - 168, SP - 8), (SP + 8, SP + 24), (MP + 264, MP + 268),
      (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] ∧
    m.readLE (MP + 279) 1 = S.mem.readLE (MP + 279) 1 ∧
    m.readLE (MP + 264) 4 = S.mem.readLE (MP + 264) 4 ∧ m.readLE BI 8 < 512 ∧
    K' = K.appendTrace es ∧ Emits 2 [readBytes S.mem ptr len] es

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem gwrite_k (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) (E : KEnv)
    (ret : Nat) (hret : RetAddr (P.link impl) ret) (S : State) (K : Kern)
    (SP G MP ptr len cap : Nat)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr P "runtime.gwrite"))
    (hsp : S.sp = BitVec.ofNat 64 SP) (hg : S.regs 28 = BitVec.ofNat 64 G)
    (hx0 : S.regs 0 = BitVec.ofNat 64 ptr) (hx1 : S.regs 1 = BitVec.ofNat 64 len)
    (hx2 : S.regs 2 = BitVec.ofNat 64 cap) (hmpE : S.mem.readLE (G + 48) 8 = MP)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hal : SP % 16 = 0) (hb : 168 ≤ SP) (ha : SP + 24 ≤ 2 ^ 48)
    (hw : S.mem.accessible (SP - 168) 192 true = true)
    (hg0 : 0 < G) (hg1 : G + 256 ≤ 2 ^ 48) (hg2 : S.mem.accessible (G + 16) 8 false = true)
    (hg3 : S.mem.readLE (G + 16) 8 + 128 < SP)
    (hgm : S.mem.accessible (G + 48) 8 false = true)
    (hwb : S.mem.accessible (G + 232) 16 false = true) (h_rd_wb : S.mem.readLE (G + 232) 8 = 0)
    (hm1 : MP + 280 ≤ 2 ^ 48) (hm2 : S.mem.accessible (MP + 264) 16 true = true)
    (h_rd_dy : S.mem.readLE (MP + 268) 4 = 0)
    (hc1 : 1 ≤ S.mem.readLE (MP + 279) 1) (hc2 : S.mem.readLE (MP + 279) 1 ≤ 125)
    (hpk : S.mem.accessible PK 4 false = true) (hbi : S.mem.accessible BI 8 true = true)
    (hbi2 : S.mem.readLE BI 8 < 512) (hbl : S.mem.accessible BL 512 true = true)
    (how : S.mem.accessible OW 8 false = true) (h_rd_ow : S.mem.readLE OW 8 = 0)
    (hpl : ptr + len ≤ 2 ^ 48) (hlc : len ≤ cap) (hcap : cap ≤ 2 ^ 48) (hl31 : len < 2 ^ 31)
    (hbuf : S.mem.accessible ptr len false = true)
    (a1 : Apart (SP - 168) 192 (G + 16) 8) (a2 : Apart (SP - 168) 192 (G + 48) 8)
    (a3 : Apart (SP - 168) 192 (G + 232) 16) (a4 : Apart (SP - 168) 192 (MP + 264) 16)
    (a5 : Apart (SP - 168) 192 ptr len) (a6 : Apart (SP - 168) 192 PK 4)
    (a7 : Apart (SP - 168) 192 BI 8) (a8 : Apart (SP - 168) 192 BL 512)
    (a9 : Apart (SP - 168) 192 OW 8)
    (b1 : Apart (MP + 264) 16 (G + 16) 8) (b2 : Apart (MP + 264) 16 (G + 48) 8)
    (b3 : Apart (MP + 264) 16 (G + 232) 16) (b4 : Apart (MP + 264) 16 ptr len)
    (b5 : Apart (MP + 264) 16 PK 4) (b6 : Apart (MP + 264) 16 BI 8)
    (b7 : Apart (MP + 264) 16 BL 512) (b8 : Apart (MP + 264) 16 OW 8)
    (c1 : Apart ptr len BI 8) (c2 : Apart ptr len BL 512)
    (d1 : Apart (G + 16) 8 BI 8) (d2 : Apart (G + 16) 8 BL 512)
    (d3 : Apart (G + 48) 8 BI 8) (d4 : Apart (G + 48) 8 BL 512)
    (d5 : Apart (G + 232) 16 BI 8) (d6 : Apart (G + 232) 16 BL 512)
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
  apply ReturnsK.of_reaches
  janus_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31] until [segAddr P "runtime.gwrite" + 0xac, segAddr P "runtime.gwrite" + 0xc8,
      segAddr P "runtime.gwrite" + 0xd4]
    calls [recordForPanic impl hmm]
  -- the return without a write (`len(b) = 0`)
  · janus_step
    apply ReturnsK.to_reaches
    apply hk
    refine ⟨_, _, _, _, [], by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_,
      (Kern.appendTrace_nil K).symm, emits_fail _⟩
    · janus_simp
    · janus_simp
    · janus_simp; rw [h_bi]; assumption
  -- the `write(2, b, len)` system call in `write1`
  refine ⟨.svc, by kernel_site, Or.inl ⟨⟨.write, by simp [svcSys, Sys.ofArm64, setReg], by decide, ?_⟩, ?_⟩⟩
  · simp [Safe, Buf, argsOf, setReg, Nat.mod_eq_of_lt (show ptr < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    right; janus_disch
  · rintro s' k' ⟨sc, m', r, hsc, heff, rfl⟩
    simp [svcSys, Sys.ofArm64, setReg] at hsc
    subst hsc
    simp only [Effect, argsOf, setReg_apply] at heff
    obtain ⟨rfl, ⟨c, hc, rfl, rfl⟩ | ⟨⟨he1, he2⟩, rfl⟩⟩ := heff
    all_goals name_reads
    · apply ReturnsK.of_reaches
      janus_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31, addWithCarry_c] until
        [segAddr P "runtime.writeErrData" + 0x70, segAddr P "runtime.gwrite" + 0xac, segAddr P "runtime.gwrite" + 0xc8, segAddr P "runtime.gwrite" + 0xd4]
      janus_step
      apply ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, [_], by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_, rfl, ?_⟩
      · janus_simp
      · janus_simp
      · janus_simp; rw [h_bi]; assumption
      · simp [Nat.mod_eq_of_lt (show ptr < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega),
          hl32] at hc ⊢
        exact emits_of_eq (by readbytes_frame) (by omega)
    · apply ReturnsK.of_reaches
      janus_run [hmpE, h_pk, h_bi, h_bl, h_ow, sep_cons, sep_nil, hl32, hl31, addWithCarry_c] until
        [segAddr P "runtime.writeErrData" + 0x70, segAddr P "runtime.gwrite" + 0xac, segAddr P "runtime.gwrite" + 0xc8, segAddr P "runtime.gwrite" + 0xd4]
      janus_step
      apply ReturnsK.to_reaches
      apply hk
      refine ⟨_, _, _, _, [], by ret_state [hsp, hg], by janus_frame, ?_, ?_, ?_,
        (Kern.appendTrace_nil _).symm, emits_fail _⟩
      · janus_simp
      · janus_simp
      · janus_simp; rw [h_bi]; assumption

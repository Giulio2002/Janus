import PrintProofs.Amd64.FnPrintlock

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## `recordForPanic(b)`: the copy of every piece into the crash backlog -/

/-- What `recordForPanic(b)` needs at its entry `s` (`RAX, RBX, RCX = b`): the stack, `g` and its
M with print count `1 ≤ c ≤ 125`, the globals, `b` readable, and the written ranges apart from
everything read. -/
def RfpPre (s : State) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ (s.regs 4).toNat % 8 = 0 ∧ 80 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 32 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 80) 112 true = true ∧
    (s.regs 14).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 56 < (s.regs 4).toNat ∧
    s.mem.accessible ((s.regs 14).toNat + 48) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 16 true = true ∧
    1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 ∧
    s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 ≤ 125 ∧
    s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4 + 1 < 2 ^ 31 ∧
    s.mem.accessible PK 4 false = true ∧ s.mem.accessible BI 8 true = true ∧
    s.mem.readLE BI 8 < 512 ∧ s.mem.accessible BL 512 true = true ∧
    (s.regs 0).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧ (s.regs 3).toNat ≤ (s.regs 1).toNat ∧
    (s.regs 1).toNat < 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (s.regs 3).toNat false = true ∧
    -- the stack window, the M's fields, `b` and `g`'s fields apart from each other and the globals
    Sep ((s.regs 4).toNat - 80) 112 [((s.regs 14).toNat + 16, 8), ((s.regs 14).toNat + 48, 8),
      (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, 16), ((s.regs 0).toNat, (s.regs 3).toNat),
      (PK, 4), (BI, 8), (BL, 512)] ∧
    Sep (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 16 [((s.regs 14).toNat + 16, 8),
      ((s.regs 14).toNat + 48, 8), ((s.regs 0).toNat, (s.regs 3).toNat), (PK, 4), (BI, 8), (BL, 512)] ∧
    Sep (s.regs 0).toNat (s.regs 3).toNat [(BI, 8), (BL, 512)] ∧
    Sep ((s.regs 14).toNat + 16) 8 [(BI, 8), (BL, 512)] ∧
    Sep ((s.regs 14).toNat + 48) 8 [(BI, 8), (BL, 512)]

/-- What `recordForPanic` guarantees: the return, memory changed only in its stack window and
argument spill slots, the M's `locks` and print count (restored), the backlog and its index (kept
in range). -/
@[reducible] def RfpPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [] f x yh m zh kr ∧
    MemFrame s.mem m [((s.regs 4).toNat - 80, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 32),
      (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 14).toNat + 48) 8 + 268),
      (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 14).toNat + 48) 8 + 280),
      (BI, BI + 8), (BL, BL + 512)] ∧
    m.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 =
      s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 279) 1 ∧
    m.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4 =
      s.mem.readLE (s.mem.readLE ((s.regs 14).toNat + 48) 8 + 264) 4 ∧
    m.readLE BI 8 < 512

set_option hygiene false in
/-- Close `RfpPost s s'` at the return (inside `recordForPanic`'s proof). -/
macro "rfp_post" : tactic => `(tactic| (
  unfold RfpPost
  simp only [hsp, hg, hx0, hx1, hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl, Nat.mod_eq_of_lt hgl,
    hmpE, h_bi, h_bl]
  refine ⟨_, _, _, _, _, _, _, by ret_state64 [hsp, hsp', hbp', hg', hg, hx15, hfs, hdf, hmx, hx87, hfw, Nat.mod_eq_of_lt hspl, callRegs64_apply], by janus_frame, ?_, ?_, ?_⟩ <;>
    (dsimp only; janus64_simp; all_goals first | omega | (split <;> omega) | (simp only [h_bi] at hidx; exact hidx) | assumption)))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
theorem recordForPanic (impl : List Amd64.Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    Summary (P.link impl) (segAddr P "runtime.recordForPanic") RfpPre RfpPost := by
  -- PROOF recordForPanic
  intro s hpc hpre
  unfold RfpPre at hpre
  obtain ⟨hra, hal, hb, ha, hw, hg1, hg2, hg3, hgm2, hm1, hm2, hc1, hc2, hl31, hpk, hbi,
    hbi2, hbl, hpl, hlc, hcap, hbuf, ho1, ho2, ho3, ho4, ho5⟩ := hpre
  simp only [sep_cons, sep_nil, and_true] at ho1 ho2 ho3 ho4 ho5
  split_ands
  have hsp : s.regs 4 = BitVec.ofNat 64 (s.regs 4).toNat := by simp
  have hg : s.regs 14 = BitVec.ofNat 64 (s.regs 14).toNat := by simp
  have hx0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have hx3 : s.regs 3 = BitVec.ofNat 64 (s.regs 3).toNat := by simp
  have hx1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by simp
  have hspl := (s.regs 4).isLt
  have hgl := (s.regs 14).isLt
  have hx1l := (s.regs 1).isLt
  generalize (s.regs 4).toNat = SP at *
  generalize (s.regs 14).toNat = G at *
  generalize (s.regs 0).toNat = ptr at *
  generalize (s.regs 3).toNat = len at *
  generalize (s.regs 1).toNat = cap at *
  generalize hmpE : s.mem.readLE (G + 48) 8 = MP at *
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  simp only [h_pk, h_bi, h_bl] at *
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  have hnz : (s.mem.readLE (MP + 279) 1 % 256 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; omega
  have loop : ∀ k (S : State) (i : Nat), len - i ≤ k → i ≤ len →
      S.rip = BitVec.ofNat 64 (segAddr P "runtime.recordForPanic" + 0xa1) →
      S.regs 4 = BitVec.ofNat 64 SP - 48#64 → S.regs 5 = BitVec.ofNat 64 SP - 8#64 →
      S.regs 14 = BitVec.ofNat 64 G →
      S.regs 0 = BitVec.ofNat 64 i → S.regs 7 = BitVec.ofNat 64 len →
      S.regs 2 = BitVec.ofNat 64 cap → S.regs 6 = BitVec.ofNat 64 ptr →
      MemFrame s.mem S.mem [(SP - 80, SP), (SP + 8, SP + 32), (MP + 264, MP + 268),
        (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] →
      S.mem.readLE (SP - 8) 8 = (s.regs 5).toNat →
      S.mem.readLE (SP + 8) 8 = ptr → S.mem.readLE (SP + 16) 8 = len →
      S.mem.readLE (SP + 24) 8 = cap →
      S.mem.readLE (MP + 279) 1 = s.mem.readLE (MP + 279) 1 + 1 →
      S.mem.readLE (MP + 264) 4 = s.mem.readLE (MP + 264) 4 →
      S.mem.readLE BI 8 < 512 →
      S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df → S.mxcsr = s.mxcsr → S.x87 = s.x87 → S.fpucw = s.fpucw →
      ReachesRet (P.link impl) (retAddrOf s) S (RfpPost s) := by
    intro k
    induction k with
    | zero =>
      intro S i hk hi hpc' hsp' hbp' hg' h0 h7 h2 h6 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 hidx hx15 hfs hdf hmx hx87 hfw
      janus64_run [hmpE, zx8_chain, ofNat8_eq_zero_iff, hnz]
      all_goals rfp_post
    | succ k ih =>
      intro S i hk hi hpc' hsp' hbp' hg' h0 h7 h2 h6 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 hidx hx15 hfs hdf hmx hx87 hfw
      simp only [h_bi] at *
      janus_eval_nat h_bi : BI
      by_cases hle : len ≤ i
      · have hil' : i = len := by omega
        subst hil'
        janus64_run [hmpE, zx8_chain, ofNat8_eq_zero_iff, hnz]
        all_goals rfp_post
      have hil : i < len := by omega
      have e1 := sshr_sub_and (S.mem.readLE BI 8) 512 (by rw [h_bi]; exact hidx) (by decide)
      have e2 := sshr_sub_and i cap (by omega) (by omega)
      have e4 := toNat_sub_small len i (by omega) (by omega)
      have e5 := neg_sub_512 (S.mem.readLE BI 8) (by rw [h_bi]; exact hidx)
      have e3 : ((BitVec.ofNat 64 len - BitVec.ofNat 64 i).toInt <
          (0#64 - (BitVec.ofNat 64 (S.mem.readLE BI 8) - 512#64)).toInt) =
          (len - i < 512 - S.mem.readLE BI 8) := by
        rw [toInt_small _ (by rw [e4]; omega), toInt_small _ (by rw [e5]; omega), e4, e5]
        simp only [Int.ofNat_lt]
      have e1b := sshr_sub_and_bv (S.mem.readLE BI 8) 512 (by rw [h_bi]; exact hidx) (by decide)
      have e2b := sshr_sub_and_bv i cap (by omega) (by omega)
      have e6 := ofNat_add_sub (S.mem.readLE BI 8) len i (by omega) (by rw [h_bi]; omega)
      have e7 := sshr63_small (S.mem.readLE BI 8 + (len - i)) (by rw [h_bi]; omega)
      have e6' := ofNat_add_neg512 (S.mem.readLE BI 8) (by rw [h_bi]; exact hidx)
      have e7' := sshr63_small 512 (by decide)
      have e8 := BitVec.ofNat_add_ofNat (n := 64) (S.mem.readLE BI 8) (len - i)
      rw [h_bi] at e1 e3 e5 e1b e6 e7 e6' e8
      have hsepb : Apart ptr len BL 512 := by simp only [h_bl]; assumption
      rw [h_bl] at hsepb
      unfold Apart at hsepb
      -- `printBacklog`'s address as a variable: the code computes it as a literal (`LEAQ`), on
      -- which the flag computations of a `CMP` would otherwise be evaluated
      obtain ⟨BLv, hBLv⟩ : ∃ v, BL = v := ⟨_, rfl⟩
      have hlit : (BitVec.ofNat 64 BL : BitVec 64) = BitVec.ofNat 64 BLv := by rw [hBLv]
      rw [h_bl] at hlit
      -- its value only as bounds (an equation would be a rewrite rule against `hlit`)
      have hBLb : BL ≤ BLv ∧ BLv ≤ BL := by omega
      rw [h_bl] at hBLb
      clear h_bl
      have hne : (BitVec.ofNat 64 ptr + BitVec.ofNat 64 i =
          BitVec.ofNat 64 (S.mem.readLE BI 8) + BitVec.ofNat 64 BLv) = False := by
        simp only [eq_iff_iff, iff_false]
        intro h
        have h' := congrArg BitVec.toNat h
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
        rw [h_bi] at h'
        omega
      rw [h_bi] at hne
      rw [hBLv] at hf
      have e9 := BitVec.ofNat_add_ofNat (n := 64) ptr i
      have e10 := BitVec.ofNat_add_ofNat (n := 64) (S.mem.readLE BI 8) BLv
      rw [h_bi] at e10
      have e11 : BitVec.ofNat 64 (S.mem.readLE BI 8) + BitVec.ofNat 64 (512 - S.mem.readLE BI 8) = 512#64 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [h_bi]; omega
      rw [h_bi] at e11
      by_cases hmin : len - i < 512 - S.mem.readLE BI 8 <;> rw [h_bi] at hmin
      · janus64_run [hmin, hmpE, zx8_chain, ofNat8_eq_zero_iff, hnz, e1, e2, e3, e4, e5, Int.ofNat_lt,
          e1b, e2b, e6, e7, e6', e7', BitVec.zero_ushiftRight, andmask512_nat, e8, hne, e9, e10, hlit]
          until [segAddr P "runtime.recordForPanic" + 0xa1] calls [hmm]
        clear hlit e9 e10 e8 e6 e6' hne e1 e1b e2 e2b e3 e4 e5 e7 e7'
        all_goals refine ih _ len (by omega) (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals try (rw [hBLv]; janus_frame)
        all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply]; first | with_reducible assumption | with_reducible rfl)
        all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]; omega)
        all_goals try with_reducible assumption
        case refine_1 => dsimp only; rfl
        all_goals try (janus64_simp; done)
        all_goals try (janus64_simp; omega)
      · janus64_run [hmin, hmpE, zx8_chain, ofNat8_eq_zero_iff, hnz, e1, e2, e3, e4, e5, Int.ofNat_lt,
          e1b, e2b, e6, e7, e6', e7', BitVec.zero_ushiftRight, andmask512_nat, e8, hne, e9, e10, hlit, e11]
          until [segAddr P "runtime.recordForPanic" + 0xa1] calls [hmm]
        clear hlit e11 e9 e10 e8 e6 e6' hne e1 e1b e2 e2b e3 e4 e5 e7 e7'
        all_goals refine ih _ (i + (512 - S.mem.readLE BI 8)) (by rw [h_bi]; omega) (by rw [h_bi]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals try (rw [h_bi]; dsimp only; simp only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]; omega)
        all_goals try (rw [hBLv]; janus_frame)
        all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply]; first | with_reducible assumption | with_reducible rfl)
        all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]; omega)
        all_goals try with_reducible assumption
        case refine_1 => dsimp only; rfl
        all_goals try (janus64_simp; done)
        all_goals try (janus64_simp; omega)
  janus64_run [hmpE, zx8_chain, ofNat8_eq_zero_iff, hnz] until [segAddr P "runtime.recordForPanic" + 0xa1]
    calls [printlock_held impl]
  all_goals first
    | refine loop _ _ 0 (Nat.le_refl _) (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | (have hsp' := hsp; have hbp' : s.regs 5 = s.regs 5 := rfl; have hg' := hg
       have hx15 : s.xmm 15 = s.xmm 15 := rfl; have hfs : s.fsBase = s.fsBase := rfl
       have hdf : s.df = s.df := rfl; have hmx : s.mxcsr = s.mxcsr := rfl; have hx87 : s.x87 = s.x87 := rfl; have hfw : s.fpucw = s.fpucw := rfl
       have hidx := hbi2
       rfp_post)
  all_goals try simp only [h_bi]
  all_goals try (simp only [h_bl]; janus_frame)
  all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply]; first | with_reducible assumption | with_reducible rfl)
  all_goals try (dsimp only; simp only [setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]; omega)
  all_goals try with_reducible assumption
  all_goals try (janus64_simp; done)
  all_goals try (janus64_simp; omega)

end PrintFn

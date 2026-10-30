import PrintProofs.Arm64.FnPrintlock

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-- The simp lemmas of the M's print count and `m.locks` arithmetic. -/
macro "prun" : tactic => `(tactic| janus_run [rotateRight_zero64, sext8_and255, ofNat_and255,
  setWidth32_ofNat, ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat])

/-- What `recordForPanic(b)` needs at its entry `s` (`X0, X1, X2 = b`): the stack, `g` and its M
with print count `1 ≤ c ≤ 125`, the globals, `b` readable, and the written ranges apart from
everything read. -/
def RfpPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s 104 32 ∧ GuardOK s 64 ∧
    (s.regs 28).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 48) 8 false = true ∧
    s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 true = true ∧
    1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ∧
    s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ≤ 125 ∧
    s.mem.accessible PK 4 false = true ∧ s.mem.accessible BI 8 true = true ∧
    s.mem.readLE BI 8 < 512 ∧ s.mem.accessible BL 512 true = true ∧
    (s.regs 0).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧ (s.regs 1).toNat ≤ (s.regs 2).toNat ∧
    (s.regs 2).toNat ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat false = true ∧
    -- the stack window, the M's fields, `b` and `g`'s fields apart from each other and the globals
    Sep (s.sp.toNat - 104) 136 [((s.regs 28).toNat + 16, 8), ((s.regs 28).toNat + 48, 8),
      (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), ((s.regs 0).toNat, (s.regs 1).toNat),
      (PK, 4), (BI, 8), (BL, 512)] ∧
    Sep (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 [((s.regs 28).toNat + 16, 8),
      ((s.regs 28).toNat + 48, 8), ((s.regs 0).toNat, (s.regs 1).toNat), (PK, 4), (BI, 8), (BL, 512)] ∧
    Sep (s.regs 0).toNat (s.regs 1).toNat [(BI, 8), (BL, 512)] ∧
    Sep ((s.regs 28).toNat + 16) 8 [(BI, 8), (BL, 512)] ∧
    Sep ((s.regs 28).toNat + 48) 8 [(BI, 8), (BL, 512)]

/-- What `recordForPanic` guarantees: the return, memory changed only in its stack window, the
M's `locks` and print count (restored), the backlog and its index (kept in range). -/
@[reducible] def RfpPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [] f v m ex ep ∧
    MemFrame s.mem m [(s.sp.toNat - 104, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32),
      (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 268),
      (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280),
      (BI, BI + 8), (BL, BL + 512)] ∧
    m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 =
      s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ∧
    m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 =
      s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 ∧
    m.readLE BI 8 < 512

set_option hygiene false in
/-- Close `RfpPost s s'` at the return (inside `recordForPanic`'s proof). -/
macro "rfp_post" : tactic => `(tactic| (
  unfold RfpPost
  simp only [hsp, hg, hx0, hx1, hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl, Nat.mod_eq_of_lt hgl,
    hmpE, h_bi, h_bl]
  refine ⟨_, _, _, _, _, _, by ret_state [hg, hg', h18, hsp, hsp', hdz, htp, hfc, hfs], by janus_frame, ?_, ?_, ?_⟩ <;>
    (janus_simp; first | janus_omega | (split <;> janus_omega) | skip)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem recordForPanic (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    Summary (P.link impl) (segAddr P "runtime.recordForPanic") RfpPre RfpPost := by
  -- PROOF recordForPanic
  intro s hpc hpre
  unfold RfpPre at hpre
  obtain ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hgm1, hgm2, hm1, hm2, hc1, hc2, hpk, hbi,
    hbi2, hbl, hpl, hlc, hcap, hbuf, ho1, ho2, ho3, ho4, ho5⟩ := hpre
  simp only [sep_cons, sep_nil, and_true] at ho1 ho2 ho3 ho4 ho5
  split_ands
  have hsp : s.sp = BitVec.ofNat 64 s.sp.toNat := by simp
  have hg : s.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat := by simp
  have hx0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have hx1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by simp
  have hx2 : s.regs 2 = BitVec.ofNat 64 (s.regs 2).toNat := by simp
  have hspl := s.sp.isLt
  have hgl := (s.regs 28).isLt
  have hx2l := (s.regs 2).isLt
  generalize s.sp.toNat = SP at *
  generalize (s.regs 28).toNat = G at *
  generalize (s.regs 0).toNat = ptr at *
  generalize (s.regs 1).toNat = len at *
  generalize (s.regs 2).toNat = cap at *
  generalize hmpE : s.mem.readLE (G + 48) 8 = MP at *
  janus_eval_nat h_pk : PK
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  simp only [h_pk, h_bi, h_bl] at *
  janus_eval_nat h_bi : BI
  janus_eval_nat h_bl : BL
  have hsepb : Apart ptr len BL 512 := by simp only [h_bl]; (first | with_reducible assumption | assumption)
  unfold Apart at hsepb
  have hlt : s.mem.readLE (MP + 279) 1 + 1 < 128 := by omega
  have loop : ∀ k (S : State) (i : Nat), len - i ≤ k → i ≤ len →
      S.pc = BitVec.ofNat 64 (segAddr P "runtime.recordForPanic" + 0xb4) →
      S.sp = BitVec.ofNat 64 SP - 64#64 → S.regs 28 = BitVec.ofNat 64 G → S.regs 18 = s.regs 18 →
      S.regs 0 = BitVec.ofNat 64 i → S.regs 3 = BitVec.ofNat 64 len →
      S.regs 4 = BitVec.ofNat 64 cap → S.regs 5 = BitVec.ofNat 64 ptr →
      MemFrame s.mem S.mem [(SP - 104, SP - 8), (SP + 8, SP + 32), (MP + 264, MP + 268),
        (MP + 279, MP + 280), (BI, BI + 8), (BL, BL + 512)] →
      S.mem.readLE (SP - 64) 8 = (s.regs 30).toNat → S.mem.readLE (SP - 72) 8 = (s.regs 29).toNat →
      S.mem.readLE (SP + 8) 8 = ptr → S.mem.readLE (SP + 16) 8 = len →
      S.mem.readLE (SP + 24) 8 = cap →
      S.mem.readLE (MP + 279) 1 = s.mem.readLE (MP + 279) 1 + 1 →
      S.mem.readLE (MP + 264) 4 = s.mem.readLE (MP + 264) 4 →
      S.mem.readLE BI 8 < 512 →
      S.dczid = s.dczid → S.tpidr = s.tpidr → S.fpcr = s.fpcr → S.fpsr = s.fpsr →
      ReachesRet (P.link impl) (s.regs regLR) S (RfpPost s) := by
    intro k
    induction k with
    | zero =>
      intro S i hk hi hpc' hsp' hg' h18 h0 h3 h4 h5 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 h_rd7 hidx hdz htp hfc hfs
      simp only [h_bi, h_bl] at *
      janus_eval_nat h_bi : BI
      janus_eval_nat h_bl : BL
      janus_run [hlt, hmpE, rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
        ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
      all_goals rfp_post
    | succ k ih =>
      intro S i hk hi hpc' hsp' hg' h18 h0 h3 h4 h5 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 h_rd7 hidx hdz htp hfc hfs
      simp only [h_bi, h_bl] at *
      janus_eval_nat h_bi : BI
      janus_eval_nat h_bl : BL
      by_cases hmin : len - i < 512 - S.mem.readLE BI 8 <;> rw [h_bi] at hmin
      · janus_run [hmin, sub_wrap, and_sshr_lt, sshr63_small, smod512, Int.ofNat_lt, hlt, hmpE,
          rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
          ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
          until [segAddr P "runtime.recordForPanic" + 0xb4] calls [hmm]
        all_goals first
          | refine ih _ len (by omega) (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          | rfp_post
        all_goals try (janus_simp; done)
        all_goals try janus_frame
        all_goals try (apply BitVec.eq_of_toNat_eq; simp [setReg]; omega)
        all_goals try (janus_simp; omega)
        all_goals try (first | with_reducible assumption | assumption)
      · janus_run [hmin, sub_wrap, and_sshr_lt, sshr63_small, smod512, Int.ofNat_lt, hlt, hmpE,
          rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
          ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
          until [segAddr P "runtime.recordForPanic" + 0xb4] calls [hmm]
        all_goals first
          | refine ih _ (i + (512 - S.mem.readLE BI 8)) (by simp only [h_bi]; omega) (by simp only [h_bi]; omega)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          | rfp_post
        all_goals try simp only [h_bi]
        all_goals try (janus_simp; done)
        all_goals try janus_frame
        all_goals try (apply BitVec.eq_of_toNat_eq; simp [setReg]; omega)
        all_goals try (janus_simp; omega)
        all_goals try (first | with_reducible assumption | assumption)
  janus_run [hmpE, rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero,
    sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat] until [segAddr P "runtime.recordForPanic" + 0x28]
    calls [printlock_held impl]
  name_reads
  janus_run [hlt, hmpE, rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero,
    sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat] until [segAddr P "runtime.recordForPanic" + 0xb4]
  all_goals first
    | refine loop _ _ 0 (Nat.le_refl _) (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | (have hg' := hg; have h18 : s.regs 18 = s.regs 18 := rfl; have hsp' := hsp
       have hdz : s.dczid = s.dczid := rfl; have htp : s.tpidr = s.tpidr := rfl
       have hfc : s.fpcr = s.fpcr := rfl; have hfs : s.fpsr = s.fpsr := rfl
       rfp_post)
  all_goals try simp only [h_bi]
  all_goals try (janus_simp; done)
  all_goals try janus_frame
  all_goals try (janus_simp; omega)
  all_goals try (first | with_reducible assumption | assumption)

end PrintFn

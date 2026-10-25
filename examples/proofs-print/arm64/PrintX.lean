import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace Proof

abbrev P := Extracted.program

/-! ## The runtime's print globals (`.noptrbss`/`.bss`), at the addresses the code computes -/

/-- `runtime.panicking` (`atomic.Uint32`): `ADRP`+`ADD` in `recordForPanic`. -/
def PK : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 40)
  (segWord P "runtime.recordForPanic" 10) (segWord P "runtime.recordForPanic" 11) 0
/-- `runtime.printBacklogIndex` (`int`): `ADRP`+`LDR` in `recordForPanic`. -/
def BI : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 140)
  (segWord P "runtime.recordForPanic" 35) (segWord P "runtime.recordForPanic" 36) 3
/-- `runtime.printBacklog` (`[512]byte`): `ADRP`+`ADD` in `recordForPanic`. -/
def BL : Nat := adrpLdTarget (segAddr P "runtime.recordForPanic" + 220)
  (segWord P "runtime.recordForPanic" 55) (segWord P "runtime.recordForPanic" 56) 0
/-- `runtime.debuglock` (`mutex`): `ADRP`+`ADD` in `printlock`. -/
def DL : Nat := adrpLdTarget (segAddr P "runtime.printlock" + 72)
  (segWord P "runtime.printlock" 18) (segWord P "runtime.printlock" 19) 0
/-- `runtime.overrideWrite` (`func`): `ADRP`+`LDR` in `write`. -/
def OW : Nat := adrpLdTarget (segAddr P "runtime.write" + 12)
  (segWord P "runtime.write" 3) (segWord P "runtime.write" 4) 3

example : PK = 0x18f564 ∧ BI = 0x18f688 ∧ BL = 0x190320 ∧ DL = 0x18f690 ∧ OW = 0x168c70 := by decide

/-- `runtime.printlock` with the M's print count already `c ≥ 1`: no `lock2`. -/
theorem printlock_held (impl : List Segment) :
    Summary (P.link impl) (segAddr P "runtime.printlock")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s 40 0 ∧ GuardOK s 0 ∧
        (s.regs 28).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 48) 8 false = true ∧
        s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 true = true ∧
        1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ≤ 126 ∧
        Sep (s.sp.toNat - 40) 32 [((s.regs 28).toNat + 16, 8), ((s.regs 28).toNat + 48, 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16)])
      (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
        s' = retState s junk [] f v m ∧
        MemFrame s.mem m [(s.sp.toNat - 40, s.sp.toNat - 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 268),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280)] ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 + 1 ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4) := by
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, ⟨hg1, hg2, hg3⟩, hgm1, hgm2, hm1, hm2, hc1, hc2, hout⟩
  simp only [sep_cons, sep_nil, and_true] at hout
  split_ands
  have hlt : s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 < 128 := by omega
  janus_run [rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', hlt]
  refine ⟨_, _, _, _, by ret_state, by janus_frame, ?_, ?_⟩
  all_goals (janus_simp; first | omega | (split <;> janus_arith))

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

/-- The ranges `recordForPanic` writes: its stack window, the M's `locks` and print count, the
backlog and its index. -/
def rfpW (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 104, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32),
    (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 268),
    (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280),
    (BI, BI + 8), (BL, BL + 512)]

def RfpPost (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
    s' = retState s junk [] f v m ∧ MemFrame s.mem m (rfpW s) ∧
    m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 =
      s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 ∧
    m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 =
      s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 ∧
    m.readLE BI 8 < 512

set_option hygiene false in
/-- Close `RfpPost s s'` at the return (inside `recordForPanic`'s proof). -/
macro "rfp_post" : tactic => `(tactic| (
  unfold RfpPost rfpW
  simp only [hsp, hg, hx0, hx1, hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspl, Nat.mod_eq_of_lt hgl,
    hmpE, h_bi, h_bl]
  refine ⟨_, _, _, _, by ret_state [hg, hg', h18, hsp, hsp'], by janus_frame, ?_, ?_, ?_⟩ <;>
    (janus_simp; first | janus_omega | (split <;> janus_omega) | skip)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem recordForPanic (impl : List Segment)
    (hmm : MemmoveContract (P.link impl) (P.contractAddr "runtime.memmove")) :
    Summary (P.link impl) (segAddr P "runtime.recordForPanic") RfpPre RfpPost := by
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
  have hlt : s.mem.readLE (MP + 279) 1 + 1 < 128 := by omega
  have loop : ∀ k (S : State) (i : Nat), len - i = k → i ≤ len →
      S.pc = BitVec.ofNat 64 (segAddr P "runtime.recordForPanic" + 0xb4) →
      S.sp = BitVec.ofNat 64 SP - 64#64 → S.regs 28 = BitVec.ofNat 64 G → S.regs 18 = s.regs 18 →
      S.regs 0 = BitVec.ofNat 64 i → S.regs 3 = BitVec.ofNat 64 len →
      S.regs 4 = BitVec.ofNat 64 cap → S.regs 5 = BitVec.ofNat 64 ptr →
      MemFrame s.mem S.mem [(SP - 104, SP - 8), (SP + 8, SP + 32), (MP + 264, MP + 268),
        (MP + 279, MP + 280), (1635976, 1635976 + 8), (1639200, 1639200 + 512)] →
      S.mem.readLE (SP - 64) 8 = (s.regs 30).toNat → S.mem.readLE (SP - 72) 8 = (s.regs 29).toNat →
      S.mem.readLE (SP + 8) 8 = ptr → S.mem.readLE (SP + 16) 8 = len →
      S.mem.readLE (SP + 24) 8 = cap →
      S.mem.readLE (MP + 279) 1 = s.mem.readLE (MP + 279) 1 + 1 →
      S.mem.readLE (MP + 264) 4 = s.mem.readLE (MP + 264) 4 →
      S.mem.readLE 1635976 8 < 512 →
      ReachesRet (P.link impl) (s.regs regLR) S (RfpPost s) := by
    intro k
    induction k with
    | zero =>
      intro S i hk hi hpc' hsp' hg' h18 h0 h3 h4 h5 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 h_rd7 hidx
      janus_run [hlt, hmpE, rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
        ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
      all_goals rfp_post
    | succ k ih =>
      intro S i hk hi hpc' hsp' hg' h18 h0 h3 h4 h5 hf h_rd1 h_rd2 h_rd3 h_rd4 h_rd5 h_rd6 h_rd7 hidx
      by_cases hmin : len - i < 512 - S.mem.readLE 1635976 8
      · janus_run [hmin, sub_wrap, and_sshr_lt, sshr63_small, smod512, Int.ofNat_lt, hlt, hmpE,
          rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
          ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
          until [segAddr P "runtime.recordForPanic" + 0xb4] calls [hmm]
        all_goals refine ih _ len ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | janus_frame | (janus_simp; done) | (janus_simp; janus_omega) | skip
        trace_state
        all_goals sorry
      · janus_run [hmin, sub_wrap, and_sshr_lt, sshr63_small, smod512, Int.ofNat_lt, hlt, hmpE,
          rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat,
          ofNat32_eq_zero, sext32_add_mod, sext8_add_mod, sext8_add_mod', ite_eq_nat]
          until [segAddr P "runtime.recordForPanic" + 0xb4] calls [hmm]
        all_goals sorry
  sorry

end Proof

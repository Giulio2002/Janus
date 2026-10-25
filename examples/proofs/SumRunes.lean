import Extracted

/-!
# `SumRunes(s string) uint64` sums the code points `for range s` yields (arm64)

**Guarantee.** For every string `s = (p, n)`, every `rt` and **every** implementation of
`runtime.decoderune` satisfying its contract (`RtContract … decoderuneSpec`,
`Janus/Contracts/String.lean`; met by the runtime's own code, `examples/proofs/Decoderune.lean`),
and every Go call state of `example.com/basic.SumRunes` with the stack guard 48 bytes below `SP`
(so neither SumRunes' nor `decoderune`'s stack check grows the stack), the stack window
`[SP-4144, SP+24)` writable and outside `rt`, the string readable, outside `rt` and the window,
and `g`'s guard word outside both: the call returns, obeys the ABI, and `X0` is
`sumRunes (bytes of s)`: the sum, modulo `2^64`, of the runes Go's `for range` produces, with
U+FFFD for every invalid UTF-8 sequence (`Janus/Spec/String.lean`, checked against the Go
runtime in `JanusTests/String.lean`).

**How.** `loop` is the invariant at the loop head (`cmp x1, x2`): `X3` plus the sum of the runes
from index `X2` on is the result, and memory differs from the prologue's only in `rt`,
`decoderune`'s window and the saved accumulator (`MemFrame`). One iteration either takes an
ASCII byte inline (`hasc`) or calls `decoderune` through its contract (`step_sum` with
`rangeStep`); the induction is on the bytes left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

abbrev head : Nat := Extracted.entry + 0x38

/-- The memory after the prologue's stores. -/
def M0 (s : State) (ret : Nat) (p n : BitVec 64) : Memory :=
  (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat + 16) 8 n.toNat).writeLE (s.sp.toNat + 8) 8 p.toNat

/-- What the loop may change besides `rt`: `decoderune`'s stack window and spill slots, and the
saved accumulator. -/
def R (s : State) : List (Nat × Nat) := [(s.sp.toNat - 4144, s.sp.toNat - 56), (s.sp.toNat - 40, s.sp.toNat - 8)]

/-- `SXTW` of a word whose low half is a non-negative `int32`. -/
theorem sxtw_small (x : BitVec 64) (h : x.toNat % 2 ^ 32 < 2 ^ 31) :
    ((if x.getLsbD 31 = true then 18446744073709551615#64 else 0#64) &&& 18446744069414584320#64 |||
      x.rotateRight 0 &&& 4294967295#64 &&& 4294967295#64) = BitVec.ofNat 64 (x.toNat % 2 ^ 32) := by
  have h31 : x.getLsbD 31 = false := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_false_iff_not]
    have : x.toNat / 2 ^ 31 % 2 = x.toNat % 2 ^ 32 / 2 ^ 31 := by omega
    omega
  rw [h31]
  apply BitVec.eq_of_toNat_eq
  simp only [Bool.false_eq_true, ite_false, BitVec.zero_and, BitVec.zero_or, BitVec.toNat_and,
    BitVec.toNat_ofNat]
  have hr : x.rotateRight 0 = x := by simp [BitVec.rotateRight, BitVec.rotateRightAux]
  have e : x.toNat &&& 4294967295 = x.toNat % 4294967296 := Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  rw [hr]
  simp only [show (4294967295 : Nat) % 2 ^ 64 = 4294967295 from rfl, e]
  have e2 : x.toNat % 4294967296 &&& 4294967295 = x.toNat % 4294967296 % 4294967296 :=
    Nat.and_two_pow_sub_one_eq_mod _ 32
  rw [e2]
  omega

theorem toInt_setWidth32_readLE1 (m : Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 1))).toInt = (m.readLE a 1 : Int) := by
  have hb := Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  rw [toInt32_of_lt _ (by simp; omega)]
  simp; omega

theorem toInt_127 : (127#32).toInt = 127 := by decide

theorem toNat_setWidth32_readLE1 (m : Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 1))).toNat = m.readLE a 1 := by
  have hb := Memory.readLE_lt m a 1
  simp only [Nat.pow_one] at hb
  simp; omega

/-- One iteration of the range loop: the rune it adds and the index it moves to. -/
theorem step_sum (bs : List Nat) (k a r k' : Nat) (hk : k < bs.length) (hs : rangeStep bs k = (r, k')) :
    ((a + r) % 2 ^ 64 + (runesFrom bs k').sum) % 2 ^ 64 = (a + (runesFrom bs k).sum) % 2 ^ 64 := by
  rw [runesFrom_of_lt bs k hk, hs]
  simp only [List.sum_cons]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem loop (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hdec : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.decoderune")
      rt 4096 H decoderuneSpec) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 48 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb : 4144 ≤ s.sp.toNat) (ha : s.sp.toNat + 24 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 4144) (4144 + 24) true = true)
    (hout : Outside (s.sp.toNat - 4144) 4168 rt) (hgr : Outside ((s.regs 28).toNat + 16) 8 rt)
    (hgs : (s.regs 28).toNat + 24 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16)
    (hp1 : p.toNat + n.toNat ≤ 2 ^ 48) (hp2 : 0 < n.toNat → s.mem.accessible p.toNat n.toNat false = true)
    (hpr : Outside p.toNat n.toNat rt)
    (hps : p.toNat + n.toNat ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ p.toNat)
    (hn : n.toNat < 2 ^ 63) (hra : ret % 4 = 0 ∧ ret < 2 ^ 48) :
    ∀ fuel (S : State) (T : Nat),
      ((S.regs 3).toNat + (runesFrom (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).sum) % 2 ^ 64 = T →
      n.toNat - (S.regs 2).toNat ≤ fuel → (S.regs 2).toNat ≤ n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = p → S.regs 1 = n →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 56#64 → S.regs 18 = s.regs 18 →
      MemFrame (M0 s ret p n) S.mem (rt ++ R s) →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = T) := by
  intro fuel
  induction fuel with
  | zero =>
    intro S T hT hf hk hpc h0 h1 hsp h28 h29 h18 hfr
    simp only [M0, R] at hfr
    janus_run
    rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
    simp [Nat.mod_eq_of_lt (S.regs 3).isLt]
  | succ fuel ih =>
    intro S T hT hf hk hpc h0 h1 hsp h28 h29 h18 hfr
    have hfr0 := hfr
    have hbs : strBytes S.mem p.toNat n.toNat = strBytes s.mem p.toNat n.toNat := by
      rw [strBytes_of_frame hfr (by
        simp only [R, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpr, by omega, by omega⟩)]
      simp only [M0]
      rw [strBytes_writeLE _ _ _ _ _ _ (by omega), strBytes_writeLE _ _ _ _ _ _ (by omega),
        strBytes_writeLE _ _ _ _ _ _ (by omega), strBytes_writeLE _ _ _ _ _ _ (by omega)]
    simp only [M0, R] at hfr
    by_cases hkn : (S.regs 2).toNat = n.toNat
    · janus_run
      rw [← hT, runesFrom_of_le _ _ (by simp; omega)]
      simp [Nat.mod_eq_of_lt (S.regs 3).isLt]
    · have hr := hp2 (by omega)
      by_cases hasc : s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 < 128
      · all_goals
          janus_run [false_implies, implies_true, List.not_mem_nil, forall_const, sub_flags_nv32,
            toInt_setWidth32_readLE1, toInt_127, toNat_setWidth32_readLE1] until [head] calls [hdec]
        all_goals
          apply ih
          all_goals (try (janus_simp; done))
          all_goals (try (janus_simp; omega))
        all_goals
          have hb := Memory.readLE_lt s.mem (p.toNat + (S.regs 2).toNat) 1
          simp only [Nat.pow_one] at hb
          try simp (disch := first | omega | decide |
              (simp (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
            only [sub_flags_nv32, toInt32_of_lt, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
              Nat.reduceMod] at hbr
          try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            beq_iff_eq, Bool.and_eq_false_iff, Bool.not_eq_false'] at hbr
        all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        all_goals (try simp only [callRegs_apply, Nat.reduceEqDiff, ↓reduceIte, getD_cons_zero,
          getD_cons_lit, Nat.reduceSub, Nat.reduceAdd, or_self, or_false, false_or])
        all_goals
          have hkl : (S.regs 2).toNat < (strBytes s.mem p.toNat n.toNat).length := by simp; omega
          have hd1 := decodeRune_snd (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hd2 := decodeRune_snd_le_length _ _ hkl
          simp only [strBytes_length] at hd2
          have hd3 := decodeRune_fst_le (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hby := byteAt_strBytes s.mem p.toNat n.toNat (S.regs 2).toNat (by simp at hkl; omega)
          simp only [maxRune] at hd3
          have hfw : MemFrame (M0 s ret p n) (S.mem.writeLE (s.sp.toNat - 16) 8 (S.regs 3).toNat) (rt ++ R s) :=
            hfr0.writeLE _ (r := (s.sp.toNat - 40, s.sp.toNat - 8)) (by simp [R]) (by omega) (by omega)
          try rw [hbs] at *
        all_goals first
          | (simpa [M0, R] using hfr0)
          | (refine MemFrame.trans hfw hfl ?_
             intro a k' h
             simp only [R, outside_append, outside_cons, outside_nil, and_true] at h ⊢
             obtain ⟨hrt, h2, h3⟩ := h
             exact ⟨⟨hrt, h2, h3⟩, by omega, by omega⟩)
          | (obtain ⟨-, hr1⟩ := hpost; omega)
          | (obtain ⟨hr0, hr1⟩ := hpost
             have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat := by
               unfold rangeStep; rw [if_neg (by omega)]
             rw [sxtw_small _ (by omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, hr1,
               Nat.mod_eq_of_lt (by omega : (BitVec.toNat _ % 2 ^ 32) < 2 ^ 64)]
             rw [show BitVec.toNat _ % 2 ^ 32 = (decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).1 from hr0]
             exact step_sum _ _ _ _ _ hkl (by rw [hrs]))
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1, (S.regs 2).toNat + 1) := by
               unfold rangeStep; rw [hby, if_pos (by omega)]
             rw [sxtw_small _ (by simp; omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
               BitVec.toNat_add]
             simp only [BitVec.toNat_ofNat]
             rw [Nat.mod_eq_of_lt (by omega : (S.regs 2).toNat + 1 % 2 ^ 64 < 2 ^ 64)]
             have := step_sum _ _ (S.regs 3).toNat _ _ hkl hrs
             rw [show (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 =
               s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 by omega]
             simpa using this)

      · all_goals
          janus_run [false_implies, implies_true, List.not_mem_nil, forall_const, sub_flags_nv32,
            toInt_setWidth32_readLE1, toInt_127, toNat_setWidth32_readLE1] until [head] calls [hdec]
        all_goals
          apply ih
          all_goals (try (janus_simp; done))
          all_goals (try (janus_simp; omega))
        all_goals
          rename_i hfl hpost
          have hb := Memory.readLE_lt s.mem (p.toNat + (S.regs 2).toNat) 1
          simp only [Nat.pow_one] at hb
          try simp (disch := first | omega | decide |
              (simp (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega))
            only [sub_flags_nv32, toInt32_of_lt, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
              Nat.reduceMod] at hbr
          try simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
            beq_iff_eq, Bool.and_eq_false_iff, Bool.not_eq_false'] at hbr
        all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
        all_goals (try simp only [callRegs_apply, Nat.reduceEqDiff, ↓reduceIte, getD_cons_zero,
          getD_cons_lit, Nat.reduceSub, Nat.reduceAdd, or_self, or_false, false_or])
        all_goals
          have hkl : (S.regs 2).toNat < (strBytes s.mem p.toNat n.toNat).length := by simp; omega
          have hd1 := decodeRune_snd (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hd2 := decodeRune_snd_le_length _ _ hkl
          simp only [strBytes_length] at hd2
          have hd3 := decodeRune_fst_le (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat
          have hby := byteAt_strBytes s.mem p.toNat n.toNat (S.regs 2).toNat (by simp at hkl; omega)
          simp only [maxRune] at hd3
          have hfw : MemFrame (M0 s ret p n) (S.mem.writeLE (s.sp.toNat - 16) 8 (S.regs 3).toNat) (rt ++ R s) :=
            hfr0.writeLE _ (r := (s.sp.toNat - 40, s.sp.toNat - 8)) (by simp [R]) (by omega) (by omega)
          try rw [hbs] at *
        all_goals first
          | (simpa [M0, R] using hfr0)
          | (refine MemFrame.trans hfw hfl ?_
             intro a k' h
             simp only [R, outside_append, outside_cons, outside_nil, and_true] at h ⊢
             obtain ⟨hrt, h2, h3⟩ := h
             exact ⟨⟨hrt, h2, h3⟩, by omega, by omega⟩)
          | (obtain ⟨-, hr1⟩ := hpost; omega)
          | (obtain ⟨hr0, hr1⟩ := hpost
             have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat := by
               unfold rangeStep; rw [if_neg (by omega)]
             rw [sxtw_small _ (by omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, hr1,
               Nat.mod_eq_of_lt (by omega : (BitVec.toNat _ % 2 ^ 32) < 2 ^ 64)]
             rw [show BitVec.toNat _ % 2 ^ 32 = (decodeRune (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat).1 from hr0]
             exact step_sum _ _ _ _ _ hkl (by rw [hrs]))
          | (have hrs : rangeStep (strBytes s.mem p.toNat n.toNat) (S.regs 2).toNat =
                 (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1, (S.regs 2).toNat + 1) := by
               unfold rangeStep; rw [hby, if_pos (by omega)]
             rw [sxtw_small _ (by simp; omega), ← hT, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
               BitVec.toNat_add]
             simp only [BitVec.toNat_ofNat]
             rw [Nat.mod_eq_of_lt (by omega : (S.regs 2).toNat + 1 % 2 ^ 64 < 2 ^ 64)]
             have := step_sum _ _ (S.regs 3).toNat _ _ hkl hrs
             rw [show (s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 =
               s.mem.readLE (p.toNat + (S.regs 2).toNat) 1 by omega]
             simpa using this)


/-- The precondition. -/
def Pre (rt : List (Nat × Nat)) (p n : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 4144 24 ∧ Outside (s.sp.toNat - 4144) 4168 rt ∧
    Outside ((s.regs 28).toNat + 16) 8 rt ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
    StrIn s.mem p.toNat n.toNat ∧ Outside p.toNat n.toNat rt ∧
    (p.toNat + n.toNat ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ p.toNat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64)
    (hdec : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.decoderune")
      rt 4096 H decoderuneSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, n] (Pre rt p n)
      (fun s s' => (s'.regs 0).toNat = sumRunes (strBytes s.mem p.toNat n.toNat)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, hgr, hgs, ⟨hp1, hp2⟩, hpr, hps⟩
  janus_intro hs
  have hra : ret % 4 = 0 ∧ ret < 2 ^ 48 := ⟨hret.aligned, by have := hret.user; omega⟩
  janus_run until [head]
  refine loop impl rt H p n hdec ret hret s hg1 hg2 (by omega) hal hb ha hw hout hgr hgs hp1 hp2 hpr hps
    (by omega) hra n.toNat _ _ (by simp [setReg, sumRunes, runes]) (by simp [setReg]) (by simp [setReg]) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) ?_
  simp only [M0, R]
  exact MemFrame.refl _ _

end Proof

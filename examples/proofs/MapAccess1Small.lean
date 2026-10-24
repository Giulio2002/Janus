import Extracted

/-!
# `runtime.mapaccess1_fast64` meets the `Access1` contract on small maps

**Guarantee.** For every type-descriptor address `t` and every heap range `heap`, the machine
code of Go 1.26's `runtime.mapaccess1_fast64(t, m, k)` (what `v := m[k]` calls for a
`map[uint64]V`) satisfies the map contract `Janus.Contracts.Map.Access1`, for the
representation `smallModel t zeroVal heap` (`Janus/Spec/SwissMap.lean`): nil maps, and
well-formed **small** Swiss maps (`SwissSmall`: no directory, at most 8 entries in one group of
control word + 8 key/value slots, all inside `heap`). That is: from every call state with the
contract's precondition (`RTPre`: stack, stack guard and return address; the slot size `16` at
`t + 88` and the zero value `runtime.zeroVal` readable; the stack window outside `heap`), the
function returns to `X30` without faulting, keeping `SP`, `X18`, `X28`, `X29`, changing memory
only in its own 16-byte frame record below `SP`, and returns in `X0` a pointer to 8 readable
bytes inside the map's memory that hold `m[k]`, or to `runtime.zeroVal` (which holds `0`) when
`k` is absent or `m` is nil. `zeroVal` is recomputed from the extracted `ADRP`+`ADD` words.

**What stays trusted.** This is the only runtime map function verified from its code, and only
on small maps: the `dirLen ≠ 0` path (hashing through the type's hasher by an indirect `BLR`,
directory and table probing) and the `writing ≠ 0` path (`fatal("concurrent map read and map
write")`) are excluded by `SwissSmall`. Every other map contract (`Access2`, `Assign`, `Delete`,
`Clear`, `MakeSmall`, `IterStart`, `IterNext`, `Access2Ptr`) remains an assumption of the
theorems that use it, and `SwissSmall` is our reading of Go 1.26's layout, not a proved property
of maps the runtime builds.

**How.** The prologue and the header checks run straight-line; the slot scan is the loop at
`+0x1dc`, proved by induction over the slots left (`loop`): after `i` slots, `X1` points at
slot `i`'s key and `X3` holds the full-slot mask shifted by `8i` (`maskFrom`, whose bit 7 says
whether slot `i` is full, `maskFrom_bit7`). `mask_toNat` shows the `MVN`/`AND` on the control
word computes that mask.
-/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Swiss
  Janus.Contracts Janus.Contracts.Map

namespace Proof

theorem sw32_ofNat_eq_zero (n : Nat) : (BitVec.setWidth 32 (BitVec.ofNat 64 n) = 0#32) = (n % 2^32 = 0) := by
  apply propext
  rw [← BitVec.toNat_inj]
  simp

/-- The final state: result pointer `p` in `X0`, and the ABI frame. -/
def Res (s s' : State) (p : Nat) : Prop :=
  s'.regs 0 = BitVec.ofNat 64 p ∧ s'.sp = s.sp ∧ s'.pc = s.regs 30 ∧
    s'.mem = (s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat ∧
    s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
    s'.vregs = s.vregs ∧ s'.dczid = s.dczid ∧ s'.tpidr = s.tpidr ∧ s'.fpcr = s.fpcr ∧
    s'.fpsr = s.fpsr

theorem rr_mono {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

theorem ofNat_add8 (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Address of `runtime.zeroVal`, the zero value an access returns for an absent key: the
`ADRP`+`ADD` pair at `+0xe8`, recomputed from the extracted words. -/
def zeroVal : Nat :=
  adrpLdTarget (Extracted.entry + 0xe8) (segWord Extracted.program "runtime.mapaccess1_fast64" 58)
    (segWord Extracted.program "runtime.mapaccess1_fast64" 59) 0

set_option maxHeartbeats 0 in
theorem loop (s : State) (g k zv : Nat) (hsp1 : 64 ≤ s.sp.toNat) (hsp2 : s.sp.toNat ≤ 2^48)
    (hal : s.sp.toNat % 16 = 0)
    (hst : s.mem.accessible (s.sp.toNat - 64) 64 true = true)
    (hga : s.mem.accessible g 136 false = true) (hgb : g + 136 ≤ 2^48)
    (hd2 : g + 136 ≤ s.sp.toNat - 64 ∨ s.sp.toNat ≤ g)
    (hlr : BitVec.toNat (s.regs 30) % 4 = 0) (hlr2 : BitVec.toNat (s.regs 30) < 2 ^ 48)
    (hk : (s.regs 2).toNat = k) (hzv : zv = (janus_eval% zeroVal)) :
    ∀ n i (S : State), i + n = 8 →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1dc) →
      S.regs 1 = BitVec.ofNat 64 (g + 8 + 16 * i) →
      S.regs 2 = s.regs 2 →
      S.regs 3 = BitVec.ofNat 64 (maskFrom s.mem g i) →
      S.regs 4 = BitVec.ofNat 64 16 →
      S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 30 = s.regs 30 → S.sp = s.sp - BitVec.ofNat 64 48 →
      S.mem = (s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat →
      S.vregs = s.vregs → S.dczid = s.dczid → S.tpidr = s.tpidr →
      S.fpcr = s.fpcr → S.fpsr = s.fpsr →
      ReachesRet Extracted.program (s.regs 30) S (fun s' => ∃ p, Res s s' p ∧
        (lookupFrom s.mem g k i = none ∧ p = zv ∨ ∃ j, lookupFrom s.mem g k i = some j ∧ p = slotVal g j)) := by
  subst hzv hk
  intro n
  induction n with
  | zero =>
    intro i S hn hpc h1 h2 h3 h4 h18 h28 h30 hsp hmem hv hdz htp hfc hfs
    rw [maskFrom_ge _ _ _ (by omega)] at h3
    janus_run
    exact ⟨(janus_eval% zeroVal), ⟨by simp [setReg], rfl, rfl, rfl, by simp [setReg, h18], by simp [setReg, h28], by simp [setReg], hv, hdz, htp, by simp [hfc], by simp [hfs]⟩,
      .inl ⟨lookupFrom_ge _ _ _ _ (by omega), rfl⟩⟩
  | succ n ih =>
    intro i S hn hpc h1 h2 h3 h4 h18 h28 h30 hsp hmem hv hdz htp hfc hfs
    have hml : maskFrom s.mem g i < 2 ^ 64 := by
      have := maskFrom_lt s.mem g (n+1) i hn
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
    janus_run [sw32_ofNat_eq_zero, maskFrom_bit7 _ _ _ (show i < 8 by omega), lsr8_ofNat _ hml] until [Extracted.entry + 0x1dc]
    · exact ⟨(janus_eval% zeroVal), ⟨by simp [setReg], rfl, rfl, rfl, by simp [setReg, h18], by simp [setReg, h28], by simp [setReg], hv, hdz, htp, by simp [hfc], by simp [hfs]⟩,
        .inl ⟨lookupFrom_of_mask_zero _ _ _ (n + 1) i hn ‹_›, rfl⟩⟩
    · rename_i _ _ hc _
      refine ⟨g + 16 + 16 * i, ⟨by simp [setReg, ofNat_add8]; exact congrArg _ (by omega), rfl, rfl, rfl, by simp [setReg, h18], by simp [setReg, h28], by simp [setReg], hv, hdz, htp, by simp [hfc], by simp [hfs]⟩,
        .inr ⟨i, ?_, rfl⟩⟩
      rw [lookupFrom_eq _ _ _ _ (by omega)]
      simp [hc, slotKey]
    all_goals
      refine rr_mono (ih (i + 1) _ (by omega) rfl (by simp [setReg, ofNat_add8]; exact congrArg _ (by omega)) (by simp [setReg, h2]) ?_ (by simp [setReg, h4])
        (by simp [setReg, h18]) (by simp [setReg, h28]) (by simp [setReg, h30]) rfl rfl hv hdz htp (by simp [hfc]) (by simp [hfs])) ?_
      · simp [setReg]
        exact congrArg _ (by rw [maskFrom_eq _ _ _ (by omega)]; have := fullBit_le (ctrl s.mem g i); omega)
      · rintro s' ⟨p, hr, hl⟩
        refine ⟨p, hr, ?_⟩
        rw [lookupFrom_eq _ _ _ _ (by omega)]
        split
        · exfalso; unfold slotKey at *; omega
        · exact hl

set_option maxHeartbeats 0 in
theorem run (t : Nat) (heap : Nat × Nat) (f : AMap (BitVec 64) (BitVec 64)) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : RTPre (smallModel t zeroVal heap) 3 s ∧ (smallModel t zeroVal heap).Typ (s.regs 0).toNat ∧
      IsMap (smallModel t zeroVal heap) s.mem (s.regs 1).toNat f) :
    ReachesRet Extracted.program (s.regs 30) s (fun s' => ∃ p, Res s s' p ∧
      ((f (s.regs 2) = none ∧ p = zeroVal) ∨
        ∃ j, j < 8 ∧ p = slotVal (group s.mem (s.regs 1).toNat) j ∧
          f (s.regs 2) = some (BitVec.ofNat 64 (s.mem.readLE p 8)))) := by
  obtain ⟨lo, hi⟩ := heap
  obtain ⟨⟨henv, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hty, hmap⟩ := hpre
  janus_eval_nat hzv : zeroVal
  unfold smallModel at henv hty hmap hout hg3 hd1 hd2 hst
  simp only [SmallEnv, regG, stackguard0Offset, stackguard0] at henv hty hout hg1 hg2 hg3 hd1 hd2 hst
  rw [hzv] at henv hout ⊢
  simp only [outside_cons, outside_nil, and_true] at hout
  obtain ⟨ht1, ht2, ht3, hz1, hz2, hz3⟩ := henv
  subst hty
  by_cases h0 : (s.regs 1).toNat = 0
  · simp only [IsMap, h0, ite_true] at hmap
    subst hmap
    janus_run
    exact ⟨(janus_eval% zeroVal), ⟨by simp [setReg], rfl, rfl, rfl, by simp [setReg], by simp [setReg],
      by simp [setReg], rfl, rfl, rfl, rfl, rfl⟩, .inl ⟨rfl, rfl⟩⟩
  · simp only [IsMap, h0, ite_false] at hmap
    obtain ⟨-, hh1, ⟨hh2, hh3⟩, hdl, hwr, hgr, ⟨hgi1, hgi2⟩, hhb, hcont, hused⟩ := hmap
    simp only [group] at hgr hgi1 hgi2 hcont ⊢
    generalize hgdef : s.mem.readLE ((s.regs 1).toNat + 16) 8 = g at hgr hgi1 hgi2 hcont ⊢
    have hgdef' := hgdef
    janus_run [sw32_ofNat_eq_zero] until [Extracted.entry + 0x1dc]
    · -- `used = 0`: the map is empty
      rename_i hu
      obtain ⟨ks, hks, hlen⟩ := hused
      have hks0 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hks0
      have hnone : f (s.regs 2) = none := by
        cases hf : f (s.regs 2) with
        | none => rfl
        | some v => exact absurd ((hks.2 (s.regs 2)).2 (by simp [hf])) (by simp)
      exact ⟨(janus_eval% zeroVal), ⟨by simp [setReg], rfl, rfl, rfl, by simp [setReg], by simp [setReg],
        by simp [setReg], rfl, rfl, rfl, rfl, rfl⟩, .inl ⟨hnone, rfl⟩⟩
    · have hmk : (~~~BitVec.ofNat 64 (s.mem.readLE g 8) &&& 9259542123273814144#64) =
          BitVec.ofNat 64 (maskFrom s.mem g 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [mask_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (maskFrom_lt64 _ _ _ (by decide))]
      rw [hgdef] at *
      refine rr_mono (loop s g (s.regs 2).toNat (janus_eval% zeroVal) hd1 (by omega) hal
        (Memory.accessible_mono _ hst (by omega) (by omega)) hgr (by omega) (by omega) hl1 hl2 rfl rfl
        8 0 _ rfl rfl (by simp [setReg, ofNat_add8]) (by simp [setReg]) (by simp [setReg, hmk])
        (by simp [setReg, ht3]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl rfl rfl rfl rfl)
        ?_
      rintro s' ⟨p, hr, hl⟩
      refine ⟨p, hr, ?_⟩
      rcases hl with ⟨hl, rfl⟩ | ⟨j, hl, rfl⟩
      · exact .inl ⟨by rw [hcont, hl]; rfl, rfl⟩
      · exact .inr ⟨j, lookupFrom_lt _ _ _ 8 0 rfl j hl, rfl, by rw [hcont, hl]; rfl⟩

/-- **`runtime.mapaccess1_fast64` meets its contract on small maps.** -/
theorem correctness (t : Nat) (heap : Nat × Nat) :
    Access1 Extracted.program Extracted.entry (smallModel t zeroVal heap) := by
  intro f s hpc hpre
  have hrun := run t heap f s hpc hpre
  obtain ⟨⟨henv, -, ⟨-, -, -, hd1, -, -, hst⟩, hout⟩, -, hmap⟩ := hpre
  refine rr_mono hrun ?_
  rintro s' ⟨p, ⟨h0, hsp, hpc', hmem, h18, h28, h29, hv, hdz, htp, hfc, hfs⟩, hslot⟩
  have hl := smallModel_laws t zeroVal heap
  obtain ⟨lo, hi⟩ := heap
  have hout' := hout
  simp only [smallModel_priv, smallModel_depth, outside_cons, outside_nil, and_true] at hout' hd1
  have hag : Agrees s.mem s'.mem (smallModel t zeroVal (lo, hi)).priv := by
    rw [hmem]
    simp only [smallModel_depth] at hout
    exact (agrees_writeLE _ _ (Outside.of_sub hout (by omega) (by omega))).writeLE _
      (Outside.of_sub hout (by omega) (by omega))
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
    simp only at hsp hpc' hdz htp hfc hfs h18 h28 h29 ⊢
    subst hsp hpc' hdz htp hfc hfs
    congr
    funext i
    simp only [keepABI]
    split
    · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
    · rfl
  · rw [hmem]
    simp only [rtWrites, calleeStack, smallModel, List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · exact hl.env_frame _ _ _ henv hag
  · intro mp' f' _ h; exact hl.rep_frame _ _ _ _ h hag
  · exact IsMap.frame hl hmap hag
  · rw [h0, BitVec.toNat_ofNat]
    obtain ⟨-, -, -, hz1, hz2, hz3⟩ := (henv : SmallEnv s.mem t zeroVal)
    rcases hslot with ⟨hn, rfl⟩ | ⟨j, hj, rfl, hf⟩
    · rw [Nat.mod_eq_of_lt (by omega), hn]
      refine ⟨by rw [hag.accessible]; exact hz1, (show InRanges zeroVal 8 (smallModel t zeroVal (lo, hi)).priv from
        ⟨(zeroVal, zeroVal + 8), by simp only [smallModel_priv, List.mem_cons, true_or, or_true], Nat.le_refl zeroVal, Nat.le_refl (zeroVal + 8)⟩), ?_⟩
      rw [hag.readLE (show InRanges zeroVal 8 (smallModel t zeroVal (lo, hi)).priv from
        ⟨(zeroVal, zeroVal + 8), by simp only [smallModel_priv, List.mem_cons, true_or, or_true], Nat.le_refl zeroVal, Nat.le_refl (zeroVal + 8)⟩), hz3]; rfl
    · have h0' : (s.regs 1).toNat ≠ 0 := by
        intro h; simp only [IsMap, h, ite_true] at hmap; rw [hmap] at hf; cases hf
      simp only [IsMap, h0', ite_false, smallModel_rep] at hmap
      have hgr := hmap.grp
      have hgi := hmap.grpIn
      have hhb := hmap.heapBound
      have hin : InRanges (slotVal (group s.mem (s.regs 1).toNat) j) 8 (smallModel t zeroVal (lo, hi)).priv :=
        ⟨(lo, hi), by simp only [smallModel_priv, List.mem_cons, true_or], by unfold slotVal; omega, by unfold slotVal; omega⟩
      rw [Nat.mod_eq_of_lt (by unfold slotVal; omega), hf]
      refine ⟨?_, hin, ?_⟩
      · rw [hag.accessible]
        exact Memory.accessible_mono _ hgr (by unfold slotVal; omega) (by unfold slotVal; omega)
      · rw [hag.readLE hin]
        simp only [Option.getD_some, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (Memory.readLE_lt _ _ 8)).symm

end Proof

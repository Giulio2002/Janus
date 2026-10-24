import Janus
import Extracted

/-!
# `runtime.mapaccess1_fast64` (amd64) meets the `Access1` contract on small maps

**Guarantee.** For every type-descriptor address `t` and heap range `heap`, the amd64 machine
code of Go 1.26's `runtime.mapaccess1_fast64(t, m, k)` satisfies
`Janus.Contracts.MapAmd64.Access1` for the representation `smallModel t zeroVal heap`
(`Janus/Spec/SwissMap.lean`: nil maps and well-formed small Swiss maps, `SwissSmall`): from every
call state with the contract's precondition it returns to `[RSP]` without faulting, with `RSP + 8`,
`RBP`, `R14` and `X15` preserved, memory changed only in its saved-`RBP` slot, and `RAX` pointing
to 8 readable bytes in the map's memory holding `m[k]`, or to `runtime.zeroVal` (zero) when `k`
is absent or `m` is nil. `zeroVal` is recomputed from the extracted RIP-relative `LEA`.

**What stays trusted.** As for arm64 (`examples/proofs/MapAccess1Small.lean`): the large-map path
(indirect call of the type's hasher, directory and table probing) and the concurrent-write
`fatal` path are excluded by `SwissSmall`; every other map contract remains an assumption.

**How.** The lookup builds a one-bit-per-slot mask with `MOVQ`/`PMOVMSKB`/`NOT`/`MOVZX`
(`msb_fullMask`: bit `i` set iff slot `i` is full, `fullMask`), then scans with `SHR`/`BT`; the
scan is the loop at `+0x1ad`, proved by induction over the slots left (`loop`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Swiss
  Janus.Contracts.MapAmd64

namespace Proof

theorem rr_mono {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', h1, h2, h3⟩ := h; exact ⟨k, s', h1, h2, hQ _ h3⟩

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `SHR r, 1` on a value below `2^64`. -/
theorem shr1_ofNat (m : Nat) (hm : m < 2 ^ 64) : BitVec.ofNat 64 m >>> 1 = BitVec.ofNat 64 (m / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- `BT EBX, 0` on the shifted mask: whether slot `i` is full. -/
theorem fullMask_bit0 (mem : Memory) (g i : Nat) (hi : i < 8) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (fullMask mem g i))).getLsbD 0 = decide (ctrl mem g i < 128) := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, fullMask_eq _ _ _ hi, Nat.testBit_eq_decide_div_mod_eq]
  have := fullBit_le (ctrl mem g i)
  unfold fullBit at *
  split <;> simp_all <;> omega

theorem msbBytes_cons (k b y : Nat) (hb : b < 256) :
    msbBytes (k + 1) (b + 256 * y) = b / 128 + 2 * msbBytes k y := by
  simp only [msbBytes]
  rw [show (b + 256 * y) % 256 = b by omega, show (b + 256 * y) / 256 = y by omega]

theorem msbBytes_zero_arg : ∀ k, msbBytes k 0 = 0
  | 0 => rfl
  | k + 1 => by simp only [msbBytes]; rw [msbBytes_zero_arg k]

theorem fullBit_eq (b : Nat) (hb : b < 256) : fullBit b = 1 - b / 128 := by
  unfold fullBit; split <;> omega

theorem msb_fullMask (mem : Janus.Arm64.Memory) (g : Nat) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64
      (~~~BitVec.setWidth 32 (BitVec.ofNat 64 (msbBytes 16 (mem.readLE g 8))))))) =
      BitVec.ofNat 64 (fullMask mem g 0) := by
  have hb : ∀ i, (mem.bytes (g + i)).toNat < 256 := fun i => (mem.bytes (g + i)).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [Nat.add_zero] at h0
  have hmsb : msbBytes 16 (mem.readLE g 8) =
      (mem.bytes g).toNat / 128 + 2 * ((mem.bytes (g + 1)).toNat / 128 + 2 * ((mem.bytes (g + 2)).toNat / 128 +
      2 * ((mem.bytes (g + 3)).toNat / 128 + 2 * ((mem.bytes (g + 4)).toNat / 128 + 2 * ((mem.bytes (g + 5)).toNat / 128 +
      2 * ((mem.bytes (g + 6)).toNat / 128 + 2 * ((mem.bytes (g + 7)).toNat / 128))))))) := by
    simp only [Janus.Arm64.Memory.readLE, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
    rw [msbBytes_cons _ _ _ h0, msbBytes_cons _ _ _ h1, msbBytes_cons _ _ _ h2, msbBytes_cons _ _ _ h3,
      msbBytes_cons _ _ _ h4, msbBytes_cons _ _ _ h5, msbBytes_cons _ _ _ h6,
      show (mem.bytes (g + 7)).toNat = (mem.bytes (g + 7)).toNat + 256 * 0 by omega,
      msbBytes_cons _ _ _ (by omega), msbBytes_zero_arg]
    omega
  have hfm : fullMask mem g 0 =
      fullBit (mem.bytes g).toNat + 2 * (fullBit (mem.bytes (g + 1)).toNat + 2 * (fullBit (mem.bytes (g + 2)).toNat +
      2 * (fullBit (mem.bytes (g + 3)).toNat + 2 * (fullBit (mem.bytes (g + 4)).toNat + 2 * (fullBit (mem.bytes (g + 5)).toNat +
      2 * (fullBit (mem.bytes (g + 6)).toNat + 2 * fullBit (mem.bytes (g + 7)).toNat)))))) := by
    simp only [fullMask_eq mem g _ (by decide : (0:Nat) < 8), fullMask_eq mem g _ (by decide : (1:Nat) < 8),
      fullMask_eq mem g _ (by decide : (2:Nat) < 8), fullMask_eq mem g _ (by decide : (3:Nat) < 8),
      fullMask_eq mem g _ (by decide : (4:Nat) < 8), fullMask_eq mem g _ (by decide : (5:Nat) < 8),
      fullMask_eq mem g _ (by decide : (6:Nat) < 8), fullMask_eq mem g _ (by decide : (7:Nat) < 8),
      fullMask_ge mem g 8 (by decide), ctrl, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_not, BitVec.toNat_ofNat, hmsb, hfm]
  rw [fullBit_eq _ h0, fullBit_eq _ h1, fullBit_eq _ h2, fullBit_eq _ h3, fullBit_eq _ h4, fullBit_eq _ h5,
    fullBit_eq _ h6, fullBit_eq _ h7]
  omega

/-- The final state: result pointer `p` in `RAX`, and the ABI frame. -/
def Res (s s' : State) (p : Nat) : Prop :=
  s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.rip = retAddrOf s ∧
    s'.mem = s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat ∧
    s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
    s'.fsBase = s.fsBase ∧ s'.df = s.df

/-- Address of `runtime.zeroVal`: the RIP-relative `LEA` at `+0xed`. -/
def zeroVal : Nat := ripTarget Extracted.program (Extracted.entry + 0xed)

set_option maxHeartbeats 0 in
theorem loop (s : State) (g k zv : Nat) (hsp1 : 32 ≤ (s.regs 4).toNat) (hsp2 : (s.regs 4).toNat + 8 ≤ 2^48)
    (hst : s.mem.accessible ((s.regs 4).toNat - 32) 40 true = true)
    (hga : s.mem.accessible g 136 false = true) (hgb : g + 136 ≤ 2^48)
    (hd2 : g + 136 ≤ (s.regs 4).toNat - 32 ∨ (s.regs 4).toNat + 8 ≤ g)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hk : (s.regs 1).toNat = k) (hzv : zv = 5763968) :
    ∀ n i (S : State), i + n = 8 →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x1ad) →
      S.regs 2 = BitVec.ofNat 64 (g + 8 + 16 * i) →
      S.regs 1 = s.regs 1 →
      S.regs 3 = BitVec.ofNat 64 (fullMask s.mem g i) →
      S.regs 6 = BitVec.ofNat 64 16 →
      S.regs 4 = s.regs 4 - BitVec.ofNat 64 32 → S.regs 5 = s.regs 4 - BitVec.ofNat 64 8 →
      S.regs 14 = s.regs 14 →
      S.mem = s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat →
      S.xmm 15 = s.xmm 15 → S.fsBase = s.fsBase → S.df = s.df →
      ReachesRet Extracted.program (retAddrOf s) S (fun s' => ∃ p, Res s s' p ∧
        (lookupFrom s.mem g k i = none ∧ p = zv ∨ ∃ j, lookupFrom s.mem g k i = some j ∧ p = slotVal g j)) := by
  subst hzv hk
  have hsp32 : (s.regs 4 - BitVec.ofNat 64 32).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  intro n
  induction n with
  | zero =>
    intro i S hn hpc h2 h1 h3 h6 h4 h5 h14 hmem hx hfs hdf
    rw [fullMask_ge _ _ _ (by omega)] at h3
    janus64_run
    exact ⟨5763968, ⟨by simp [setRegF], by simp [setRegF], rfl, rfl, by simp [setRegF],
      by simp [setRegF, h14], hx, hfs, rfl⟩, .inl ⟨lookupFrom_ge _ _ _ _ (by omega), rfl⟩⟩
  | succ n ih =>
    intro i S hn hpc h2 h1 h3 h6 h4 h5 h14 hmem hx hfs hdf
    have hml := fullMask_lt64 s.mem g i (by omega)
    janus64_run [fullMask_bit0 _ _ _ (show i < 8 by omega), shr1_ofNat _ hml] until [Extracted.entry + 0x1ad]
    · exact ⟨5763968, ⟨by simp [setRegF], by simp [setRegF], rfl, rfl, by simp [setRegF],
        by simp [setRegF, h14], hx, hfs, rfl⟩,
        .inl ⟨lookupFrom_of_fullMask_zero _ _ _ (n + 1) i hn ‹_›, rfl⟩⟩
    · rename_i hmask hkey
      refine ⟨g + 16 + 16 * i, ⟨by simp [setRegF, ofNat_add]; exact congrArg _ (by omega),
        by simp [setRegF], rfl, rfl, by simp [setRegF], by simp [setRegF, h14], hx, hfs, rfl⟩,
        .inr ⟨i, ?_, rfl⟩⟩
      rw [lookupFrom_eq _ _ _ _ (by omega)]
      have := Arm64.Memory.readLE_lt s.mem (g + 8 + 16 * i) 8
      exact if_pos ⟨hkey, by unfold slotKey; omega⟩
    all_goals
      refine rr_mono (ih (i + 1) _ (by omega) rfl (by simp [setRegF, ofNat_add]; exact congrArg _ (by omega))
        (by simp [setRegF, h1]) ?_ (by simp [setRegF, h6]) (by simp [setRegF, h4]) (by simp [setRegF, h5])
        (by simp [setRegF, h14]) rfl hx hfs rfl) ?_
      · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
        exact congrArg _ (by rw [fullMask_eq _ _ _ (by omega)]; have := fullBit_le (ctrl s.mem g i); omega)
      · rintro s' ⟨p, hr, hl⟩
        refine ⟨p, hr, ?_⟩
        rw [lookupFrom_eq _ _ _ _ (by omega)]
        split
        · exfalso; unfold slotKey at *; omega
        · exact hl

set_option maxHeartbeats 0 in
theorem run (t : Nat) (heap : Nat × Nat) (f : AMap (BitVec 64) (BitVec 64)) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 Extracted.entry)
    (hpre : RTPre (smallModel t zeroVal heap) 3 s ∧ (smallModel t zeroVal heap).Typ (s.regs 0).toNat ∧
      IsMap (smallModel t zeroVal heap) s.mem (s.regs 3).toNat f) :
    ReachesRet Extracted.program (retAddrOf s) s (fun s' => ∃ p, Res s s' p ∧
      ((f (s.regs 1) = none ∧ p = zeroVal) ∨
        ∃ j, j < 8 ∧ p = slotVal (group s.mem (s.regs 3).toNat) j ∧
          f (s.regs 1) = some (BitVec.ofNat 64 (s.mem.readLE p 8)))) := by
  obtain ⟨lo, hi⟩ := heap
  obtain ⟨⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd1, hb, hst, hx, hdf, hra, hout⟩, hty, hmap⟩ := hpre
  janus_eval_nat hzv : zeroVal
  simp only [smallModel_env, smallModel_typ, smallModel_depth, smallModel_priv, SmallEnv, regG, regSP,
    stackguard0Offset, stackguard0] at henv hty hout hg1 hg2 hg3 hd1 hst
  rw [hzv] at henv hout ⊢
  simp only [outside_cons, outside_nil, and_true] at hout
  obtain ⟨ht1, ht2, ht3, hz1, hz2, hz3⟩ := henv
  subst hty
  have hsp32 : (s.regs 4 - BitVec.ofNat 64 32).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hty' : (s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).readLE ((s.regs 0).toNat + 88) 8 = 16 := by
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact ht3
  by_cases h0 : (s.regs 3).toNat = 0
  · simp only [IsMap, h0, ite_true] at hmap
    subst hmap
    janus64_run
    exact ⟨5763968, ⟨by simp [setRegF], by simp [setRegF], rfl, rfl, by simp [setRegF], by simp [setRegF],
      rfl, rfl, hdf.symm⟩, .inl ⟨rfl, rfl⟩⟩
  · simp only [IsMap, h0, ite_false, smallModel_rep] at hmap
    obtain ⟨-, hh1, ⟨hh2, hh3⟩, hdl, hwr, hgr, ⟨hgi1, hgi2⟩, hhb, hcont, hused⟩ := hmap
    simp only [group] at hgr hgi1 hgi2 hcont ⊢
    generalize hgdef : s.mem.readLE ((s.regs 3).toNat + 16) 8 = g at hgr hgi1 hgi2 hcont ⊢
    janus64_run until [Extracted.entry + 0x1ad]
    · rename_i hu
      obtain ⟨ks, hks, hlen⟩ := hused
      have hks0 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hks0
      have hnone : f (s.regs 1) = none := by
        cases hf : f (s.regs 1) with
        | none => rfl
        | some v => exact absurd ((hks.2 (s.regs 1)).2 (by simp [hf])) (by simp)
      exact ⟨5763968, ⟨by simp [setRegF], by simp [setRegF], rfl, rfl, by simp [setRegF], by simp [setRegF],
        rfl, rfl, hdf.symm⟩, .inl ⟨hnone, rfl⟩⟩
    · refine rr_mono (loop s g (s.regs 1).toNat 5763968 (by omega) (by omega)
        (Arm64.Memory.accessible_mono _ hst (by omega) (by omega)) hgr (by omega) (by omega) hra rfl rfl
        8 0 _ rfl rfl (by simp [setRegF, ofNat_add]) (by simp [setRegF]) (by simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]; exact msb_fullMask s.mem g)
        (by simp [setRegF, hty']) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simp [setXmmF]) rfl hdf.symm) ?_
      rintro s' ⟨p, hr, hl⟩
      refine ⟨p, hr, ?_⟩
      rcases hl with ⟨hl, rfl⟩ | ⟨j, hl, rfl⟩
      · exact .inl ⟨by rw [hcont, hl]; rfl, rfl⟩
      · exact .inr ⟨j, lookupFrom_lt _ _ _ 8 0 rfl j hl, rfl, by rw [hcont, hl]; rfl⟩

/-- **`runtime.mapaccess1_fast64` (amd64) meets its contract on small maps.** -/
theorem correctness (t : Nat) (heap : Nat × Nat) :
    Access1 Extracted.program Extracted.entry (smallModel t zeroVal heap) := by
  intro f s hpc hpre
  have hrun := run t heap f s hpc hpre
  obtain ⟨⟨henv, -, -, hd1, -, hst, -, -, -, hout⟩, -, hmap⟩ := hpre
  refine rr_mono hrun ?_
  rintro s' ⟨p, ⟨h0, hsp, hpc', hmem, h5, h14, hx, hfs, hdf⟩, hslot⟩
  have hl := smallModel_laws t zeroVal heap
  obtain ⟨lo, hi⟩ := heap
  simp only [smallModel_depth] at hd1 hout
  have hag : Agrees s.mem s'.mem (smallModel t zeroVal (lo, hi)).priv := by
    rw [hmem]
    exact agrees_writeLE _ _ (Outside.of_sub hout (by omega) (by omega))
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, rip, fl, xm, mem, yh, fs, df⟩ := s'
    simp only at hsp hpc' hfs hdf h5 h14 hx ⊢
    subst hpc' hfs hdf
    congr
    · funext i
      simp only [keepABI]
      split
      · rename_i hi; subst hi; exact hsp
      · split
        · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
        · rfl
    · funext i
      simp only [keepX15]
      split
      · rename_i hi; subst hi; exact hx
      · rfl
  · rw [hmem]
    simp only [rtWrites, calleeStack, smallModel_priv, smallModel_depth, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · exact hl.env_frame _ _ _ henv hag
  · intro mp' f' _ h; exact hl.rep_frame _ _ _ _ h hag
  · exact IsMap.frame hl hmap hag
  · rw [h0, BitVec.toNat_ofNat]
    obtain ⟨-, -, -, hz1, hz2, hz3⟩ := (henv : SmallEnv s.mem t zeroVal)
    rcases hslot with ⟨hn, hp⟩ | ⟨j, hj, hp, hf⟩
    · rw [hp]
      generalize zeroVal = zv at *
      rw [Nat.mod_eq_of_lt (by omega), hn]
      have hin : InRanges zv 8 (smallModel t zv (lo, hi)).priv :=
        ⟨(zv, zv + 8), by simp only [smallModel_priv, List.mem_cons, true_or, or_true],
          Nat.le_refl zv, Nat.le_refl (zv + 8)⟩
      refine ⟨by rw [hag.accessible]; exact hz1, hin, ?_⟩
      rw [hag.readLE hin, hz3]; rfl
    · have h0' : (s.regs 3).toNat ≠ 0 := by
        intro h; simp only [IsMap, h, ite_true] at hmap; rw [hmap] at hf; cases hf
      simp only [IsMap, h0', ite_false, smallModel_rep] at hmap
      rw [hp] at hf
      have hgr := hmap.grp
      have hgi := hmap.grpIn
      have hhb := hmap.heapBound
      have hin : InRanges (slotVal (group s.mem (s.regs 3).toNat) j) 8 (smallModel t zeroVal (lo, hi)).priv :=
        ⟨(lo, hi), by simp only [smallModel_priv, List.mem_cons, true_or], by unfold slotVal; omega,
          by unfold slotVal; omega⟩
      rw [hp, Nat.mod_eq_of_lt (by unfold slotVal; omega), hf]
      refine ⟨?_, hin, ?_⟩
      · rw [hag.accessible]
        exact Arm64.Memory.accessible_mono _ hgr (by unfold slotVal; omega) (by unfold slotVal; omega)
      · rw [hag.readLE hin]
        simp only [Option.getD_some, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (Arm64.Memory.readLE_lt _ _ 8)).symm

end Proof

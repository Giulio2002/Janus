import Extracted

/-!
# `int64_t e_alloca(size_t n)` (C, arm64): an `alloca`'d array, for every `n`

```c
int64_t e_alloca(size_t n) {
	int64_t *p = alloca(n * sizeof *p + 8);
	for (size_t i = 0; i < n; i++) p[i] = (int64_t)i;
	int64_t s = 0;
	for (size_t i = 0; i < n; i++) s += p[i];
	return s;
}
```

**Guarantee.** For every `n` (below `2^59`), every AAPCS64 call of the gcc-compiled `e_alloca`
whose C stack has room for the frame and the allocation (`48 + T` bytes, `T` the 16-rounded
`alloca` size) and whose stack-protector guard is readable returns `0 + 1 + … + (n − 1)
(mod 2^64)`, restores the callee-saved state, and changes memory only in its stack window.

**How.** gcc (with Ubuntu's `-fstack-clash-protection` and stack protector) allocates in two
steps: whole 64 KiB pages, each probed by a store (`probe`, a loop over the pages), then the
remainder rounded to 16 (`and x1, x1, #0xfff0`), and addresses the array at `SP + 16`. The masks
are turned into arithmetic by `and_highMask_eq` / `and_rangeMask_eq`, and the moving `SP` is
tracked as a numeral below the entry `SP` (the dynamic frame). Three loop invariants: `probe`,
`fill`, `sum`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI
open Janus.Contracts.Libc (memFrame_trans)

namespace Proof

/-- The 16-rounded allocation and its 64 KiB part. -/
def T (n : Nat) : Nat := (8 * n + 23) / 16 * 16
def big (n : Nat) : Nat := (8 * n + 23) / 65536 * 65536

/-- The GOT slot of `__stack_chk_guard` (an `R_AARCH64_GLOB_DAT` relocation: the dynamic linker
fills it; named by the relocation's symbol, `Extracted.dyngot`). -/
def gslot : Nat := DynGOT.slotOf Extracted.dyngot "__stack_chk_guard"

def Pre (n : BitVec 64) (s : State) : Prop :=
  n.toNat < 2 ^ 59 ∧ CStack s (48 + T n.toNat) 0 ∧
    s.mem.accessible gslot 8 false = true ∧ s.mem.accessible (s.mem.readLE gslot 8) 8 false = true ∧
    Outside gslot 8 [(s.sp.toNat - (48 + T n.toNat), s.sp.toNat)] ∧
    Outside (s.mem.readLE gslot 8) 8 [(s.sp.toNat - (48 + T n.toNat), s.sp.toNat)]

/-- The guard's GOT slot, as a numeral. -/
abbrev GS : Nat := janus_eval% gslot

/-- The standing facts of a call. -/
structure Ctx (n : BitVec 64) (ret : Nat) (s : State) : Prop where
  hret : RetAddr Extracted.program ret
  hn : n.toNat < 2 ^ 59
  hal : s.sp.toNat % 16 = 0
  hb : 48 + T n.toNat ≤ s.sp.toNat
  ha : s.sp.toNat ≤ 2 ^ 48
  hw : s.mem.accessible (s.sp.toNat - (48 + T n.toNat)) (48 + T n.toNat) true = true
  hga : s.mem.accessible GS 8 false = true
  hgpa : s.mem.accessible (s.mem.readLE GS 8) 8 false = true
  hgo : GS + 8 ≤ s.sp.toNat - (48 + T n.toNat) ∨ s.sp.toNat ≤ GS
  hgpo : s.mem.readLE GS 8 + 8 ≤ s.sp.toNat - (48 + T n.toNat) ∨
    s.sp.toNat ≤ s.mem.readLE GS 8

/-- What a state of the run keeps of the call state `s`. -/
structure Inv (n : BitVec 64) (ret : Nat) (s S : State) : Prop where
  x19 : S.regs 19 = s.regs 19
  x20 : S.regs 20 = s.regs 20
  x21 : S.regs 21 = s.regs 21
  x22 : S.regs 22 = s.regs 22
  x23 : S.regs 23 = s.regs 23
  x24 : S.regs 24 = s.regs 24
  x25 : S.regs 25 = s.regs 25
  x26 : S.regs 26 = s.regs 26
  x27 : S.regs 27 = s.regs 27
  x28 : S.regs 28 = s.regs 28
  x29 : S.regs 29 = s.sp - 16#64
  fpcr : S.fpcr = s.fpcr
  vregs : S.vregs = s.vregs
  mem : MemFrame s.mem S.mem [(s.sp.toNat - (48 + T n.toNat), s.sp.toNat)]
  fp : S.mem.readLE (s.sp.toNat - 16) 8 = (s.regs 29).toNat
  lr : S.mem.readLE (s.sp.toNat - 8) 8 = ret
  canary : S.mem.readLE (s.sp.toNat - 24) 8 = s.mem.readLE (s.mem.readLE GS 8) 8

/-- The goal of a run from the call state `s`. -/
def Q (n : BitVec 64) (s : State) : Outcome → Prop :=
  IsReturn fun s' => CReturn s s' ∧ ((s'.regs 0).toNat = n.toNat * (n.toNat - 1) / 2 % 2 ^ 64 ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - (48 + T n.toNat), s.sp.toNat)])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem epilogue (n : BitVec 64) (ret : Nat) (s S : State) (c : Ctx n ret s) (I : Inv n ret s S)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x94))
    (h0 : S.regs 0 = BitVec.ofNat 64 (n.toNat * (n.toNat - 1) / 2)) :
    Reaches (Extracted.program.withExit ret) S (Q n s) := by
  obtain ⟨hret, hn, hal, hb, ha, hw, hga, hgpa, hgo, hgpo⟩ := c
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, hm, hfp, hlr, hcan⟩ := I
  have h16 : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x94)) := hpc
  clear hpc
  unfold Q
  janus_run [hfp, hlr, hcan]
  refine ⟨?_, hm⟩
  simp only [hv]
  simp

theorem Inv.of_same {n : BitVec 64} {ret : Nat} {s S S' : State} (I : Inv n ret s S)
    (h : ∀ i, 19 ≤ i → i ≤ 29 → S'.regs i = S.regs i) (hm : S'.mem = S.mem) (hf : S'.fpcr = S.fpcr)
    (hv : S'.vregs = S.vregs) : Inv n ret s S' :=
  ⟨(h 19 (by omega) (by omega)).trans I.x19, (h 20 (by omega) (by omega)).trans I.x20,
   (h 21 (by omega) (by omega)).trans I.x21, (h 22 (by omega) (by omega)).trans I.x22,
   (h 23 (by omega) (by omega)).trans I.x23, (h 24 (by omega) (by omega)).trans I.x24,
   (h 25 (by omega) (by omega)).trans I.x25, (h 26 (by omega) (by omega)).trans I.x26,
   (h 27 (by omega) (by omega)).trans I.x27, (h 28 (by omega) (by omega)).trans I.x28,
   (h 29 (by omega) (by omega)).trans I.x29, hf.trans I.fpcr, hv.trans I.vregs,
   hm ▸ I.mem, hm ▸ I.fp, hm ▸ I.lr, hm ▸ I.canary⟩

theorem Inv.of_write {n : BitVec 64} {ret : Nat} {s S S' : State} (I : Inv n ret s S)
    (h : ∀ i, 19 ≤ i → i ≤ 29 → S'.regs i = S.regs i) {a v : Nat}
    (ha1 : s.sp.toNat - (48 + T n.toNat) ≤ a) (ha2 : a + 8 ≤ s.sp.toNat - 24)
    (hm : S'.mem = S.mem.writeLE a 8 v) (hf : S'.fpcr = S.fpcr) (hv : S'.vregs = S.vregs) :
    Inv n ret s S' :=
  ⟨(h 19 (by omega) (by omega)).trans I.x19, (h 20 (by omega) (by omega)).trans I.x20,
   (h 21 (by omega) (by omega)).trans I.x21, (h 22 (by omega) (by omega)).trans I.x22,
   (h 23 (by omega) (by omega)).trans I.x23, (h 24 (by omega) (by omega)).trans I.x24,
   (h 25 (by omega) (by omega)).trans I.x25, (h 26 (by omega) (by omega)).trans I.x26,
   (h 27 (by omega) (by omega)).trans I.x27, (h 28 (by omega) (by omega)).trans I.x28,
   (h 29 (by omega) (by omega)).trans I.x29, hf.trans I.fpcr, hv.trans I.vregs,
   hm ▸ I.mem.writeLE_inRanges v ⟨_, List.mem_singleton_self _, ha1, by omega⟩,
   by rw [hm, Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.fp,
   by rw [hm, Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.lr,
   by rw [hm, Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.canary⟩

theorem tri_succ (j : Nat) : (j + 1) * j / 2 = j * (j - 1) / 2 + j := by
  rcases j with _ | j
  · rfl
  · rw [show (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega,
      Nat.add_mul_div_left _ _ (by omega)]
    simp

theorem T_ge (n : Nat) : 8 * n + 8 ≤ T n := by unfold T; omega

/-- The array: `alloca` returns `SP + 16` after the allocation. -/
def arr (n : Nat) (s : State) : Nat := s.sp.toNat - (48 + T n) + 16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem sumLoop (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (j : Nat), j + k + 1 = n.toNat →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x84) →
      S.regs 1 = BitVec.ofNat 64 (arr n.toNat s + 8 * j) →
      S.regs 2 = BitVec.ofNat 64 (arr n.toNat s + 8 * n.toNat) →
      (S.regs 0).toNat = j * (j - 1) / 2 % 2 ^ 64 →
      (∀ i, i < n.toNat → S.mem.readLE (arr n.toNat s + 8 * i) 8 = i) →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hga, hgpa, hgo, hgpo⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S j hk hpc h1 h2 h0 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * j) 8 false = true :=
      Memory.accessible_read_of_write _ (Memory.accessible_mono _ hw (by unfold arr; omega)
        (by unfold arr; omega))
    have hwj := hwd j (by omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x84)) := hpc
    clear hpc
    janus_run [hwj] until [janus_eval% (Extracted.entry + 0x94)]
    refine epilogue n ret s _ c (I.of_same (fun i h1 h2 => by
      simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl) rfl rfl rfl) rfl ?_
    apply BitVec.eq_of_toNat_eq
    simp only [setReg, show (0 : Nat) ≠ 3 by decide, show (0 : Nat) ≠ 1 by decide, if_false, if_true]
    rw [BitVec.toNat_add, h0, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show n.toNat = j + 1 by omega,
      show j + 1 - 1 = j by omega, tri_succ]
    have : j < 2 ^ 64 := by omega
    have : j * (j - 1) / 2 + j < 2 ^ 64 * 2 ^ 64 := by
      have : j * (j - 1) ≤ j * j := Nat.mul_le_mul_left _ (by omega)
      have : j * j < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' (by omega) (by omega)
      omega
    omega
  | succ k ih =>
    intro S j hk hpc h1 h2 h0 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * j) 8 false = true :=
      Memory.accessible_read_of_write _ (Memory.accessible_mono _ hw (by unfold arr; omega)
        (by unfold arr; omega))
    have hwj := hwd j (by omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x84)) := hpc
    clear hpc
    janus_run [hwj] until [janus_eval% (Extracted.entry + 0x84)]
    refine ih _ (j + 1) (by omega) rfl ?_ h2 ?_ hwd (I.of_same (fun i h1 h2 => by
      simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl) rfl rfl rfl)
    · simp only [setReg, show (1 : Nat) ≠ 3 by decide, if_false, if_true]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [setReg, show (0 : Nat) ≠ 3 by decide, show (0 : Nat) ≠ 1 by decide, if_false, if_true]
      rw [BitVec.toNat_add, h0, BitVec.toNat_ofNat, show j + 1 - 1 = j by omega, tri_succ]
      have : j < 2 ^ 64 := by omega
      omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fillLoop (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (i : Nat), i + k + 1 = n.toNat →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x68) → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 2 = BitVec.ofNat 64 (arr n.toNat s) → S.regs 0 = n →
      (∀ m, m < i → S.mem.readLE (arr n.toNat s + 8 * m) 8 = m) →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hga, hgpa, hgo, hgpo⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S i hk hpc h1 h2 h0 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * i) 8 true = true :=
      Memory.accessible_mono _ hw (by unfold arr; omega) (by unfold arr; omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x68)) := hpc
    clear hpc
    janus_run until [janus_eval% (Extracted.entry + 0x84)]
    have hnn : n.toNat = i + 1 := by omega
    have hrd : ∀ m, m < n.toNat → (S.mem.writeLE (arr n.toNat s + i * 8) 8 i).readLE (arr n.toNat s + 8 * m) 8 = m := by
      intro m hm'
      by_cases hmi : m = i
      · subst hmi
        rw [show arr n.toNat s + m * 8 = arr n.toNat s + 8 * m by omega, Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [Memory.readLE_writeLE_of_disjoint (m := S.mem) i (by omega)]; exact hwd m (by omega)
    rw [← hnn] at *
    refine sumLoop n ret s c (n.toNat - 1) _ 0 (by omega) rfl ?_ ?_ ?_ hrd
      (I.of_write (fun i h1 h2 => by
        simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl)
        (a := arr n.toNat s + i * 8) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl)
    · simp only [setReg, show (1 : Nat) ≠ 2 by decide, if_false, if_true, Nat.mul_zero, Nat.add_zero]
    · simp only [setReg, if_true]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      unfold arr; omega
    · simp [setReg]
  | succ k ih =>
    intro S i hk hpc h1 h2 h0 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * i) 8 true = true :=
      Memory.accessible_mono _ hw (by unfold arr; omega) (by unfold arr; omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x68)) := hpc
    clear hpc
    janus_run until [janus_eval% (Extracted.entry + 0x68)]
    refine ih _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_
      (I.of_write (fun i h1 h2 => by
        simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl)
        (a := arr n.toNat s + i * 8) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl)
    · simp only [setReg, if_true]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp [setReg, h2]
    · simp [setReg, h0]
    · intro m hm'
      by_cases hmi : m = i
      · subst hmi
        rw [show arr n.toNat s + m * 8 = arr n.toNat s + 8 * m by omega, Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [Memory.readLE_writeLE_of_disjoint (m := S.mem) i (by omega)]; exact hwd m (by omega)


theorem T_split (n : Nat) : big n + (8 * n + 23) % 65536 / 16 * 16 = T n := by
  unfold big T; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rest (n : BitVec 64) (ret : Nat) (s S : State) (c : Ctx n ret s) (I : Inv n ret s S)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x48))
    (hsp : S.sp = s.sp - BitVec.ofNat 64 (48 + big n.toNat))
    (h1 : S.regs 1 = BitVec.ofNat 64 (8 * n.toNat + 23)) (h0 : S.regs 0 = n) :
    Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have hTs := T_split n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hga, hgpa, hgo, hgpo⟩ := c'
  have I' := I
  obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, hm, hfp, hlr, hcan⟩ := I'
  have hsmall : (BitVec.ofNat 64 (8 * n.toNat + 23) &&& 65520#64) =
      BitVec.ofNat 64 ((8 * n.toNat + 23) % 65536 / 16 * 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (65520#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 16 - 2 ^ 4) from rfl,
      and_rangeMask_eq _ 4 16 (by omega) (by omega)]
    simp only [BitVec.toNat_ofNat]; omega
  have hacc0 : s.mem.accessible (s.sp.toNat - (48 + T n.toNat)) 8 true = true :=
    Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)
  have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x48)) := hpc
  clear hpc
  janus_run [hsmall] until [janus_eval% (Extracted.entry + 0x50)]
  rw [show 48 + big n.toNat + (8 * n.toNat + 23) % 65536 / 16 * 16 = 48 + T n.toNat by omega]
  have h48T : (s.sp - BitVec.ofNat 64 (48 + T n.toNat)).toNat = s.sp.toNat - (48 + T n.toNat) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hT16 : T n.toNat % 16 = 0 := by unfold T; omega
  generalize hX : s.sp - BitVec.ofNat 64 (48 + T n.toNat) = X
  have hXt : X.toNat = s.sp.toNat - (48 + T n.toNat) := hX ▸ h48T
  have hXa : X.toNat % 16 = 0 := by omega
  clear hX h48T
  janus_run until [janus_eval% (Extracted.entry + 0x68), janus_eval% (Extracted.entry + 0x94)]
  · refine fillLoop n ret s c (n.toNat - 1) _ 0 (by omega) rfl (by simp [setReg]) ?_ (by simp [setReg, h0])
      (fun m hm => absurd hm (by omega)) ?_
    · simp only [setReg, if_true]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hXt]; unfold arr; omega
    · exact Inv.of_write (Inv.of_write I (S' := { S with mem := S.mem.writeLE X.toNat 8 0 }) (a := X.toNat) (v := 0)
        (fun i _ _ => rfl) (by omega) (by omega) rfl rfl rfl) (a := X.toNat + 1024) (v := 0)
        (fun i h1 h2 => by simp only [setReg]; split <;> (try split) <;> first | omega | rfl)
        (by omega) (by omega) rfl I.fpcr.symm rfl
  · refine epilogue n ret s _ c ?_ rfl ?_
    · exact Inv.of_write I (a := X.toNat) (v := 0)
        (fun i h1 h2 => by simp only [setReg]; split <;> (try split) <;> first | omega | rfl)
        (by omega) (by omega) rfl I.fpcr.symm rfl
    · simp only [setReg, show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 1 by decide, if_false, h0]
      rw [show n.toNat = 0 by omega]; apply BitVec.eq_of_toNat_eq; simp; omega
  · refine fillLoop n ret s c (n.toNat - 1) _ 0 (by omega) rfl (by simp [setReg]) ?_ (by simp [setReg, h0])
      (fun m hm => absurd hm (by omega)) ?_
    · simp only [setReg, if_true]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hXt]; unfold arr; omega
    · exact Inv.of_write I (a := X.toNat) (v := 0)
        (fun i h1 h2 => by simp only [setReg]; split <;> (try split) <;> first | omega | rfl)
        (by omega) (by omega) rfl I.fpcr.symm rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem probe (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (j : Nat), j + k + 1 = big n.toNat / 65536 →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x38) →
      S.sp = s.sp - BitVec.ofNat 64 (48 + 65536 * j) →
      S.regs 2 = s.sp - BitVec.ofNat 64 (48 + big n.toNat) →
      S.regs 1 = BitVec.ofNat 64 (8 * n.toNat + 23) → S.regs 0 = n →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have hTs := T_split n.toNat
  have hbig : big n.toNat % 65536 = 0 := by unfold big; omega
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hga, hgpa, hgo, hgpo⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S j hk hpc hsp h2 h1 h0 I
    have I' := I
    obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, hm, hfp, hlr, hcan⟩ := I'
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x38)) := hpc
    clear hpc
    have hX : s.sp - BitVec.ofNat 64 (48 + 65536 * j) - 65536#64 = s.sp - BitVec.ofNat 64 (48 + 65536 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hX] until [janus_eval% (Extracted.entry + 0x48)]
    have hK : 65536 * (j + 1) = big n.toNat := by omega
    refine rest n ret s _ c ?_ rfl (by simp only; rw [hK]) (by simp only; exact h1) (by simp only; exact h0)
    exact Inv.of_write I (fun i _ _ => rfl) (by omega) (by omega) rfl I.fpcr.symm rfl
  | succ k ih =>
    intro S j hk hpc hsp h2 h1 h0 I
    have I' := I
    obtain ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, hm, hfp, hlr, hcan⟩ := I'
    have hpc' : S.pc = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x38)) := hpc
    clear hpc
    have hX : s.sp - BitVec.ofNat 64 (48 + 65536 * j) - 65536#64 = s.sp - BitVec.ofNat 64 (48 + 65536 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hX] until [janus_eval% (Extracted.entry + 0x38)]
    exact ih _ (j + 1) (by omega) rfl rfl (by simp only; exact h2) (by simp only; exact h1) (by simp only; exact h0)
      (Inv.of_write I (fun i _ _ => rfl) (by omega) (by omega) rfl I.fpcr.symm rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem correctness (n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [n] (Pre n)
      (fun s s' => (s'.regs 0).toNat = n.toNat * (n.toNat - 1) / 2 % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - (48 + T n.toNat), s.sp.toNat)]) := by
  intro ret hret s hs ⟨hn, ⟨hal, hb, ha, hw⟩, hga, hgpa, hgo, hgpo⟩
  have e4 : gslot = janus_eval% gslot := rfl
  rw [e4] at hga hgpa hgo hgpo
  simp only [outside_cons, outside_nil, and_true] at hgo hgpo
  janus_intro hs.call
  have hx1 : (n.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64) + 23#64 =
      BitVec.ofNat 64 (8 * n.toNat + 23) := by
    rw [rot61]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hbig : (BitVec.ofNat 64 (8 * n.toNat + 23) &&& 18446744073709486080#64) = BitVec.ofNat 64 (big n.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (18446744073709486080#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 16) from rfl,
      and_highMask_eq _ 16 (by omega)]
    simp only [BitVec.toNat_ofNat, big]; omega
  have hsmall : (BitVec.ofNat 64 (8 * n.toNat + 23) &&& 65520#64) =
      BitVec.ofNat 64 ((8 * n.toNat + 23) % 65536 / 16 * 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (65520#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 16 - 2 ^ 4) from rfl,
      and_rangeMask_eq _ 4 16 (by omega) (by omega)]
    simp only [BitVec.toNat_ofNat]; omega
  have c : Ctx n ret s := ⟨hret, hn, hal, hb, by omega, by simpa using hw, hga, hgpa, hgo, hgpo⟩
  have hT := T_ge n.toNat
  have hr48 := hret.user
  have hInv : ∀ S : State, (∀ i, 19 ≤ i → i ≤ 29 → i ≠ 29 → S.regs i = s.regs i) → S.regs 29 = s.sp - 16#64 →
      S.fpcr = s.fpcr → S.vregs = s.vregs →
      S.mem = ((s.mem.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat (s.regs 29))).writeLE
        (BitVec.toNat s.sp - 8) 8 ret).writeLE (BitVec.toNat s.sp - 24) 8 (s.mem.readLE (s.mem.readLE GS 8) 8) →
      Inv n ret s S := by
    intro S hr h29 hf hv hm
    refine ⟨hr 19 (by omega) (by omega) (by omega), hr 20 (by omega) (by omega) (by omega),
      hr 21 (by omega) (by omega) (by omega), hr 22 (by omega) (by omega) (by omega),
      hr 23 (by omega) (by omega) (by omega), hr 24 (by omega) (by omega) (by omega),
      hr 25 (by omega) (by omega) (by omega), hr 26 (by omega) (by omega) (by omega),
      hr 27 (by omega) (by omega) (by omega), hr 28 (by omega) (by omega) (by omega), h29, hf, hv, ?_, ?_, ?_, ?_⟩
    · rw [hm]; janus_frame
    · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
    · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [hm, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
  janus_run [hx1, hbig, hsmall] until [Extracted.entry + 0x38, Extracted.entry + 0x48]
  · -- no whole page
    have hb0 : big n.toNat = 0 := by
      have : big n.toNat < 2 ^ 64 := by unfold big; omega
      omega
    refine rest n ret s _ c (hInv _ (fun i h1 h2 h3 => by simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl)
      (by simp [setReg]) rfl rfl rfl) rfl (by simp only; rw [hb0]) (by simp [setReg]) (by simp [setReg, h_x0])
  · refine probe n ret s c (big n.toNat / 65536 - 1) _ 0 (by unfold big at *; omega) rfl (by simp only) rfl
      (by simp [setReg]) (by simp [setReg, h_x0])
      (hInv _ (fun i h1 h2 h3 => by simp only [setReg]; split <;> (try split) <;> (try split) <;> first | omega | rfl)
      (by simp [setReg]) rfl rfl rfl)

end Proof

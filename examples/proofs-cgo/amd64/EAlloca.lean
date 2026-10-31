import Extracted

/-!
# `int64_t e_alloca(size_t n)` (C, amd64): an `alloca`'d array, for every `n`

The x86-64 counterpart of the arm64 proof (same C source).

**Guarantee.** For every `n` (below `2^59`), every System V call of the gcc-compiled `e_alloca`
whose C stack has room for the frame and the allocation (`24 + T` bytes below `RSP`, `T` the
16-rounded `alloca` size) and whose stack-protector guard `%fs:0x28` is readable returns
`0 + 1 + … + (n − 1) (mod 2^64)`, restores the callee-saved state, and changes memory only in its
stack window; `__stack_chk_fail@plt` is never reached (the canary at `RBP − 8` is kept).

**How.** gcc (`-fstack-clash-protection`, stack protector) allocates whole 4 KiB pages, each
probed by `orq $0, 0xff8(%rsp)` (`probe`), then the 16-rounded remainder (`and $0xff0, %eax`,
probed at its top when non-zero), and aligns the array to `RSP`. The masks become arithmetic by
`Janus.FFI.and_highMask_eq` / `and_rangeMask_eq`. Loop invariants: `probe`, `fillLoop` (unrolled
by two; an odd `n` stores `p[0]` first), `sumLoop`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI
open Janus.Contracts.Libc (memFrame_trans)

namespace Proof

/-- The 16-rounded allocation and its 4 KiB part. -/
def T (n : Nat) : Nat := (8 * n + 31) / 16 * 16
def big (n : Nat) : Nat := (8 * n + 31) / 4096 * 4096

/-- The stack-protector guard (`%fs:0x28`, glibc's `tcbhead_t.stack_guard`). -/
abbrev guard (s : State) : Nat := s.fsBase.toNat + 0x28

def Pre (n : BitVec 64) (s : State) : Prop :=
  n.toNat < 2 ^ 59 ∧ CStack s (24 + T n.toNat) 8 ∧ guard s + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (guard s) 8 false = true ∧
    Outside (guard s) 8 [((s.regs 4).toNat - (24 + T n.toNat), (s.regs 4).toNat + 8)]

/-- The standing facts of a call. -/
structure Ctx (n : BitVec 64) (ret : Nat) (s : State) : Prop where
  hret : RetAddr Extracted.program ret
  hn : n.toNat < 2 ^ 59
  hal : (s.regs 4).toNat % 16 = 8
  hb : 24 + T n.toNat ≤ (s.regs 4).toNat
  ha : (s.regs 4).toNat + 8 ≤ 2 ^ 48
  hw : s.mem.accessible ((s.regs 4).toNat - (24 + T n.toNat)) (24 + T n.toNat + 8) true = true
  hgb : s.fsBase.toNat + 0x28 + 8 ≤ 2 ^ 48
  hga : s.mem.accessible (s.fsBase.toNat + 0x28) 8 false = true
  hgo : s.fsBase.toNat + 0x28 + 8 ≤ (s.regs 4).toNat - (24 + T n.toNat) ∨
    (s.regs 4).toNat + 8 ≤ s.fsBase.toNat + 0x28
  hr47 : ret < 2 ^ 47

/-- What a state of the run keeps of the call state `s`. -/
structure Inv (n : BitVec 64) (ret : Nat) (s S : State) : Prop where
  rbx : S.regs 3 = s.regs 3
  rbp : S.regs 5 = s.regs 4 - 8#64
  r12 : S.regs 12 = s.regs 12
  r13 : S.regs 13 = s.regs 13
  r14 : S.regs 14 = s.regs 14
  r15 : S.regs 15 = s.regs 15
  fs : S.fsBase = s.fsBase
  df : S.df = false
  mxcsr : S.mxcsr = s.mxcsr
  fpucw : S.fpucw = s.fpucw
  mem : MemFrame s.mem S.mem [((s.regs 4).toNat - (24 + T n.toNat), (s.regs 4).toNat)]
  fp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  lr : S.mem.readLE (s.regs 4).toNat 8 = ret
  canary : S.mem.readLE ((s.regs 4).toNat - 16) 8 = s.mem.readLE (s.fsBase.toNat + 0x28) 8

/-- The goal of a run from the call state `s`. -/
def Q (n : BitVec 64) (s : State) : Amd64.Outcome → Prop :=
  IsReturn fun s' => CReturn s s' ∧ ((s'.regs 0).toNat = n.toNat * (n.toNat - 1) / 2 % 2 ^ 64 ∧
    MemFrame s.mem s'.mem [((s.regs 4).toNat - (24 + T n.toNat), (s.regs 4).toNat)])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem epilogue (n : BitVec 64) (ret : Nat) (s S : State) (c : Ctx n ret s) (I : Inv n ret s S)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xbc))
    (h2 : S.regs 2 = BitVec.ofNat 64 (n.toNat * (n.toNat - 1) / 2)) :
    Reaches (Extracted.program.withExit ret) S (Q n s) := by
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c
  obtain ⟨h3, h5, h12, h13, h14, h15, hfs, hdf, hmx, hcw, hm, hfp, hlr, hcan⟩ := I
  have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0xbc)) := hpc
  clear hpc
  have hgbS : S.fsBase.toNat + 0x28 + 8 ≤ 2 ^ 48 := by rw [hfs]; exact hgb
  have hgacc0 : s.mem.accessible (S.fsBase.toNat + 0x28) 8 false = true := by rw [hfs]; exact hga
  have hgacc : S.mem.accessible (S.fsBase.toNat + 0x28) 8 false = true := by rw [hfs, hm.accessible]; exact hga
  have hgrd : S.mem.readLE (S.fsBase.toNat + 0x28) 8 = s.mem.readLE (s.fsBase.toNat + 0x28) 8 := by
    rw [hfs, hm.readLE _ _ (by simp; omega)]
  unfold Q
  janus64_run [hfp, hlr, hcan, hgrd]
  exact ⟨hcw, hm⟩

theorem Inv.of_same {n : BitVec 64} {ret : Nat} {s S S' : State} (I : Inv n ret s S)
    (h3 : S'.regs 3 = S.regs 3) (h5 : S'.regs 5 = S.regs 5) (h12 : S'.regs 12 = S.regs 12)
    (h13 : S'.regs 13 = S.regs 13) (h14 : S'.regs 14 = S.regs 14) (h15 : S'.regs 15 = S.regs 15)
    (hm : S'.mem = S.mem) (hf : S'.fsBase = S.fsBase) (hd : S'.df = S.df) (hx : S'.mxcsr = S.mxcsr)
    (hc : S'.fpucw = S.fpucw) : Inv n ret s S' :=
  ⟨h3.trans I.rbx, h5.trans I.rbp, h12.trans I.r12, h13.trans I.r13, h14.trans I.r14, h15.trans I.r15,
   hf.trans I.fs, hd.trans I.df, hx.trans I.mxcsr, hc.trans I.fpucw,
   hm ▸ I.mem, hm ▸ I.fp, hm ▸ I.lr, hm ▸ I.canary⟩

theorem Inv.of_write {n : BitVec 64} {ret : Nat} {s S S' : State} (I : Inv n ret s S)
    (h3 : S'.regs 3 = S.regs 3) (h5 : S'.regs 5 = S.regs 5) (h12 : S'.regs 12 = S.regs 12)
    (h13 : S'.regs 13 = S.regs 13) (h14 : S'.regs 14 = S.regs 14) (h15 : S'.regs 15 = S.regs 15)
    {a v : Nat} (ha1 : (s.regs 4).toNat - (24 + T n.toNat) ≤ a) (ha2 : a + 8 ≤ (s.regs 4).toNat - 16)
    (hm : S'.mem = S.mem.writeLE a 8 v) (hf : S'.fsBase = S.fsBase) (hd : S'.df = S.df)
    (hx : S'.mxcsr = S.mxcsr) (hc : S'.fpucw = S.fpucw) : Inv n ret s S' :=
  ⟨h3.trans I.rbx, h5.trans I.rbp, h12.trans I.r12, h13.trans I.r13, h14.trans I.r14, h15.trans I.r15,
   hf.trans I.fs, hd.trans I.df, hx.trans I.mxcsr, hc.trans I.fpucw,
   hm ▸ I.mem.writeLE_inRanges v ⟨_, List.mem_singleton_self _, ha1, by omega⟩,
   by rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.fp,
   by rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.lr,
   by rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) v (by omega)]; exact I.canary⟩

theorem tri_succ (j : Nat) : (j + 1) * j / 2 = j * (j - 1) / 2 + j := by
  rcases j with _ | j
  · rfl
  · rw [show (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega,
      Nat.add_mul_div_left _ _ (by omega)]
    simp

theorem T_ge (n : Nat) : 8 * n + 16 ≤ T n := by unfold T; omega
theorem T_split (n : Nat) : big n + (8 * n + 31) % 4096 / 16 * 16 = T n := by unfold big T; omega

/-- The array: `alloca` returns the (16-aligned) `RSP` after the allocation. -/
def arr (n : Nat) (s : State) : Nat := (s.regs 4).toNat - (24 + T n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem sumLoop (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (j : Nat), j + k + 1 = n.toNat →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0xb0) →
      S.regs 0 = BitVec.ofNat 64 (arr n.toNat s + 8 * j) →
      S.regs 1 = BitVec.ofNat 64 (arr n.toNat s + 8 * n.toNat) →
      (S.regs 2).toNat = j * (j - 1) / 2 % 2 ^ 64 →
      (∀ i, i < n.toNat → S.mem.readLE (arr n.toNat s + 8 * i) 8 = i) →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S j hk hpc h0 h1 h2 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * j) 8 false = true :=
      Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hw
        (by unfold arr; omega) (by unfold arr; omega))
    have hwj := hwd j (by omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0xb0)) := hpc
    clear hpc
    janus64_run [hwj] until [janus_eval% (Extracted.entry + 0xbc)]
    refine epilogue n ret s _ c (I.of_same (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      rfl rfl rfl rfl rfl) rfl ?_
    apply BitVec.eq_of_toNat_eq
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
    rw [BitVec.toNat_add, h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show n.toNat = j + 1 by omega,
      show j + 1 - 1 = j by omega, tri_succ]
    have : j < 2 ^ 64 := by omega
    omega
  | succ k ih =>
    intro S j hk hpc h0 h1 h2 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * j) 8 false = true :=
      Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hw
        (by unfold arr; omega) (by unfold arr; omega))
    have hwj := hwd j (by omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0xb0)) := hpc
    clear hpc
    janus64_run [hwj] until [janus_eval% (Extracted.entry + 0xb0)]
    refine ih _ (j + 1) (by omega) rfl ?_ (by simp [setRegF_apply, h1]) ?_ hwd
      (I.of_same (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      rfl rfl rfl rfl rfl)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      rw [BitVec.toNat_add, h2, BitVec.toNat_ofNat, show j + 1 - 1 = j by omega, tri_succ]
      have : j < 2 ^ 64 := by omega
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fillLoop (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (i : Nat), i + 2 * (k + 1) = n.toNat →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x90) → S.regs 2 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 (arr n.toNat s) → S.regs 7 = n →
      (∀ m, m < i → S.mem.readLE (arr n.toNat s + 8 * m) 8 = m) →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S i hk hpc h2 h0 h7 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * i) 16 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hw (by unfold arr; omega) (by unfold arr; omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x90)) := hpc
    clear hpc
    janus64_run until [janus_eval% (Extracted.entry + 0xb0)]
    have hrd : ∀ m, m < i + 2 → ((S.mem.writeLE (arr n.toNat s + i * 8) 8 i).writeLE
        (arr n.toNat s + (i + 1) * 8) 8 (i + 1)).readLE (arr n.toNat s + 8 * m) 8 = m := by
      intro m hm'
      by_cases hm1 : m = i + 1
      · subst hm1
        rw [show arr n.toNat s + (i + 1) * 8 = arr n.toNat s + 8 * (i + 1) by omega,
          Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem.writeLE _ _ _) (i + 1) (by omega)]
        by_cases hmi : m = i
        · subst hmi
          rw [show arr n.toNat s + m * 8 = arr n.toNat s + 8 * m by omega, Janus.Arm64.Memory.readLE_writeLE_self]
          exact Nat.mod_eq_of_lt (by omega)
        · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) i (by omega)]; exact hwd m (by omega)
    have hnn : n.toNat = i + 2 := by omega
    have hrd' : ∀ m, m < n.toNat → ((S.mem.writeLE (arr n.toNat s + i * 8) 8 i).writeLE
        (arr n.toNat s + (i + 1) * 8) 8 (i + 1)).readLE (arr n.toNat s + 8 * m) 8 = m :=
      fun m hm => hrd m (by omega)
    have I1 : Inv n ret s { S with mem := S.mem.writeLE (arr n.toNat s + i * 8) 8 i } :=
      Inv.of_write I rfl rfl rfl rfl rfl rfl (a := arr n.toNat s + i * 8) (by unfold arr; omega)
        (by unfold arr; omega) rfl rfl rfl rfl rfl
    refine sumLoop n ret s c (n.toNat - 1) _ 0 (by omega) rfl ?_ ?_ (by simp [setRegF_apply]) (by first | exact hrd' | exact hnn ▸ hrd)
      (Inv.of_write I1 (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (a := arr n.toNat s + (i + 1) * 8) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl rfl rfl)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h0, Nat.mul_zero, Nat.add_zero]
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      unfold arr; omega
  | succ k ih =>
    intro S i hk hpc h2 h0 h7 hwd I
    have hm := I.mem
    have hacc : s.mem.accessible (arr n.toNat s + 8 * i) 16 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hw (by unfold arr; omega) (by unfold arr; omega)
    have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x90)) := hpc
    clear hpc
    janus64_run until [janus_eval% (Extracted.entry + 0x90)]
    have I1 : Inv n ret s { S with mem := S.mem.writeLE (arr n.toNat s + i * 8) 8 i } :=
      Inv.of_write I rfl rfl rfl rfl rfl rfl (a := arr n.toNat s + i * 8) (by unfold arr; omega)
        (by unfold arr; omega) rfl rfl rfl rfl rfl
    refine ih _ (i + 2) (by omega) rfl ?_ (by simp [setRegF_apply, h0]) (by simp [setRegF_apply, h7]) ?_
      (Inv.of_write I1 (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (a := arr n.toNat s + (i + 1) * 8) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl rfl rfl)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · intro m hm'
      by_cases hm1 : m = i + 1
      · subst hm1
        rw [show arr n.toNat s + (i + 1) * 8 = arr n.toNat s + 8 * (i + 1) by omega,
          Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem.writeLE _ _ _) (i + 1) (by omega)]
        by_cases hmi : m = i
        · subst hmi
          rw [show arr n.toNat s + m * 8 = arr n.toNat s + 8 * m by omega, Janus.Arm64.Memory.readLE_writeLE_self]
          exact Nat.mod_eq_of_lt (by omega)
        · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) i (by omega)]; exact hwd m (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem alloc58 (n : BitVec 64) (ret : Nat) (s S : State) (c : Ctx n ret s) (I : Inv n ret s S)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x58))
    (hsp : S.regs 4 = BitVec.ofNat 64 (arr n.toNat s)) (h7 : S.regs 7 = n) :
    Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c'
  have hm := I.mem
  have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x58)) := hpc
  clear hpc
  have hT16 : T n.toNat % 16 = 0 := by unfold T; omega
  have harr : arr n.toNat s + 15 &&& 18446744073709551600 = arr n.toNat s := by
    have h := Janus.FFI.and_highMask_eq (BitVec.ofNat 64 (arr n.toNat s + 15)) 4 (by omega)
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := arr n.toNat s + 15) (by unfold arr; omega)] at h
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at h
    rw [h]; unfold arr; omega
  have hacc : s.mem.accessible (arr n.toNat s) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hw (by unfold arr; omega) (by unfold arr; omega)
  have hlt : arr n.toNat s + 8 * n.toNat < 2 ^ 64 := by unfold arr; omega
  have hlt15 : arr n.toNat s + 15 < 2 ^ 64 := by unfold arr; omega
  have hB : BitVec.ofNat 64 (arr n.toNat s) + 15#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (arr n.toNat s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := arr n.toNat s) (by omega), Nat.mod_eq_of_lt (a := arr n.toNat s + 15) (by omega)]
    rw [show (18446744073709551600 : Nat) % 2 ^ 64 = 18446744073709551600 from rfl]; exact harr
  have hpar : (BitVec.setWidth 8 n &&& 1#8).toNat = n.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, show (1#8 : BitVec 8).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  janus64_run [harr, hB] until [janus_eval% (Extracted.entry + 0x90), janus_eval% (Extracted.entry + 0xb0),
    janus_eval% (Extracted.entry + 0xbc)]
  · -- n = 0
    refine epilogue n ret s _ c (I.of_same (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      rfl rfl rfl rfl rfl) rfl ?_
    simp only [setRegF_apply, ↓reduceIte, hbr]
  · -- n even, n ≠ 0
    have hev' : n.toNat % 2 = 0 := by have := congrArg BitVec.toNat hbr; rw [hpar] at this; simpa using this
    refine fillLoop n ret s c (n.toNat / 2 - 1) _ 0 (by omega) rfl (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply, h7]) (fun m hm => absurd hm (by omega))
      (I.of_same (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      rfl rfl rfl rfl rfl)
  · -- n = 1
    have hn1' : n.toNat = 1 := by omega
    refine sumLoop n ret s c 0 _ 0 (by omega) rfl (by simp [setRegF_apply]) ?_ (by simp [setRegF_apply]) ?_
      (Inv.of_write I (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (a := arr n.toNat s) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl rfl rfl)
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    · intro i hi
      rw [show i = 0 by omega, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]
  · -- n odd, n ≥ 3
    rename_i hn0 hodd
    have hodd' : n.toNat % 2 = 1 := by
      have : ¬ (BitVec.setWidth 8 n &&& 1#8).toNat = 0 := fun h => hodd (BitVec.eq_of_toNat_eq h)
      rw [hpar] at this; omega
    refine fillLoop n ret s c ((n.toNat - 1) / 2 - 1) _ 1 (by omega) rfl (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply, h7]) ?_
      (Inv.of_write I (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (a := arr n.toNat s) (by unfold arr; omega) (by unfold arr; omega) rfl rfl rfl rfl rfl)
    intro m hm
    rw [show m = 0 by omega, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rest (n : BitVec 64) (ret : Nat) (s S : State) (c : Ctx n ret s) (I : Inv n ret s S)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x4b))
    (hsp : S.regs 4 = s.regs 4 - BitVec.ofNat 64 (24 + big n.toNat))
    (h0 : S.regs 0 = BitVec.ofNat 64 (8 * n.toNat + 31)) (h7 : S.regs 7 = n) :
    Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have hTs := T_split n.toNat
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c'
  have I' := I
  obtain ⟨h3, h5, h12, h13, h14, h15, hfs, hdf, hmx, hcw, hm, hfp, hlr, hcan⟩ := I'
  have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x4b)) := hpc
  clear hpc
  have hsm : (8 * n.toNat + 31) % 4294967296 &&& 4080 = (8 * n.toNat + 31) % 4096 / 16 * 16 := by
    have h := Janus.FFI.and_rangeMask_eq (BitVec.ofNat 64 ((8 * n.toNat + 31) % 4294967296)) 4 12 (by omega) (by omega)
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    rw [Nat.mod_eq_of_lt (a := (8 * n.toNat + 31) % 4294967296) (by omega)] at h
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at h
    rw [h]; omega
  have hsB : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (8 * n.toNat + 31)) &&& 4080#32) =
      BitVec.ofNat 64 ((8 * n.toNat + 31) % 4096 / 16 * 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 8 * n.toNat + 31) (by omega), show 4080 % 2 ^ 32 = 4080 from rfl, hsm,
      BitVec.toNat_ofNat]
  have hX : s.regs 4 - BitVec.ofNat 64 (24 + big n.toNat) - BitVec.ofNat 64 ((8 * n.toNat + 31) % 4096 / 16 * 16) =
      BitVec.ofNat 64 (arr n.toNat s) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, arr]; omega
  have harr_eq : arr n.toNat s = (s.regs 4).toNat - (24 + T n.toNat) := rfl
  have harr_b : arr n.toNat s + T n.toNat ≤ 2 ^ 48 := by omega
  janus64_run [hsm, hsB, hX] until [janus_eval% (Extracted.entry + 0x58)]
  · exact alloc58 n ret s _ c (I.of_same (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      rfl rfl I.df.symm hmx.symm rfl) rfl (by simp [setRegF_apply]) (by simp [setRegF_apply, h7])
  · exact alloc58 n ret s _ c (Inv.of_write I (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (a := arr n.toNat s + ((8 * n.toNat + 31) % 4096 / 16 * 16 - 8)) (by omega) (by omega) rfl rfl I.df.symm
      hmx.symm rfl) rfl (by simp [setRegF_apply]) (by simp [setRegF_apply, h7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem probe (n : BitVec 64) (ret : Nat) (s : State) (c : Ctx n ret s) :
    ∀ k (S : State) (j : Nat), j + k + 1 = big n.toNat / 4096 →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x36) →
      S.regs 4 = s.regs 4 - BitVec.ofNat 64 (24 + 4096 * j) →
      S.regs 2 = s.regs 4 - BitVec.ofNat 64 (24 + big n.toNat) →
      S.regs 0 = BitVec.ofNat 64 (8 * n.toNat + 31) → S.regs 7 = n →
      Inv n ret s S → Reaches (Extracted.program.withExit ret) S (Q n s) := by
  have hT := T_ge n.toNat
  have hTs := T_split n.toNat
  have hbig : big n.toNat % 4096 = 0 := by unfold big; omega
  have c' := c
  obtain ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩ := c'
  intro k
  induction k with
  | zero =>
    intro S j hk hpc hsp h2 h0 h7 I
    have hm := I.mem
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x36)) := hpc
    clear hpc
    have hX : s.regs 4 - BitVec.ofNat 64 (24 + 4096 * j) - 4096#64 = s.regs 4 - BitVec.ofNat 64 (24 + 4096 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hX] until [janus_eval% (Extracted.entry + 0x4b)]
    have hK : 4096 * (j + 1) = big n.toNat := by omega
    refine rest n ret s _ c (Inv.of_write I (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by omega) (by omega) rfl rfl rfl rfl rfl) rfl (by simp [setRegF_apply]; rw [hK])
      (by simp [setRegF_apply, h0]) (by simp [setRegF_apply, h7])
  | succ k ih =>
    intro S j hk hpc hsp h2 h0 h7 I
    have hm := I.mem
    have hpc' : S.rip = BitVec.ofNat 64 (janus_eval% (Extracted.entry + 0x36)) := hpc
    clear hpc
    have hX : s.regs 4 - BitVec.ofNat 64 (24 + 4096 * j) - 4096#64 = s.regs 4 - BitVec.ofNat 64 (24 + 4096 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hX] until [janus_eval% (Extracted.entry + 0x36)]
    exact ih _ (j + 1) (by omega) rfl (by simp [setRegF_apply]) (by simp [setRegF_apply, h2])
      (by simp [setRegF_apply, h0]) (by simp [setRegF_apply, h7])
      (Inv.of_write I (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by omega) (by omega) rfl rfl rfl rfl rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem correctness (n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [n] (Pre n)
      (fun s s' => (s'.regs 0).toNat = n.toNat * (n.toNat - 1) / 2 % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - (24 + T n.toNat), (s.regs 4).toNat)]) := by
  intro ret hret s hs ⟨hn, ⟨hal, hb, ha, hw⟩, hgb, hga, hgo⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = n := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Amd64.Program.withExit] at hal hb ha hw h_ret
  simp only [guard, outside_cons, outside_nil, and_true] at hgb hga hgo
  have hr47 : ret < 2 ^ 47 := hret.user
  have c : Ctx n ret s := ⟨hret, hn, hal, hb, ha, hw, hgb, hga, hgo, hr47⟩
  have hx1 : n <<< 3 + 31#64 = BitVec.ofNat 64 (8 * n.toNat + 31) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have hbig : (BitVec.ofNat 64 (8 * n.toNat + 31) &&& 18446744073709547520#64) = BitVec.ofNat 64 (big n.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show (18446744073709547520#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 12) from rfl,
      Janus.FFI.and_highMask_eq _ 12 (by omega)]
    simp only [BitVec.toNat_ofNat, big]; omega
  have hT := T_ge n.toNat
  have hTs := T_split n.toNat
  have hInv : ∀ S : State, S.regs 3 = s.regs 3 → S.regs 5 = s.regs 4 - 8#64 → S.regs 12 = s.regs 12 →
      S.regs 13 = s.regs 13 → S.regs 14 = s.regs 14 → S.regs 15 = s.regs 15 → S.fsBase = s.fsBase →
      S.df = false → S.mxcsr = s.mxcsr → S.fpucw = s.fpucw →
      S.mem = (s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 16) 8
        (s.mem.readLE (s.fsBase.toNat + 40) 8) → Inv n ret s S := by
    intro S h3 h5 h12 h13 h14 h15 hf hd hx hc hm
    refine ⟨h3, h5, h12, h13, h14, h15, hf, hd, hx, hc, ?_, ?_, ?_, ?_⟩
    · rw [hm]; janus_frame
    · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 5).isLt
    · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), h_ret]
    · rw [hm, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)
  janus64_run [hx1, hbig] until [Extracted.entry + 0x36, Extracted.entry + 0x4b]
  · -- no whole page
    have hb0 : big n.toNat = 0 := by
      have : big n.toNat < 2 ^ 64 := by unfold big; omega
      omega
    refine rest n ret s _ c (hInv _ (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl rfl rfl rfl rfl) rfl
      (by simp [setRegF_apply, hb0]) (by simp [setRegF_apply]) (by simp [setRegF_apply, h_a0])
  · refine probe n ret s c (big n.toNat / 4096 - 1) _ 0 (by unfold big at *; omega) rfl (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply, h_a0])
      (hInv _ (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl rfl rfl rfl rfl)

end Proof

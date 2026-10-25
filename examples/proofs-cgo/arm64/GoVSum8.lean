import Extracted

/-!
# `VSum8(a, …, h int64) int64` (Go) → `k_vsum8` (C) → `k_vsum(8, a, …, h)` (C, variadic) → back to
# Go, end to end (arm64)

```go
func VSum8(a, b, c, d, e, f, g, h int64) int64 { return int64(C.k_vsum8(C.int64_t(a), …, C.int64_t(h))) }
```
```c
int64_t k_vsum8(int64_t a, …, int64_t h) { return k_vsum(8, a, b, c, d, e, f, g, h); }
```

**Guarantee (`correctness`).** For all 64-bit `a … h`, every Go call of
`example.com/cgo/cabi.VSum8` satisfying `GoPre` (stack checks, 160 bytes of stack, the cgo
globals as statically initialised, and the GOT slot of `__stack_chk_guard` and the guard readable
Go memory away from the stacks) returns, restores `SP`, `g` and the frame pointer, and leaves
`a + b + … + h` (mod 2^64) in `X0`, under the trusted `CgoCall` contract only.

**How.** `k_vsum8` makes the variadic call `k_vsum(8, a, …, h)`: `n` in `W0`, `a`–`g` in
`X1`–`X7` and `h` in the first stacked slot, which is where the classification of the variadic
call puts them (on Linux variadic arguments are passed as named ones). The callee contract of
`k_vsum` (as in `KVSum.lean`, proved for every argument count) states its precondition in terms
of the classification (`VPre.args`: `PieceAt … (intLoc …)`); `vpre8_iff` evaluates it for eight
arguments, and `janus_run` proves it at `k_vsum8`'s call site.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C Janus.Spec Janus.FFI

namespace Proof

/-! ## The variadic C function `k_vsum` (as in `KVSum.lean`), as a callee summary -/

abbrev entry : Nat := segAddr Extracted.program "k_vsum"

/-- The prototype of the call `k_vsum(|xs|, xs…)`. -/
def sig (xs : List (BitVec 64)) : AAPCS64.Sig :=
  ⟨some (.int 8 true), .int 4 true :: xs.map fun _ => .int 8 true, some 1⟩

theorem assign_n : AAPCS64.assign {} (.int 4 true) = (.direct [⟨0, 4, .gpr 0⟩], ⟨1, 0, 0⟩) := by
  decide

/-- The GOT slot of `__stack_chk_guard` (`adrp x0, …; ldr x0, [x0, #…]` at `k_vsum+0x8`). -/
def got : Nat :=
  adrpLdTarget (entry + 0x8) (segWord Extracted.program "k_vsum" 2)
    (segWord Extracted.program "k_vsum" 3) 3

/-- The sum of the first `i` words, mod 2^64. -/
def psum (xs : List (BitVec 64)) (i : Nat) : BitVec 64 := BitVec.ofNat 64 ((xs.take i).map BitVec.toNat).sum

theorem psum_succ (xs : List (BitVec 64)) (i : Nat) (hi : i < xs.length) :
    psum xs (i + 1) = psum xs i + xs[i] := by
  apply BitVec.eq_of_toNat_eq
  simp only [psum, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- What `k_vsum` needs at its entry (the facts `CCallA` gives, the frame and the canary). -/
structure VPre (xs : List (BitVec 64)) (s : State) : Prop where
  n : (s.regs 0).toNat % 2 ^ 32 = xs.length
  len : xs.length < 2 ^ 31
  args : ∀ i (hi : i < xs.length), PieceAt s xs[i].toNat ⟨0, 8, intLoc ⟨1, 0, 0⟩ i⟩
  al : s.sp.toNat % 16 = 0
  b : 128 ≤ s.sp.toNat
  top : s.sp.toNat ≤ 2 ^ 48
  acc : s.mem.accessible (s.sp.toNat - 128) 128 true = true
  ga : s.mem.accessible got 8 false = true
  gb : got + 8 ≤ 2 ^ 48
  Ga : s.mem.accessible (s.mem.readLE got 8) 8 false = true
  Gb : s.mem.readLE got 8 + 8 ≤ 2 ^ 48
  go : got + 8 ≤ s.sp.toNat - 128 ∨ s.sp.toNat ≤ got
  Go : s.mem.readLE got 8 + 8 ≤ s.sp.toNat - 128 ∨ s.sp.toNat ≤ s.mem.readLE got 8
  lra : (s.regs 30).toNat % 4 = 0
  lrb : (s.regs 30).toNat < 2 ^ 56

/-- What `k_vsum` guarantees: `SP`, `X19`–`X29`, the SIMD&FP registers and `FPCR` kept, memory
changed only in its frame, the sum in `X0`. -/
abbrev VPost (xs : List (BitVec 64)) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - 128, s.sp.toNat)] ∧ s'.regs 0 = psum xs xs.length

/-- The frame after the prologue. -/
def M (s : State) : Memory :=
  ((((((((((((((s.mem.writeLE (s.sp.toNat - 80) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat - 72) 8 (s.regs 30).toNat).writeLE
    (s.sp.toNat - 56) 8 (s.regs 1).toNat).writeLE
    (s.sp.toNat - 48) 8 (s.regs 2).toNat).writeLE
    (s.sp.toNat - 40) 8 (s.regs 3).toNat).writeLE
    (s.sp.toNat - 32) 8 (s.regs 4).toNat).writeLE
    (s.sp.toNat - 24) 8 (s.regs 5).toNat).writeLE
    (s.sp.toNat - 16) 8 (s.regs 6).toNat).writeLE
    (s.sp.toNat - 8) 8 (s.regs 7).toNat).writeLE
    (s.sp.toNat - 88) 8 (s.mem.readLE (s.mem.readLE got 8) 8)).writeLE
    (s.sp.toNat - 120) 8 s.sp.toNat).writeLE
    (s.sp.toNat - 112) 8 s.sp.toNat).writeLE
    (s.sp.toNat - 104) 8 (s.sp.toNat - 64)).writeLE
    (s.sp.toNat - 96) 4 4294967240).writeLE
    (s.sp.toNat - 92) 4 0

theorem M_frame (s : State) (hb : 128 ≤ s.sp.toNat) :
    MemFrame s.mem (M s) [(s.sp.toNat - 128, s.sp.toNat)] := by
  unfold M; janus_frame

/-- The general-register save area: `X(i+1)` at `SP - 56 + 8i`. -/
theorem M_save (s : State) (hb : 128 ≤ s.sp.toNat) (i : Nat) (hi : i < 7) :
    (M s).readLE (s.sp.toNat - (56 - 8 * i)) 8 = (s.regs (i + 1)).toNat := by
  have h := fun (r : Nat) => (s.regs r).isLt
  unfold M
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, Nat.reducePow,
    Nat.sub_zero] <;>
  exact Nat.mod_eq_of_lt (h _)

/-- The other reads of the frame: the saved `X29`, `X30` and the canary. -/
theorem M_fp (s : State) (hb : 128 ≤ s.sp.toNat) : (M s).readLE (s.sp.toNat - 80) 8 = (s.regs 29).toNat := by
  unfold M
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
  exact Nat.mod_eq_of_lt (s.regs 29).isLt

theorem M_lr (s : State) (hb : 128 ≤ s.sp.toNat) : (M s).readLE (s.sp.toNat - 72) 8 = (s.regs 30).toNat := by
  unfold M
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
  exact Nat.mod_eq_of_lt (s.regs 30).isLt

theorem M_canary (s : State) (hb : 128 ≤ s.sp.toNat) :
    (M s).readLE (s.sp.toNat - 88) 8 = s.mem.readLE (s.mem.readLE got 8) 8 := by
  unfold M
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
  exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)

/-- Memory outside the frame reads as before. -/
theorem M_out (s : State) (hb : 128 ≤ s.sp.toNat) (a n : Nat)
    (h : a + n ≤ s.sp.toNat - 128 ∨ s.sp.toNat ≤ a) : (M s).readLE a n = s.mem.readLE a n :=
  (M_frame s hb).readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)

theorem M_acc (s : State) (hb : 128 ≤ s.sp.toNat) (a n : Nat) (w : Bool) :
    (M s).accessible a n w = s.mem.accessible a n w := by
  unfold M; simp only [Memory.accessible_writeLE]

/-- `VPost` with the result `acc`. -/
abbrev EPost (acc : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - 128, s.sp.toNat)] ∧ s'.regs 0 = acc

/-- `S` agrees with the state after the prologue on everything the rest of `k_vsum` keeps. -/
structure Kept (s S : State) : Prop where
  sp : S.sp = s.sp - 128#64
  mem : S.mem = M s
  r19 : S.regs 19 = s.regs 19
  r20 : S.regs 20 = s.regs 20
  r21 : S.regs 21 = s.regs 21
  r22 : S.regs 22 = s.regs 22
  r23 : S.regs 23 = s.regs 23
  r24 : S.regs 24 = s.regs 24
  r25 : S.regs 25 = s.regs 25
  r26 : S.regs 26 = s.regs 26
  r27 : S.regs 27 = s.regs 27
  r28 : S.regs 28 = s.regs 28
  r30 : S.regs 30 = s.regs 30
  v : S.vregs = s.vregs
  fpcr : S.fpcr = s.fpcr

set_option maxHeartbeats 2000000 in
/-- The epilogue (`k_vsum+0xb0`): the canary check passes, the frame is popped, `X0` returned. -/
theorem epilogue (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) (S : State) (acc : BitVec 64)
    (hpc : S.pc = BitVec.ofNat 64 (entry + 0xb0)) (hk : Kept s S) (h0 : S.regs 0 = acc) :
    ReachesRet Extracted.program (s.regs 30) S (EPost acc s) := by
  obtain ⟨hsp, hm, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h30, hv, hfc⟩ := hk
  have hal := hp.al; have hb := hp.b; have htop := hp.top; have hacc := hp.acc
  have hga := hp.ga; have hgb := hp.gb; have hGa := hp.Ga; have hGb := hp.Gb
  have hgo := hp.go; have hGo := hp.Go; have hlra := hp.lra; have hlrb := hp.lrb
  have hM := M_frame s hb
  have hgM := M_out s hb got 8 hgo
  have hGM := M_out s hb _ 8 hGo
  have hfp := M_fp s hb; have hlr := M_lr s hb; have hcan := M_canary s hb
  rw [← M_acc s hb] at hacc hga hGa
  janus_eval_nat h_got : got
  rw [h_got] at hga hgb hGa hGb hgo hGo hgM hGM hcan
  clear hgo hGo hM
  janus_run [BitVec.ofNat_toNat, BitVec.setWidth_eq, hcan, hgM, hGM, hlr, hfp]
  simp only [EPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h19, h20, h21, h22, h23, h24, h25,
    h26, h27, h28, h0, hv, true_and]
  exact ⟨M_frame s hb, trivial⟩

/-- The stacked variadic argument `xs[i]` (`i ≥ 7`), read in the frame memory. -/
theorem stack_arg (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) (i : Nat) (h7 : 7 ≤ i)
    (hi : i < xs.length) :
    s.sp.toNat + 8 * (i - 7) + 8 ≤ 2 ^ 48 ∧
      (M s).accessible (s.sp.toNat + 8 * (i - 7)) 8 false = true ∧
      (M s).readLE (s.sp.toNat + 8 * (i - 7)) 8 = xs[i].toNat := by
  have h := hp.args i hi
  rw [intLoc_stack _ _ (by simp; omega)] at h
  simp only [Nat.zero_add, show 1 + i - 8 = i - 7 by omega] at h
  rw [pieceAt_stack_word] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by rw [M_acc s hp.b]; exact h2, ?_⟩
  rw [M_out s hp.b _ _ (Or.inr (by omega))]; exact h3

/-- `cmp wN, #0`: the flags of `x - 0`. -/
theorem addSub_zero_snd (x : BitVec 32) :
    (addSub x 0#32 true).snd = ⟨x.msb, decide (x = 0#32), true, false⟩ := by
  have hx := x.isLt
  have e : BitVec.ofNat 32 (x.toNat + (~~~(0#32)).toNat + (true).toNat) = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_ofNat]; simp; omega
  simp only [addSub, ↓reduceIte, addWithCarry, e]
  congr 1
  · simp only [BitVec.toNat_not]; simp; omega
  · simp only [decide_eq_false_iff_not, Decidable.not_not]
    rw [BitVec.toInt_not]; simp; omega

/-- The loop counter `W1` after `add w1, w1, #1`. -/
theorem cnt_succ (i : Nat) (h : i + 1 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 i) + 1#32) = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `cmp w8, w1` of the loop: `W8 = n` and `W1 = i + 1`. -/
theorem cnt_eq (k i : Nat) (hk : k < 2 ^ 31) (hi : i + 1 < 2 ^ 31) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 k) =
      BitVec.setWidth 32 (BitVec.ofNat 64 (i + 1))) ↔ k = i + 1 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

macro "kept_tac" hk:term : tactic => `(tactic|
  (constructor <;> simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, ($hk).sp, ($hk).mem,
    ($hk).r19, ($hk).r20, ($hk).r21, ($hk).r22, ($hk).r23, ($hk).r24, ($hk).r25, ($hk).r26,
    ($hk).r27, ($hk).r28, ($hk).r30, ($hk).v, ($hk).fpcr]))

set_option maxHeartbeats 4000000 in
/-- The loop over the stacked arguments (`k_vsum+0x80` and its unrolled copy at `+0x98`), after
`i ≥ 8` arguments: by induction on the arguments left. -/
theorem stack_phase (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) :
    ∀ m i (S : State) (b : Bool), i + m = xs.length → 8 ≤ i → i < xs.length →
      S.pc = BitVec.ofNat 64 (entry + if b then 0x98 else 0x80) → Kept s S →
      S.regs 0 = psum xs i → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 2 = BitVec.ofNat 64 (s.sp.toNat + 8 * (i - 8)) →
      S.regs 8 = BitVec.ofNat 64 xs.length →
      ReachesRet Extracted.program (s.regs 30) S (EPost (psum xs xs.length) s) := by
  intro m
  induction m with
  | zero => intro i S b hm _ hi; omega
  | succ m ih =>
    intro i S b hm h8 hlt hpc hk h0 h1 h2 h8r
    have hlen := hp.len
    have htop := hp.top
    obtain ⟨hab, hacc, hrd⟩ := stack_arg xs s hp i (by omega) (by omega)
    have e : s.sp.toNat + 8 * (i - 8) + 8 = s.sp.toNat + 8 * (i - 7) := by omega
    have hrd7 := hrd
    rw [← e] at hab hacc hrd
    have hsp := hk.sp; have hm' := hk.mem
    have hc := cnt_succ i (by omega)
    have hn2 : BitVec.ofNat 64 (s.sp.toNat + 8 * (i - 8)) + 8#64 =
        BitVec.ofNat 64 (s.sp.toNat + 8 * (i + 1 - 8)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hsum := (psum_succ xs i hlt).symm
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hpc
      janus_run [hrd, hrd7, hc, hn2, hsum] until [entry + 0x98, entry + 0xb0]
      · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
        refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
        simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hrd7, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, hsum, show i + 1 = xs.length by omega]
      · refine ih (i + 1) _ true (by omega) (by omega) ?_ rfl (by kept_tac hk) ?_ ?_ ?_ ?_
        · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr; omega
        all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h8r, hrd7,
          BitVec.ofNat_toNat, BitVec.setWidth_eq, hsum, show i + 1 - 8 = i - 7 by omega]
    · simp only [↓reduceIte] at hpc
      janus_run [hrd, hrd7, hc, hn2, hsum] until [entry + 0x80, entry + 0xb0]
      · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
        refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
        simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hrd7, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, hsum, show i + 1 = xs.length by omega]
      · refine ih (i + 1) _ false (by omega) (by omega) ?_ rfl (by kept_tac hk) ?_ ?_ ?_ ?_
        · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr; omega
        all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h8r, hrd7,
          BitVec.ofNat_toNat, BitVec.setWidth_eq, hsum, show i + 1 - 8 = i - 7 by omega]

set_option maxHeartbeats 4000000 in
/-- The loop while `__gr_offs < 0` (`k_vsum+0x5c`), after `i ≤ 7` arguments: `va_arg` reads the
saved `X(i+1)`; at `i = 7` it moves on to the stacked arguments. By induction on `7 - i`. -/
theorem reg_phase (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) :
    ∀ m i (S : State), i + m = 7 → i < xs.length →
      S.pc = BitVec.ofNat 64 (entry + 0x5c) → Kept s S →
      S.regs 0 = psum xs i → S.regs 1 = BitVec.ofNat 64 i → S.regs 2 = s.sp →
      S.regs 3 = BitVec.ofNat 64 ((2 ^ 32 - 56 + 8 * i) % 2 ^ 32) →
      S.regs 8 = BitVec.ofNat 64 xs.length →
      ReachesRet Extracted.program (s.regs 30) S (EPost (psum xs xs.length) s) := by
  intro m
  induction m with
  | zero =>
    intro i S hm hlt hpc hk h0 h1 h2 h3 h8r
    have hi : i = 7 := by omega
    subst hi
    have hlen := hp.len
    have htop := hp.top
    obtain ⟨hab, hacc, hrd⟩ := stack_arg xs s hp 7 (by omega) hlt
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hab hacc hrd
    have hsp := hk.sp; have hm' := hk.mem
    have hc := cnt_succ 7 (by omega)
    have hsum := (psum_succ xs 7 hlt).symm
    janus_run [hrd, hc, hsum] until [entry + 0x80, entry + 0xb0]
    · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
      refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
      simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, show 8 = xs.length by omega]
    · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
      refine stack_phase xs s hp (xs.length - 8) 8 _ false (by omega) (by omega) (by omega) rfl
        (by kept_tac hk) ?_ ?_ ?_ ?_
      all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h2, h8r, Nat.sub_self,
        Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | succ m ih =>
    intro i S hm hlt hpc hk h0 h1 h2 h3 h8r
    have hlen := hp.len
    have htop := hp.top
    have hb := hp.b
    have hsave := M_save s hb i (by omega)
    have harg := hp.args i hlt
    have hif : intLoc ⟨1, 0, 0⟩ i = .gpr (i + 1) := by
      simp only [intLoc]; rw [if_pos (by omega), Nat.add_comm]
    rw [hif, pieceAt_gpr_word] at harg
    rw [harg] at hsave
    have hsp := hk.sp; have hm' := hk.mem
    have hc := cnt_succ i (by omega)
    have hsum := (psum_succ xs i hlt).symm
    have hfacc : (M s).accessible (s.sp.toNat - 128) 128 true = true := by
      rw [M_acc s hb]; exact hp.acc
    have ih' := fun S => ih (i + 1) S (by omega)
    clear ih
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
        Nat.add_zero, Nat.mul_zero, Nat.sub_zero] at h3 hsave hc hsum hlt h1 h0 ih'
      janus_run [hsave, hc, hsum, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq,
        BitVec.msb_eq_decide, addSub_zero_snd] until [entry + 0x5c, entry + 0xb0]
      · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
        refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
        simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]
        exact congrArg (psum xs) (by omega)
      · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hbr
        refine ih' _ (by omega) rfl (by kept_tac hk) ?_ ?_ ?_ ?_ ?_
        all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h2, h8r]
        all_goals decide

set_option maxHeartbeats 4000000 in
/-- The callee contract of `k_vsum`. -/
theorem summary (xs : List (BitVec 64)) :
    Summary Extracted.program entry (VPre xs) (EPost (psum xs xs.length)) := by
  intro s hpc hp
  have hal := hp.al; have hb := hp.b; have htop := hp.top; have hacc := hp.acc
  have hga := hp.ga; have hgb := hp.gb; have hGa := hp.Ga; have hGb := hp.Gb
  have hgo := hp.go; have hGo := hp.Go; have hn := hp.n; have hlen := hp.len
  janus_eval_nat h_got : got
  rw [h_got] at hga hgb hGa hGb hgo hGo
  have h8 : BitVec.setWidth 64 (BitVec.setWidth 32 (s.regs 0)) = BitVec.ofNat 64 xs.length := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  janus_run [h8] until [entry + 0x5c, entry + 0xb0]
  · refine epilogue xs s hp _ _ rfl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
    · simp only [M, h_got]
    · have hk0 : xs.length = 0 := by
        simp [addSub_zero_snd, BitVec.msb_eq_decide] at hbr; omega
      simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, psum, hk0, List.take_zero,
        List.map_nil, List.sum_nil]
  · have hk0 : 0 < xs.length := by
      simp [addSub_zero_snd, BitVec.msb_eq_decide] at hbr; omega
    refine reg_phase xs s hp 7 0 _ rfl hk0 rfl
      ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [M, h_got]
    all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h8]
    rfl


/-- `VPre` for the call `k_vsum(8, a, …, h)`, with the classification evaluated. -/
theorem vpre8_iff (a b c d e f g h : BitVec 64) (s : State) :
    VPre [a, b, c, d, e, f, g, h] s ↔
      (s.regs 0).toNat % 2 ^ 32 = 8 ∧ s.regs 1 = a ∧ s.regs 2 = b ∧ s.regs 3 = c ∧ s.regs 4 = d ∧
      s.regs 5 = e ∧ s.regs 6 = f ∧ s.regs 7 = g ∧
      (s.sp.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible s.sp.toNat 8 false = true ∧
        s.mem.readLE s.sp.toNat 8 = h.toNat) ∧
      s.sp.toNat % 16 = 0 ∧ 128 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat - 128) 128 true = true ∧
      s.mem.accessible got 8 false = true ∧ got + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.mem.readLE got 8) 8 false = true ∧ s.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧
      (got + 8 ≤ s.sp.toNat - 128 ∨ s.sp.toNat ≤ got) ∧
      (s.mem.readLE got 8 + 8 ≤ s.sp.toNat - 128 ∨ s.sp.toNat ≤ s.mem.readLE got 8) ∧
      (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 := by
  have hloc : ∀ i, i < 7 → intLoc ⟨1, 0, 0⟩ i = .gpr (i + 1) := by
    intro i hi; simp only [intLoc]; rw [if_pos (by omega), Nat.add_comm]
  have hloc7 : intLoc ⟨1, 0, 0⟩ 7 = .stack 0 := by decide
  constructor
  · intro hp
    have ha := hp.args
    have h0 := ha 0 (by simp); have h1 := ha 1 (by simp); have h2 := ha 2 (by simp)
    have h3 := ha 3 (by simp); have h4 := ha 4 (by simp); have h5 := ha 5 (by simp)
    have h6 := ha 6 (by simp); have h7 := ha 7 (by simp)
    rw [hloc 0 (by omega), pieceAt_gpr_word] at h0
    rw [hloc 1 (by omega), pieceAt_gpr_word] at h1
    rw [hloc 2 (by omega), pieceAt_gpr_word] at h2
    rw [hloc 3 (by omega), pieceAt_gpr_word] at h3
    rw [hloc 4 (by omega), pieceAt_gpr_word] at h4
    rw [hloc 5 (by omega), pieceAt_gpr_word] at h5
    rw [hloc 6 (by omega), pieceAt_gpr_word] at h6
    rw [hloc7, pieceAt_stack_word] at h7
    simp only [Nat.add_zero] at h7
    exact ⟨hp.n, h0, h1, h2, h3, h4, h5, h6, h7, hp.al, hp.b, hp.top, hp.acc, hp.ga, hp.gb, hp.Ga,
      hp.Gb, hp.go, hp.Go, hp.lra, hp.lrb⟩
  · rintro ⟨hn, h0, h1, h2, h3, h4, h5, h6, h7, hal, hb, htop, hacc, hga, hgb, hGa, hGb, hgo, hGo,
      hlra, hlrb⟩
    refine ⟨hn, by simp, ?_, hal, hb, htop, hacc, hga, hgb, hGa, hGb, hgo, hGo, hlra, hlrb⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [hloc _ (by omega), pieceAt_gpr_word]; assumption)
      | (rw [hloc7, pieceAt_stack_word]; simpa using h7)

/-! ## `k_vsum8` and the cgo wrapper -/

abbrev kv8 : Nat := segAddr Extracted.program "k_vsum8"
abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_vsum8"

/-- The cgo frame at `a`: `p0`–`p7` at `a + 8k`, the result at `a + 64`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)

/-- The eight arguments read from the frame. -/
def args (m : Memory) (a : Nat) : List (BitVec 64) :=
  [fw m a 0, fw m a 1, fw m a 2, fw m a 3, fw m a 4, fw m a 5, fw m a 6, fw m a 7]

def res (m : Memory) (a : Nat) : Nat := (psum (args m a) 8).toNat

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 0 ∧ a.toNat + 72 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 72 true = true ∧
    (a.toNat + 72 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ a.toNat) ∧
    got + 8 ≤ 2 ^ 48 ∧ t.mem.accessible got 8 false = true ∧
    (got + 8 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ got) ∧
    t.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ t.mem.accessible (t.mem.readLE got 8) 8 false = true ∧
    (t.mem.readLE got 8 + 8 ≤ t.sp.toNat - 4096 ∨ t.sp.toNat ≤ t.mem.readLE got 8)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 64) 8 (res t.mem a.toNat)) t'.mem
    [(t.sp.toNat - 4096, t.sp.toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hgb, hga, hgo, hGb, hGa, hGo⟩
  apply ReturnsC.of_reaches
  janus_intro hs.call
  simp only [Nat.add_zero] at htop hacc
  janus_eval_nat h_got : got
  rw [h_got] at hgb hga hgo hGb hGa hGo
  janus_run
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₁ ⟨-, f₁, m₁, rfl, hm₁⟩
  have h48 : (t.sp - 48#64).toNat = t.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h80 : (t.sp - 48#64 - 32#64).toNat = t.sp.toNat - 80 := by
    rw [BitVec.toNat_sub, h48]; simp only [BitVec.toNat_ofNat]; omega
  apply ReturnsC.of_reaches
  janus_run [vpre8_iff, fw, BitVec.toNat_ofNat, h48, h80, h_got] until [kv8 + 0x34]
    calls [summary [fw t.mem a.toNat 0, fw t.mem a.toNat 1, fw t.mem a.toNat 2, fw t.mem a.toNat 3,
      fw t.mem a.toNat 4, fw t.mem a.toNat 5, fw t.mem a.toNat 6, fw t.mem a.toNat 7]]
  dsimp only at *
  obtain ⟨regs', sp', pc', fl', mem', dz', vr', tp', fc', fsr', ex, ep⟩ := s'
  dsimp only at *
  subst sp' pc' fc' vr' hex hep
  simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff] at *
  have h19' : regs' 19 = a := by assumption
  have h20' : regs' 20 = t.regs 20 := by assumption
  have h21' : regs' 21 = T := by assumption
  have h29' : regs' 29 = t.sp - 64#64 := by assumption
  have h0' : regs' 0 = psum (args t.mem a.toNat) 8 := by simp only [args]; assumption
  janus_run [h19', h20', h21', h29', h48, h80]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [CStack]; janus_simp [h48]
    refine ⟨by omega, by omega, by omega, ?_⟩
    janus_disch
  rintro s₂ ⟨-, f₂, m₂, rfl, hm₂⟩
  dsimp only at hm₁ hm₂
  apply ReturnsC.of_reaches
  janus_run [h19', h20', h21', h29', h48, h80, h0']
  refine ⟨?_, ?_⟩
  · repeat' (apply And.intro)
    all_goals assumption
  simp only [WPost, res, writeLE_mod_8, Nat.reducePow]
  have hT : (18446744073709551616 - T.toNat + T.toNat) % 18446744073709551616 = 0 := by
    have := T.isLt; omega
  simp only [hT, Nat.add_zero]
  obtain ⟨M, hmv, hM⟩ : ∃ M, MemFrame M mem' [(t.sp.toNat - 80 - 128, t.sp.toNat - 80)] ∧
      MemFrame m₁ M [(t.sp.toNat - 4096, t.sp.toNat)] := ⟨_, by assumption, by janus_frame⟩
  have hf : MemFrame t.mem m₂ [(t.sp.toNat - 4096, t.sp.toNat)] := by
    refine MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
      (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
        (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)])
          (MemFrame.trans (rs := [(t.sp.toNat - 4096, t.sp.toNat)]) ?_ hm₁ ?_) hM ?_) hmv ?_) hm₂ ?_
    all_goals first
      | janus_frame
      | (intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  exact hf.writeLE_both _ _ _

/-! ## The Go side: `VSum8` → `_Cfunc_k_vsum8` → `runtime.cgocall` -/

def fnVar : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" + 0x24)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" 9)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" 10) 3

def alwaysFalse : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" + 0x30)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" 12)
    (segWord Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" 13) 0

/-- At the `cgocall`: the 72-byte frame, the GOT slot and the guard are Go memory the runtime
leaves alone. -/
def G (s : State) : Prop :=
  (s.regs 1).toNat + 72 ≤ 2 ^ 48 ∧ GoKept s (s.regs 1).toNat 72 true ∧
    got + 8 ≤ 2 ^ 48 ∧ GoKept s got 8 false ∧
    s.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ GoKept s (s.mem.readLE got 8) 8 false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 1).toNat + 64) 8 (res s.mem (s.regs 1).toNat)

def GoPre (s : State) : Prop :=
  GuardOK s 96 ∧ StackOK s 160 0 ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 % 2 = 0 ∧
  got + 8 ≤ 2 ^ 48 ∧ s.mem.accessible got 8 false = true ∧
  s.mem.readLE got 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.mem.readLE got 8) 8 false = true ∧
  Outside (s.regs 28).toNat 456 [(s.sp.toNat - 160, s.sp.toNat)] ∧
  Outside (s.tpidr.toNat + 16) 8 [(s.sp.toNat - 160, s.sp.toNat)] ∧
  Outside fnVar 8 [(s.sp.toNat - 160, s.sp.toNat)] ∧
  Outside alwaysFalse 1 [(s.sp.toNat - 1168, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside got 8 [(s.sp.toNat - 1168, s.sp.toNat), ((s.regs 28).toNat, (s.regs 28).toNat + 456),
    (s.tpidr.toNat + 16, s.tpidr.toNat + 24)] ∧
  Outside (s.mem.readLE got 8) 8 [(s.sp.toNat - 1168, s.sp.toNat),
    ((s.regs 28).toNat, (s.regs 28).toNat + 456), (s.tpidr.toNat + 16, s.tpidr.toNat + 24)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a b c d e f g h : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [a, b, c, d, e, f, g, h] GoPre
      (fun _ s' => s'.regs 0 = psum [a, b, c, d, e, f, g, h] 8) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, htop, hst⟩, hfa, hfv, haa, hav, hgb, hga, hGb, hGa,
    hdg, hdt, hdf, hda, hdgot, hdG⟩
  apply ReturnsC.of_reaches
  janus_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  janus_eval_nat h_got : got
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  rw [h_got] at hgb hga hGb hGa hdgot hdG
  simp only [outside_cons, outside_nil, and_true, Nat.add_zero] at *
  have h88 : (s.sp - 88#64).toNat = s.sp.toNat - 88 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus_simp [hfv]
  · simp only [G, GoKept, cgoClobber, GoABI.regG, cgoStackScratch, gStructSize, tlsGOffset,
      outside_cons, outside_nil, and_true, h_got]
    janus_simp [h88, h144]
    repeat' (apply And.intro)
    all_goals first | omega | janus_disch | assumption
  rintro s' ⟨-, m, ⟨regs, fl, vr, tp, fs', rfl, hg, hfp⟩, hmf⟩
  simp only [E, res, args, fw, cgoClobber, GoABI.regG, GoABI.regFP, cgoStackScratch, gStructSize,
    tlsGOffset, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h88, h144] at hmf hg hfp
  apply ReturnsC.of_reaches
  janus_run [hg, hfp]

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hgb, ⟨hga, hgout⟩, hGb, ⟨hGa, hGout⟩⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hgsep := he.stackSep _ _ _ hga
    have hGsep := he.stackSep _ _ _ hGa
    have hk := he.kept got 8 ⟨hga, hgout⟩
    simp only [outside_cons, outside_nil, and_true, cgoCStack] at hsep hgsep hGsep
    refine ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hgb, he.keptAcc _ _ _ ⟨hga, hgout⟩,
      by omega, ?_, ?_, ?_⟩ <;> rw [hk]
    · exact hGb
    · exact he.keptAcc _ _ _ ⟨hGa, hGout⟩
    · omega
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, _⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by simpa [cgoCStack] using hsep)
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 1).toNat ≤ c → c + n ≤ (s.regs 1).toNat + 72 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, args, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 1).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 1).toNat + 8) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 16) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 24) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 32) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 40) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 48) 8 (by omega) (by omega),
        hk ((s.regs 1).toNat + 56) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`VSum8` end to end**, under the trusted `CgoCall` contract only: the variadic C sum. -/
theorem correctness (a b c d e f g h : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [a, b, c, d, e, f, g, h] GoPre
      (fun _ s' => s'.regs 0 = psum [a, b, c, d, e, f, g, h] 8) :=
  (go_spec a b c d e f g h).refine refines

end Proof

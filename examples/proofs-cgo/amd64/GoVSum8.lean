import Extracted

/-!
# `VSum8(a, …, h int64) int64` (Go) → `k_vsum8` (C) → `k_vsum(8, a, …, h)` (C, variadic) → back to
# Go, end to end (amd64)

```go
func VSum8(a, b, c, d, e, f, g, h int64) int64 { return int64(C.k_vsum8(C.int64_t(a), …, C.int64_t(h))) }
```
```c
int64_t k_vsum8(int64_t a, …, int64_t h) { return k_vsum(8, a, b, c, d, e, f, g, h); }
```

**Guarantee (`correctness`).** For all 64-bit `a … h`, every Go call of
`example.com/cgo/cabi.VSum8` with `a … h` in `RAX RBX RCX RDI RSI R8 R9 R10` (Go's ABIInternal)
satisfying `GoPre` (stack checks, 128 bytes of Go stack, the cgo globals as statically
initialised, the stack-protector guard at `FS:0x28` readable away from the stacks) returns,
restores `RSP`, `RBP`, `R14`, and leaves `a + b + … + h` (mod 2^64) in `RAX`, under the trusted
`CgoCall` contract only.

**How.** The wrapper calls `k_vsum8` with its eight arguments where the classification of
`int64_t (int64_t ×8)` puts them (six in `RDI RSI RDX RCX R8 R9`, `g`, `h` pushed in the argument
area). `k_vsum8` makes the variadic call `k_vsum(8, a, …, h)`: `n` in `EDI`, `a`–`e` in
`RSI RDX RCX R8 R9`, `f g h` in the argument area, and `AL = 0` vector registers, which is where
the System V classification of the variadic call puts them. The callee contract of `k_vsum` (as in
`KVSum.lean`, proved for every argument count) states its precondition in terms of the
classification (`VPre.args`: `PieceAt … (intLoc …)`, `VPre.al`: `VarargAL`); `vpre8_iff`
evaluates it for eight arguments, and `janus64_run` proves it at `k_vsum8`'s call site.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C Janus.Spec
  Janus.Amd64.FFI

namespace Proof

/-! ## The variadic C function `k_vsum` (as in `KVSum.lean`), as a callee summary -/

abbrev entry : Nat := segAddr Extracted.program "k_vsum"

def sig (xs : List (BitVec 64)) : SysV.Sig :=
  ⟨some (.int 8 true), .int 4 true :: xs.map fun _ => .int 8 true, some 1⟩

theorem assign_n : SysV.assign {} (.int 4 true) = (.direct [⟨0, 4, .gpr 7⟩], ⟨1, 0, 0⟩) := by
  decide

/-- The sum of the first `i` words, mod 2^64. -/
def psum (xs : List (BitVec 64)) (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((xs.take i).map BitVec.toNat).sum

theorem psum_succ (xs : List (BitVec 64)) (i : Nat) (hi : i < xs.length) :
    psum xs (i + 1) = psum xs i + xs[i] := by
  apply BitVec.eq_of_toNat_eq
  simp only [psum, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- What `k_vsum` needs at its entry. -/
structure VPre (xs : List (BitVec 64)) (s : State) : Prop where
  n : (s.regs 7).toNat % 2 ^ 32 = xs.length
  len : xs.length < 2 ^ 31
  args : ∀ i (hi : i < xs.length), PieceAt s xs[i].toNat ⟨0, 8, intLoc ⟨1, 0, 0⟩ i⟩
  b : 96 ≤ (s.regs 4).toNat
  top : (s.regs 4).toNat + 8 ≤ 2 ^ 48
  acc : s.mem.accessible ((s.regs 4).toNat - 88) 96 true = true
  ca : s.mem.accessible (s.fsBase.toNat + 40) 8 false = true
  cb : s.fsBase.toNat + 48 ≤ 2 ^ 48
  co : s.fsBase.toNat + 48 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat ≤ s.fsBase.toNat + 40
  ra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  df : s.df = false
  /-- `AL` bounds the vector registers used (System V variadic call; `k_vsum` does not read it:
  its prologue saves no `XMM` register). -/
  al : VarargAL s (sig xs)

/-- What `k_vsum` guarantees. -/
abbrev EPost (acc : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.fpucw = s.fpucw ∧
    s'.xmm = s.xmm ∧ MemFrame s.mem s'.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat)] ∧
    s'.regs 0 = acc

/-- The frame after the prologue. -/
def M (s : State) : Memory :=
  ((((((((s.mem.writeLE ((s.regs 4).toNat - 48) 8 (s.regs 6).toNat).writeLE
    ((s.regs 4).toNat - 40) 8 (s.regs 2).toNat).writeLE
    ((s.regs 4).toNat - 32) 8 (s.regs 1).toNat).writeLE
    ((s.regs 4).toNat - 24) 8 (s.regs 8).toNat).writeLE
    ((s.regs 4).toNat - 16) 8 (s.regs 9).toNat).writeLE
    ((s.regs 4).toNat - 64) 8 (s.mem.readLE (s.fsBase.toNat + 40) 8)).writeLE
    ((s.regs 4).toNat - 88) 4 8).writeLE
    ((s.regs 4).toNat - 80) 8 ((s.regs 4).toNat + 8)).writeLE
    ((s.regs 4).toNat - 72) 8 ((s.regs 4).toNat - 56)

theorem M_frame (s : State) (hb : 96 ≤ (s.regs 4).toNat) :
    MemFrame s.mem (M s) [((s.regs 4).toNat - 88, (s.regs 4).toNat)] := by
  unfold M; janus_frame

theorem M_acc (s : State) (a n : Nat) (w : Bool) :
    (M s).accessible a n w = s.mem.accessible a n w := by
  unfold M; simp only [Janus.Arm64.Memory.accessible_writeLE]

theorem M_out (s : State) (hb : 96 ≤ (s.regs 4).toNat) (a n : Nat)
    (h : a + n ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat ≤ a) : (M s).readLE a n = s.mem.readLE a n :=
  (M_frame s hb).readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)

/-- The general-register save area: argument register `i + 1` at `RSP - (48 - 8i)`. -/
theorem M_save (s : State) (hb : 96 ≤ (s.regs 4).toNat) (i : Nat) (hi : i < 5) :
    (M s).readLE ((s.regs 4).toNat - (48 - 8 * i)) 8 = (s.regs (CABI.argReg (i + 1))).toNat := by
  have h := fun (r : Nat) => (s.regs r).isLt
  unfold M
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Nat.mul_zero, Nat.sub_zero, Nat.reduceMul,
    Nat.reduceSub, Nat.reducePow, CABI.argReg, CABI.intArgRegs, Nat.reduceAdd] <;>
  exact Nat.mod_eq_of_lt (h _)

theorem M_canary (s : State) (hb : 96 ≤ (s.regs 4).toNat) :
    (M s).readLE ((s.regs 4).toNat - 64) 8 = s.mem.readLE (s.fsBase.toNat + 40) 8 := by
  unfold M
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  exact Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)

/-- `S` agrees with the state after the prologue on everything the rest keeps. -/
structure Kept (s S : State) : Prop where
  sp : S.regs 4 = s.regs 4 - 88#64
  mem : S.mem = M s
  r3 : S.regs 3 = s.regs 3
  r5 : S.regs 5 = s.regs 5
  r7 : S.regs 7 = s.regs 7
  r12 : S.regs 12 = s.regs 12
  r13 : S.regs 13 = s.regs 13
  r14 : S.regs 14 = s.regs 14
  r15 : S.regs 15 = s.regs 15
  df : S.df = false
  mxcsr : S.mxcsr = s.mxcsr
  fpucw : S.fpucw = s.fpucw
  xmm : S.xmm = s.xmm
  fs : S.fsBase = s.fsBase

macro "kept_tac" hk:term : tactic => `(tactic|
  (constructor <;> simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, ($hk).sp, ($hk).mem,
    ($hk).r3, ($hk).r5, ($hk).r7, ($hk).r12, ($hk).r13, ($hk).r14, ($hk).r15, ($hk).df,
    ($hk).mxcsr, ($hk).fpucw, ($hk).xmm, ($hk).fs]))

set_option maxHeartbeats 4000000 in
/-- The epilogue (`k_vsum+0x86`): the canary check passes, the frame is popped, `RDX` returned. -/
theorem epilogue (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) (S : State) (acc : BitVec 64)
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x86)) (hk : Kept s S) (h2 : S.regs 2 = acc) :
    ReachesRet Extracted.program (retAddrOf s) S (EPost acc s) := by
  obtain ⟨hsp, hm, h3, h5, h7, h12, h13, h14, h15, hdf, hmx, hfw, hx, hfs⟩ := hk
  have hb := hp.b; have htop := hp.top; have hacc := hp.acc; have hca := hp.ca; have hcb := hp.cb
  have hco := hp.co; have hra := hp.ra
  have hcan := M_canary s hb
  have hcan' : (M s).readLE ((s.regs 4).toNat - 88 + 24) 8 = s.mem.readLE (s.fsBase.toNat + 40) 8 := by
    rw [show (s.regs 4).toNat - 88 + 24 = (s.regs 4).toNat - 64 by omega]; exact hcan
  have hret := M_out s hb (s.regs 4).toNat 8 (Or.inr (Nat.le_refl _))
  rw [← M_acc s] at hacc hca
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hfsM := M_out s hb (s.fsBase.toNat + 40) 8 (by omega)
  janus64_run [hcan, hcan', hret, h88, hfs, hfsM]
  simp only [EPost, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h3, h5, h12, h13, h14, h15, hfw, hx,
    true_and, and_true]
  exact ⟨rfl, M_frame s hb⟩

/-- The stacked variadic argument `xs[i]` (`i ≥ 5`), read in the frame memory. -/
theorem stack_arg (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) (i : Nat) (h5 : 5 ≤ i)
    (hi : i < xs.length) :
    (s.regs 4).toNat + 8 + 8 * (i - 5) + 8 ≤ 2 ^ 48 ∧
      (M s).accessible ((s.regs 4).toNat + 8 + 8 * (i - 5)) 8 false = true ∧
      (M s).readLE ((s.regs 4).toNat + 8 + 8 * (i - 5)) 8 = xs[i].toNat := by
  have h := hp.args i hi
  rw [intLoc_stack _ _ (by simp; omega)] at h
  simp only [Nat.zero_add, show 1 + i - 6 = i - 5 by omega] at h
  rw [pieceAt_stack_word] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [CABI.regSP] at h1 h2 h3
  refine ⟨h1, by rw [M_acc s]; exact h2, ?_⟩
  rw [M_out s hp.b _ _ (Or.inr (by omega))]; exact h3

/-- `ADD $c, %eax` on the loop counter. -/
theorem cnt_add (x c : Nat) (h : x + c < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x) + BitVec.ofNat 32 c) =
      BitVec.ofNat 64 (x + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `CMP $c, %edi`-style comparison with a 32-bit literal. -/
theorem cnt_cmp32 (s : State) (k x : Nat) (hn : (s.regs 7).toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31)
    (hx : x < 2 ^ 32) :
    (BitVec.setWidth 32 (s.regs 7) - BitVec.ofNat 32 x = 0#32) = (k = x) := by
  apply propext
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

/-- A 32-bit counter, zero-extended. -/
theorem cnt_zext (x : Nat) (h : x < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `CMP %eax, %edi` of the loop: `EDI = n`. -/
theorem cnt_cmp (s : State) (k x : Nat) (hn : (s.regs 7).toNat % 2 ^ 32 = k) (hk : k < 2 ^ 31)
    (hx : x < 2 ^ 32) :
    (BitVec.setWidth 32 (s.regs 7) - BitVec.setWidth 32 (BitVec.ofNat 64 x) = 0#32) = (k = x) := by
  apply propext
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

set_option maxHeartbeats 4000000 in
/-- The loop over the argument area (`k_vsum+0xa8`, two arguments per iteration), after `d ≥ 6`
arguments: by induction on the arguments left. -/
theorem over_phase (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) :
    ∀ m d (S : State), d + m = xs.length → 6 ≤ d → d < xs.length →
      S.rip = BitVec.ofNat 64 (entry + 0xa8) → Kept s S →
      S.regs 2 = psum xs d → S.regs 0 = BitVec.ofNat 64 (d - 1) →
      S.regs 1 = BitVec.ofNat 64 ((s.regs 4).toNat + 8 + 8 * (d - 6)) →
      ReachesRet Extracted.program (retAddrOf s) S (EPost (psum xs xs.length) s) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro d S hm h6 hlt hpc hk h2 h0 h1
  have hlen := hp.len; have htop := hp.top; have hn := hp.n; have hb := hp.b
  obtain ⟨hab, hacc, hrd⟩ := stack_arg xs s hp d (by omega) hlt
  have hsp := hk.sp; have hm' := hk.mem; have h7 := hk.r7
  have e1 : (s.regs 4).toNat + 8 + 8 * (d - 6) + 8 = (s.regs 4).toNat + 8 + 8 * (d - 5) := by omega
  rw [← e1] at hab hacc hrd
  have hc2 := cnt_add (d - 1) 2 (by omega)
  have hc3 := cnt_add (d - 1 + 2) 1 (by omega)
  have hq1 := cnt_cmp s xs.length (d - 1 + 2) hn hlen (by omega)
  have hq2 := cnt_cmp s xs.length (d - 1 + 2 + 1) hn hlen (by omega)
  have hz := cnt_zext (d - 1 + 2 + 1) (by omega)
  by_cases hd1 : d + 1 < xs.length
  · obtain ⟨hab', hacc', hrd'⟩ := stack_arg xs s hp (d + 1) (by omega) hd1
    have e2 : (s.regs 4).toNat + 8 + 8 * (d - 6) + 16 = (s.regs 4).toNat + 8 + 8 * (d + 1 - 5) := by
      omega
    rw [← e2] at hab' hacc' hrd'
    have hs1 := (psum_succ xs d hlt).symm
    have hs2 := (psum_succ xs (d + 1) hd1).symm
    janus64_run [hrd, hrd', hc2, hc3, hz, hq1, hq2, BitVec.ofNat_toNat, BitVec.setWidth_eq, hs1, hs2]
      until [entry + 0x86, entry + 0xa8]
    · refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      exact congrArg (psum xs) (by omega)
    · refine ih (m - 2) (by omega) (d + 2) _ (by omega) (by omega) (by omega) rfl (by kept_tac hk)
        ?_ ?_ ?_
      all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      · exact congrArg (BitVec.ofNat 64) (by omega)
      · apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
  · have hs1 := (psum_succ xs d hlt).symm
    janus64_run [hrd, hc2, hc3, hz, hq1, hq2, BitVec.ofNat_toNat, BitVec.setWidth_eq, hs1]
      until [entry + 0x86, entry + 0xa8]
    refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
    exact congrArg (psum xs) (by omega)

set_option maxHeartbeats 8000000 in
/-- The loop while `gp_offset ≤ 40` (`k_vsum+0x70`), after `i ≤ 5` arguments: `va_arg` reads the
saved argument register `i + 1`; at `i = 5` it moves on to the argument area. -/
theorem reg_phase (xs : List (BitVec 64)) (s : State) (hp : VPre xs s) :
    ∀ m i (S : State), i + m = 5 → i < xs.length →
      S.rip = BitVec.ofNat 64 (entry + 0x70) → Kept s S →
      S.regs 2 = psum xs i → S.regs 0 = BitVec.ofNat 64 i → S.regs 6 = BitVec.ofNat 64 (8 + 8 * i) →
      S.regs 9 = s.regs 4 - 56#64 → S.regs 1 = s.regs 4 + 8#64 →
      ReachesRet Extracted.program (retAddrOf s) S (EPost (psum xs xs.length) s) := by
  intro m
  induction m with
  | zero =>
    intro i S hm hlt hpc hk h2 h0 h6 h9 h1
    have hi : i = 5 := by omega
    subst hi
    have hlen := hp.len; have htop := hp.top; have hn := hp.n; have hb := hp.b
    obtain ⟨hab, hacc, hrd⟩ := stack_arg xs s hp 5 (by omega) hlt
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hab hacc hrd
    have hsp := hk.sp; have hm' := hk.mem; have h7 := hk.r7
    have hq := cnt_cmp32 s xs.length 6 hn hlen (by omega)
    have hs1 := (psum_succ xs 5 hlt).symm
    have h8 : (s.regs 4 + 8#64).toNat = (s.regs 4).toNat + 8 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    janus64_run [hrd, hq, hs1, h8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      until [entry + 0x86, entry + 0xa8]
    · refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
      exact congrArg (psum xs) (by omega)
    · refine over_phase xs s hp (xs.length - 6) 6 _ (by omega) (by omega) (by omega) rfl
        (by kept_tac hk) ?_ ?_ ?_
      all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h0, h1]
      all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; try omega)
  | succ m ih =>
    intro i S hm hlt hpc hk h2 h0 h6 h9 h1
    have hlen := hp.len; have htop := hp.top; have hn := hp.n; have hb := hp.b
    have hsp := hk.sp; have hm' := hk.mem; have h7 := hk.r7
    have harg := hp.args i hlt
    have hif : intLoc ⟨1, 0, 0⟩ i = .gpr (CABI.argReg (i + 1)) := by
      simp only [intLoc]; rw [if_pos (by omega), Nat.add_comm]
    rw [hif, pieceAt_gpr_word] at harg
    have hsave := M_save s hb i (by omega)
    rw [harg] at hsave
    have hsave' : (M s).readLE ((s.regs 4).toNat - 56 + (8 + 8 * i)) 8 = xs[i].toNat := by
      rw [show (s.regs 4).toNat - 56 + (8 + 8 * i) = (s.regs 4).toNat - (48 - 8 * i) by omega]
      exact hsave
    have hacc' : (M s).accessible ((s.regs 4).toNat - 88) 96 true = true := by
      rw [M_acc]; exact hp.acc
    have h56 : (s.regs 4 - 56#64).toNat = (s.regs 4).toNat - 56 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have hq := cnt_cmp s xs.length (i + 1) hn hlen (by omega)
    have hs1 := (psum_succ xs i hlt).symm
    have ih' := fun S => ih (i + 1) S (by omega)
    clear ih
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with
      rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at h0 h6 hsave' hq hs1 ih' h2
      janus64_run [hsave', hq, hs1, h56, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        until [entry + 0x86, entry + 0x70]
      · rw [cnt_cmp32 s xs.length _ hn hlen (by decide)] at hbr
        refine epilogue xs s hp _ _ rfl (by kept_tac hk) ?_
        simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]
        exact congrArg (psum xs) (by omega)
      · rw [cnt_cmp32 s xs.length _ hn hlen (by decide)] at hbr
        refine ih' _ (by omega) rfl (by kept_tac hk) ?_ ?_ ?_ ?_ ?_
        all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h9, h1]
        all_goals rfl

set_option maxHeartbeats 4000000 in
/-- The callee contract of `k_vsum`. -/
theorem summary (xs : List (BitVec 64)) :
    Summary Extracted.program entry (VPre xs) (EPost (psum xs xs.length)) := by
  intro s hpc hp
  have hb := hp.b; have htop := hp.top; have hacc := hp.acc; have hn := hp.n; have hlen := hp.len
  have hca := hp.ca; have hcb := hp.cb; have hco := hp.co; have hra := hp.ra; have hdf := hp.df
  have hw : (BitVec.setWidth 32 (s.regs 7)).toNat = xs.length := by
    rw [BitVec.toNat_setWidth]; exact hn
  have hle : (BitVec.setWidth 32 (s.regs 7) = 0#32 ∨ (BitVec.setWidth 32 (s.regs 7)).msb = true) ↔
      xs.length = 0 := by
    rw [BitVec.msb_eq_decide, hw]
    constructor
    · rintro (h | h)
      · have := congrArg BitVec.toNat h; rw [hw] at this; simpa using this
      · simp at h; omega
    · intro h; left; apply BitVec.eq_of_toNat_eq; rw [hw, h]; rfl
  janus64_run until [entry + 0x86, entry + 0x70]
  · rw [hle] at hbr
    refine epilogue xs s hp _ _ rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by first | rfl | exact hdf, rfl, rfl, rfl, rfl⟩ ?_
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, psum, hbr, List.take_zero, List.map_nil,
      List.sum_nil]
  · rw [hle] at hbr
    refine reg_phase xs s hp 5 0 _ rfl (by omega) rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by first | rfl | exact hdf, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, psum, List.take_zero,
      List.map_nil, List.sum_nil]




/-- `VPre` for the call `k_vsum(8, a, …, h)`, with the classification evaluated. -/
theorem vpre8_iff (a b c d e f g h : BitVec 64) (s : State) :
    VPre [a, b, c, d, e, f, g, h] s ↔
      (s.regs 7).toNat % 2 ^ 32 = 8 ∧ s.regs 6 = a ∧ s.regs 2 = b ∧ s.regs 1 = c ∧ s.regs 8 = d ∧
      s.regs 9 = e ∧
      ((s.regs 4).toNat + 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 8) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 8) 8 = f.toNat) ∧
      ((s.regs 4).toNat + 16 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 16) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 16) 8 = g.toNat) ∧
      ((s.regs 4).toNat + 24 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 24) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 24) 8 = h.toNat) ∧
      96 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible ((s.regs 4).toNat - 88) 96 true = true ∧
      s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧ s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧
      (s.fsBase.toNat + 48 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat ≤ s.fsBase.toNat + 40) ∧
      s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false ∧ (s.regs 0).toNat % 256 ≤ 8 := by
  have hloc0 : intLoc ⟨1, 0, 0⟩ 0 = .gpr 6 := by decide
  have hloc1 : intLoc ⟨1, 0, 0⟩ 1 = .gpr 2 := by decide
  have hloc2 : intLoc ⟨1, 0, 0⟩ 2 = .gpr 1 := by decide
  have hloc3 : intLoc ⟨1, 0, 0⟩ 3 = .gpr 8 := by decide
  have hloc4 : intLoc ⟨1, 0, 0⟩ 4 = .gpr 9 := by decide
  have hloc5 : intLoc ⟨1, 0, 0⟩ 5 = .stack 0 := by decide
  have hloc6 : intLoc ⟨1, 0, 0⟩ 6 = .stack 8 := by decide
  have hloc7 : intLoc ⟨1, 0, 0⟩ 7 = .stack 16 := by decide
  have hs8 : sig [a, b, c, d, e, f, g, h] = ⟨some (.int 8 true), [.int 4 true, .int 8 true,
      .int 8 true, .int 8 true, .int 8 true, .int 8 true, .int 8 true, .int 8 true, .int 8 true],
      some 1⟩ := rfl
  have hv : (sig [a, b, c, d, e, f, g, h]).vecRegs = 0 := by rw [hs8]; decide
  have hal : VarargAL s (sig [a, b, c, d, e, f, g, h]) ↔ (s.regs 0).toNat % 256 ≤ 8 := by
    simp only [VarargAL, hv, Nat.zero_le, true_and]
    exact ⟨fun h => h rfl, fun h _ => h⟩
  constructor
  · intro hp
    have ha := hp.args
    have h0 := ha 0 (by simp); have h1 := ha 1 (by simp); have h2 := ha 2 (by simp)
    have h3 := ha 3 (by simp); have h4 := ha 4 (by simp); have h5 := ha 5 (by simp)
    have h6 := ha 6 (by simp); have h7 := ha 7 (by simp)
    rw [hloc0, pieceAt_gpr_word] at h0
    rw [hloc1, pieceAt_gpr_word] at h1
    rw [hloc2, pieceAt_gpr_word] at h2
    rw [hloc3, pieceAt_gpr_word] at h3
    rw [hloc4, pieceAt_gpr_word] at h4
    rw [hloc5, pieceAt_stack_word] at h5
    rw [hloc6, pieceAt_stack_word] at h6
    rw [hloc7, pieceAt_stack_word] at h7
    simp only [Nat.add_zero, CABI.regSP, Nat.add_assoc, Nat.reduceAdd] at h5 h6 h7
    exact ⟨hp.n, h0, h1, h2, h3, h4, h5, h6, h7, hp.b, hp.top, hp.acc, hp.ca, hp.cb, hp.co, hp.ra,
      hp.df, hal.1 hp.al⟩
  · rintro ⟨hn, h0, h1, h2, h3, h4, h5, h6, h7, hb, htop, hacc, hca, hcb, hco, hra, hdf, hal'⟩
    refine ⟨hn, by simp, ?_, hb, htop, hacc, hca, hcb, hco, hra, hdf, hal.2 hal'⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hloc0, pieceAt_gpr_word]; exact h0
    · rw [hloc1, pieceAt_gpr_word]; exact h1
    · rw [hloc2, pieceAt_gpr_word]; exact h2
    · rw [hloc3, pieceAt_gpr_word]; exact h3
    · rw [hloc4, pieceAt_gpr_word]; exact h4
    · rw [hloc5, pieceAt_stack_word]; simpa [CABI.regSP] using h5
    · rw [hloc6, pieceAt_stack_word]; simpa [CABI.regSP, Nat.add_assoc] using h6
    · rw [hloc7, pieceAt_stack_word]; simpa [CABI.regSP, Nat.add_assoc] using h7

/-! ## `k_vsum8` and the cgo wrapper -/

abbrev kv8 : Nat := segAddr Extracted.program "k_vsum8"
abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_vsum8"

/-- The cgo frame at `a`: `p0`–`p7` at `a + 8k`, the result at `a + 64`. -/
def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)

/-- The eight arguments read from the frame. -/
def args (m : Memory) (a : Nat) : List (BitVec 64) :=
  [fw m a 0, fw m a 1, fw m a 2, fw m a 3, fw m a 4, fw m a 5, fw m a 6, fw m a 7]

def res (m : Memory) (a : Nat) : Nat := (psum (args m a) 8).toNat

/-- The wrapper's precondition: the cgo frame, and `k_vsum`'s stack-protector guard at
`FS:0x28` readable off the C stack. -/
def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 72 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 72 true = true ∧
    (a.toNat + 72 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat) ∧
    t.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ t.mem.accessible (t.fsBase.toNat + 40) 8 false = true ∧
    (t.fsBase.toNat + 48 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ t.fsBase.toNat + 40)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 64) 8 (res t.mem a.toNat)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd, hgb, hga, hgo⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP] at hal hb htop hacc hd hgo
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h96 : (t.regs 4 - 96#64).toNat = (t.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run [vpre8_iff, fw, BitVec.toNat_ofNat, h96] calls [summary [fw t.mem a.toNat 0,
    fw t.mem a.toNat 1, fw t.mem a.toNat 2, fw t.mem a.toNat 3, fw t.mem a.toNat 4,
    fw t.mem a.toNat 5, fw t.mem a.toNat 6, fw t.mem a.toNat 7]]
  have h48 : (t.regs 4 - 48#64).toNat = (t.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h48]; omega
  · janus64_simp [h48]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run [h48]
  refine ⟨by assumption, ?_⟩
  simp only [WPost, res, args, List.length_cons, List.length_nil, Nat.reduceAdd, fw, Nat.mul_zero,
    Nat.add_zero, Nat.reduceMul]
  obtain ⟨M, hmv, hM⟩ : ∃ M, MemFrame M s'.mem [((t.regs 4).toNat - 96 - 88, (t.regs 4).toNat - 96)] ∧
      MemFrame t.mem M [((t.regs 4).toNat - 4096, (t.regs 4).toNat)] := ⟨_, by assumption, by janus_frame⟩
  have hf : MemFrame t.mem s'.mem [((t.regs 4).toNat - 4096, (t.regs 4).toNat)] :=
    MemFrame.trans (rs'' := [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]) hM hmv
      (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  apply Janus.MemFrame.writeLE_both
  exact hf.writeLE _ (List.mem_singleton_self _) (by dsimp only; omega) (by dsimp only; omega)

/-! ## The Go side: `VSum8` → `_Cfunc_k_vsum8` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" + 0x2e)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_vsum8.abi0" + 0x47)

/-- At the `cgocall`: the 72-byte frame and the guard at `FS:0x28` are Go memory the runtime
leaves alone. -/
def G (s : State) : Prop :=
  (s.regs 3).toNat + 72 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 72 true ∧
    s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ GoKept s (s.fsBase.toNat + 40) 8 false

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 64) 8 (res s.mem (s.regs 3).toNat)

def GoPre (s : State) : Prop :=
  StackGuardOK s 88 ∧ StackWritable s 128 8 ∧ TlsG s ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 128, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 128, (s.regs 4).toNat + 8)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 128, (s.regs 4).toNat + 8)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1152, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - 1152, (s.regs 4).toNat + 8),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a b c d e f g h : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [a, b, c, d, e, f, g, h] GoPre
      (fun _ s' => s'.regs 0 = psum [a, b, c, d, e, f, g, h] 8) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hfa, hfv, haa, hav,
    hcb, hca, hdg, hdt, hdf, hda, hdc⟩
  apply ReturnsC.of_reaches
  janus64_intro hs
  janus_eval_nat h_fv : fnVar
  janus_eval_nat h_af : alwaysFalse
  rw [h_fv] at hfa hfv hdf
  rw [h_af] at haa hav hda
  simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    stackguard0, stackguard0Offset] at *
  have hfsa : (s.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s.fsBase.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h80 : (s.regs 4 - 80#64).toNat = (s.regs 4).toNat - 80 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h128 : (s.regs 4 - 128#64).toNat = (s.regs 4).toNat - 128 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h80, h128]
    repeat' (apply And.intro)
    all_goals first | omega | janus64_disch | assumption
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, _, mx, x87, zh, kr, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  rename_i fsb
  simp only [E, res, args, fw, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h80, h128] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fsb + BitVec.ofNat 64 18446744073709551608).toNat = fsb.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  have hr : m.readLE (s.regs 4).toNat 8 = ret := by
    rw [hmf.readLE (s.regs 4).toNat 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    janus64_simp [h_ret]
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg', hr]

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, ⟨hacc, hout⟩, hgb, ⟨hga, hgout⟩⟩ he
    have hsep := he.stackSep _ _ _ hacc
    have hgsep := he.stackSep _ _ _ hga
    simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep hgsep
    unfold WPre; rw [he.fs]
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega, hgb,
      he.keptAcc _ _ _ ⟨hga, hgout⟩, by omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, ⟨hacc, hout⟩, _⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 72 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, args, fw, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 3).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 24) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 32) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 40) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 48) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 56) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, ⟨hacc, hout⟩, _⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`VSum8` end to end**, under the trusted `CgoCall` contract only: the variadic C sum. -/
theorem correctness (a b c d e f g h : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [a, b, c, d, e, f, g, h] GoPre
      (fun _ s' => s'.regs 0 = psum [a, b, c, d, e, f, g, h] 8) :=
  (go_spec a b c d e f g h).refine refines

end Proof

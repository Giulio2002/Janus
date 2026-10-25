import Extracted

/-!
# `int64_t k_vsum(int n, ...)` (C, amd64): a variadic function, for every `n`

```c
int64_t k_vsum(int n, ...) {
	va_list ap; va_start(ap, n);
	int64_t s = 0;
	for (int i = 0; i < n; i++) s += va_arg(ap, int64_t);
	va_end(ap);
	return s;
}
```

**Guarantee (`correctness`).** For every list `xs` of 64-bit integers (`|xs| < 2^31`), every
System V call of the gcc-compiled `k_vsum` with the prototype `int64_t (int, ...)` called as
`k_vsum(|xs|, xs[0], …)` — the arguments where the classification puts them (`CCallA`: `n` in
`EDI`, `xs[0..4]` in `RSI RDX RCX R8 R9`, the rest in consecutive 8-byte slots of the argument
area from `RSP + 8`; `AL` is an upper bound on the vector registers used, here 0) — whose 88-byte
frame below `RSP` is writable and whose stack-protector canary (`%fs:0x28`) is readable outside
the frame, returns, restores what System V requires (`CReturn`), writes no memory outside its
frame, and returns `xs[0] + … + xs[|xs|-1]` (mod 2^64) in `RAX`.

**How.** gcc's `va_arg` expansion keeps `gp_offset` in `ESI` and the register save area in `R9`
(the prologue saves `RSI`–`R9` there; it does not save the `XMM` registers, since no `va_arg`
reads one), and `overflow_arg_area` in `RCX`. `reg_phase` is the loop while `gp_offset ≤ 40`
(`va_arg` reads `[reg_save_area + gp_offset]`), `over_phase` the loop over the argument area
(unrolled twice by gcc), `epilogue` the canary check and the return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C Janus.Spec

namespace Proof

abbrev entry : Nat := Extracted.entry

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



/-- The frame and the canary: what `k_vsum` needs besides its arguments. -/
def Frame (s : State) : Prop :=
  96 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 88) 96 true = true ∧
    s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧ s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧
    Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - 88, (s.regs 4).toNat)]

/-- **`k_vsum(|xs|, xs…)` returns `xs[0] + … + xs[|xs|-1]`**, for every list `xs`. -/
theorem correctness (xs : List (BitVec 64)) (hk : xs.length < 2 ^ 31) :
    CEnsuresR Extracted.program entry (sig xs) (xs.length :: xs.map BitVec.toNat) Frame
      (fun s s' v => v = (psum xs xs.length).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat)]) := by
  refine CEnsuresA.of_summary (summary xs) ?_ ?_
  · rintro ret s hret hs ⟨hb, htop, hacc, hca, hcb, hco⟩
    simp only [outside_cons, outside_nil, and_true] at hco
    have ha := hs.args
    have hst : (sig xs).start = {} := rfl
    simp only [SysV.Sig.passing, hst] at ha
    simp only [sig, SysV.assignAll, assign_n] at ha
    rw [argsAt_cons, argsAt_ints_gen s _ xs (by decide) (by decide) (by decide)] at ha
    obtain ⟨hn, hargs⟩ := ha
    simp only [ArgAt, PiecesAt, PieceAt, bytesOf, Nat.pow_zero, Nat.div_one, and_true,
      Nat.reducePow] at hn
    exact { n := by rw [Nat.mod_eq_of_lt (by omega : xs.length < 4294967296)] at hn; simpa using hn
            len := hk, args := hargs, b := hb, top := htop, acc := hacc, ca := hca, cb := hcb,
            co := by omega, ra := hs.ret_lt hret, df := hs.df, al := hs.al }
  · rintro s s' - ⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, hx, hmf, h0⟩
    refine ⟨CReturn.of_eqs hsp h3 h5 h12 h13 h14 h15 hdf hmx hfw, _, ?_, rfl, hmf⟩
    have : SysV.result (.int 8 true) = .direct [⟨0, 8, .gpr 0⟩] := by decide
    simp only [Returned, sig, this, ResultAt, PiecesAt, and_true, pieceAt_gpr_word, h0]

end Proof

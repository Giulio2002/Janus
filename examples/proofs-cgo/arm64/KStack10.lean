import Extracted

/-!
# `int64_t k_stack10(a, b, c, d, e, f, g, h, int32_t i, j)` (C, arm64): stack arguments

**Guarantee.** For all 64-bit `a … h`, `j` and 32-bit `i`, every AAPCS64 call of the
gcc-compiled `k_stack10` whose arguments are where the classification of its prototype puts
them (`CCallA`: `a`–`h` in `X0`–`X7`, `i` in the low half of the first stacked slot `[SP]`, `j` in
the second `[SP + 8]`; Janus.C.AAPCS64) returns, restores `SP`, `X19`–`X29`, `D8`–`D15` and
`FPCR` (`CReturn`), and returns in `X0` the value
`a + 2b + 3c + 4d + 5e + 6f + 7g + 8h + 9i + 10j` (mod 2^64, `i` sign-extended).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C

namespace Proof

/-- The prototype. -/
def sig : AAPCS64.Sig :=
  ⟨some (.int 8 true), List.replicate 8 (.int 8 true) ++ [.int 4 true, .int 8 true], none⟩

/-- Where Janus's classification puts the arguments. -/
theorem passing : sig.passing =
    ((List.range 8).map fun r => .direct [⟨0, 8, .gpr r⟩]) ++
      [.direct [⟨0, 4, .stack 0⟩], .direct [⟨0, 8, .stack 8⟩]] := by decide

/-- The result is `X0`. -/
theorem result : AAPCS64.result (.int 8 true) = .direct [⟨0, 8, .gpr 0⟩] := by decide

/-- The specification. -/
def spec (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : BitVec 64 :=
  a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i.signExtend 64 + 10 * j

/-- The argument values of the call `k_stack10(a, …, j)`. -/
def vals (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : List Nat :=
  [a, b, c, d, e, f, g, h].map BitVec.toNat ++ [i.toNat, j.toNat]

/-- What `k_stack10` needs (the callee contract's precondition): its arguments where the
classification puts them, an aligned `SP` and a return address. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ s.sp.toNat % 16 = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

/-- `SPre` with the classification evaluated: the equations a call site has to establish. -/
theorem spre_iff (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) (s : State) :
    SPre (vals a b c d e f g h i j) s ↔
      s.regs 0 = a ∧ s.regs 1 = b ∧ s.regs 2 = c ∧ s.regs 3 = d ∧ s.regs 4 = e ∧ s.regs 5 = f ∧
      s.regs 6 = g ∧ s.regs 7 = h ∧
      (s.sp.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible s.sp.toNat 4 false = true ∧
        s.mem.readLE s.sp.toNat 4 = i.toNat) ∧
      (s.sp.toNat + 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + 8) 8 false = true ∧
        s.mem.readLE (s.sp.toNat + 8) 8 = j.toNat) ∧
      s.sp.toNat % 16 = 0 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, List.map, List.range, List.range.loop, List.cons_append, List.nil_append,
    ArgsAt, ArgAt, PiecesAt, and_true, List.replicate, pieceAt_gpr_word, pieceAt_stack_word]
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one, Nat.add_zero, Nat.reducePow,
    Nat.mod_eq_of_lt i.isLt, and_assoc]

/-- What it guarantees, as plain equations (for a caller's `janus_run`). -/
abbrev SPost (r : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = s.mem ∧ s'.regs 0 = r

/-- The callee contract of `k_stack10`. -/
theorem summary (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals a b c d e f g h i j))
      (SPost (spec a b c d e f g h i j)) := by
  intro s hpc hpre
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨hib, hia, hi⟩, ⟨hjb, hja, hj⟩, hal, hlra, hlrb⟩ :=
    (spre_iff a b c d e f g h i j s).1 hpre
  janus_run
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  rw [hi, hj]
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 i.toNat) = i := by
    apply BitVec.eq_of_toNat_eq; simp
  have hse : BitVec.ofInt 64 i.toInt = i.signExtend 64 := by
    rw [← BitVec.toInt_signExtend_of_le (x := i) (v := 64) (by decide), BitVec.ofInt_toInt]
  rw [hw, BitVec.ofInt_add, BitVec.ofInt_mul, hse, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [spec, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, BitVec.reduceToNat, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod, show (BitVec.ofInt 64 9).toNat = 9 from rfl]
  generalize (i.signExtend 64).toNat = I
  omega

/-- **`k_stack10` under the C calling convention**: the classified call returns the weighted
sum. -/
theorem correctness (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals a b c d e f g h i j) (fun _ => True)
      (fun _ _ v => v = (spec a b c d e f g h i j).toNat) :=
  CEnsuresA.of_summary (summary a b c d e f g h i j)
    (fun _ _ hret hs _ => ⟨hs.args, hs.spAligned, hs.lr_ok hret⟩)
    (fun _ _ _ ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, _, h0⟩ =>
      ⟨CReturn.of_eqs hsp h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 hfc hv, _,
        by simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, pieceAt_gpr_word, h0], rfl⟩)

end Proof

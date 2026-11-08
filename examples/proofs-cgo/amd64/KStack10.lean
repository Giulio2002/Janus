import Extracted

/-!
# `int64_t k_stack10(a, b, c, d, e, f, g, h, int32_t i, j)` (C, amd64): stack arguments

**Guarantee.** For all 64-bit `a … h`, `j` and 32-bit `i`, every System V call of the
gcc-compiled `k_stack10` whose arguments are where the classification of its prototype puts
them (`CCallA`: `a`–`f` in `RDI RSI RDX RCX R8 R9`, then `g`, `h`, `i` (low half of its slot) and
`j` in the 8-byte slots of the argument area at `RSP + 8`, `+ 16`, `+ 24`, `+ 32`;
`Janus.C.SysV`) and whose return-address slot is readable, returns, pops the return address,
restores `RBX RBP R12–R15`, `DF`, the `MXCSR` control bits and the x87 control word (`CReturn`),
and returns in `RAX` the value `a + 2b + 3c + 4d + 5e + 6f + 7g + 8h + 9i + 10j` (mod 2^64, `i`
sign-extended).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.C

namespace Proof

def sig : SysV.Sig :=
  ⟨some (.int 8 true), List.replicate 8 (.int 8 true) ++ [.int 4 true, .int 8 true], none⟩

theorem passing : sig.passing =
    [.direct [⟨0, 8, .gpr 7⟩], .direct [⟨0, 8, .gpr 6⟩], .direct [⟨0, 8, .gpr 2⟩],
     .direct [⟨0, 8, .gpr 1⟩], .direct [⟨0, 8, .gpr 8⟩], .direct [⟨0, 8, .gpr 9⟩],
     .direct [⟨0, 8, .stack 0⟩], .direct [⟨0, 8, .stack 8⟩], .direct [⟨0, 4, .stack 16⟩],
     .direct [⟨0, 8, .stack 24⟩]] := by decide

theorem result : SysV.result (.int 8 true) = .direct [⟨0, 8, .gpr 0⟩] := by decide

def spec (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : BitVec 64 :=
  a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i.signExtend 64 + 10 * j

def vals (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) : List Nat :=
  [a, b, c, d, e, f, g, h].map BitVec.toNat ++ [i.toNat, j.toNat]

/-- What `k_stack10` needs: its arguments where the classification puts them, a readable return
address slot holding a user address, `DF` clear. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.df = false

theorem spre_iff (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) (s : State) :
    SPre (vals a b c d e f g h i j) s ↔
      s.regs 7 = a ∧ s.regs 6 = b ∧ s.regs 2 = c ∧ s.regs 1 = d ∧ s.regs 8 = e ∧ s.regs 9 = f ∧
      ((s.regs 4).toNat + 8 + 0 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 8 + 0) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 8 + 0) 8 = g.toNat) ∧
      ((s.regs 4).toNat + 8 + 8 + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat + 8 + 8) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 8 + 8) 8 = h.toNat) ∧
      ((s.regs 4).toNat + 8 + 16 + 4 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat + 8 + 16) 4 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 8 + 16) 4 = i.toNat) ∧
      ((s.regs 4).toNat + 8 + 24 + 8 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat + 8 + 24) 8 false = true ∧
        s.mem.readLE ((s.regs 4).toNat + 8 + 24) 8 = j.toNat) ∧
      (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
      s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false := by
  unfold SPre
  rw [passing]
  simp only [vals, sig, List.map, List.cons_append, List.nil_append, List.replicate, ArgsAt, ArgAt,
    PiecesAt, and_true, pieceAt_gpr_word, pieceAt_stack_word]
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.mod_eq_of_lt i.isLt,
    and_assoc, CABI.regSP]

abbrev SPost (r : BitVec 64) (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 3 = s.regs 3 ∧ s'.regs 5 = s.regs 5 ∧
    s'.regs 12 = s.regs 12 ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    s'.regs 15 = s.regs 15 ∧ s'.df = false ∧ s'.mxcsr = s.mxcsr ∧ s'.fpucw = s.fpucw ∧
    s'.mem = s.mem ∧ s'.regs 0 = r

theorem summary (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals a b c d e f g h i j))
      (SPost (spec a b c d e f g h i j)) := by
  intro s hpc hpre
  obtain ⟨h7, h6, h2, h1, h8, h9, ⟨hgb, hga, hg⟩, ⟨hhb, hha, hh⟩, ⟨hib, hia, hi⟩, ⟨hjb, hja, hj⟩,
    hsb, hsa, hra, hdf⟩ := (spre_iff a b c d e f g h i j s).1 hpre
  simp only [Nat.add_zero] at hgb hga hg
  janus64_run
  simp only [SPost, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, true_and, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  refine ⟨rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [spec, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_sub,
    Nat.shiftLeft_eq, BitVec.reduceToNat, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_mul_mod]
  generalize (i.signExtend 64).toNat = I
  have := g.isLt
  omega

/-- **`k_stack10` under the System V calling convention.** -/
theorem correctness (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals a b c d e f g h i j) (fun s => CStack s 0 8)
      (fun _ _ v => v = (spec a b c d e f g h i j).toNat) :=
  CEnsuresA.of_summary (summary a b c d e f g h i j)
    (fun _ s hret hs ⟨_, _, hnw, hst⟩ => by
      simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at hnw hst
      exact ⟨hs.args, hnw, Janus.Arm64.Memory.accessible_weaken _ hst, hs.ret_lt hret, hs.df⟩)
    (fun _ _ _ ⟨hsp, h3, h5, h12, h13, h14, h15, hdf, hmx, hfw, _, h0⟩ =>
      ⟨CReturn.of_eqs hsp h3 h5 h12 h13 h14 h15 hdf hmx hfw, _,
        by simp only [Returned, sig, result, ResultAt, PiecesAt, and_true, pieceAt_gpr_word, h0], rfl⟩)

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def i0 : BitVec 32 := 11#32
def j0 : BitVec 64 := 12#64

/-- The stack: the return address at `[wsp]`, then the stacked arguments `7`, `8` (words), `11`
(a dword at `wsp+24`) and `12`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp))
    else if wsp + 8 ≤ a ∧ a < wsp + 16 then BitVec.ofNat 8 (7 / 256 ^ (a - (wsp + 8)))
    else if wsp + 16 ≤ a ∧ a < wsp + 24 then BitVec.ofNat 8 (8 / 256 ^ (a - (wsp + 16)))
    else if wsp + 24 ≤ a ∧ a < wsp + 28 then BitVec.ofNat 8 (11 / 256 ^ (a - (wsp + 24)))
    else if wsp + 32 ≤ a ∧ a < wsp + 40 then BitVec.ofNat 8 (12 / 256 ^ (a - (wsp + 32))) else 0,
   [⟨wsp - 64, 128, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then 1#64 else if i = 6 then 2#64 else if i = 2 then 3#64
      else if i = 1 then 4#64 else if i = 8 then 5#64 else if i = 9 then 6#64
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem spre : SPre (vals 1#64 2#64 3#64 4#64 5#64 6#64 7#64 8#64 i0 j0) s0 :=
  (spre_iff 1#64 2#64 3#64 4#64 5#64 6#64 7#64 8#64 i0 j0 s0).2
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨by decide, by decide, by decide +kernel⟩, ⟨by decide, by decide, by decide +kernel⟩,
      ⟨by decide, by decide, by decide +kernel⟩, ⟨by decide, by decide, by decide +kernel⟩,
      by decide, by decide, by decide +kernel, by decide⟩

theorem call : CCallA (Extracted.program.withExit ret) Extracted.entry sig
    (vals 1#64 2#64 3#64 4#64 5#64 6#64 7#64 8#64 i0 j0) s0 :=
  ⟨rfl, by decide +kernel, by decide, rfl, spre.1, (by intro t ht hr; simp only [sig, Option.some.injEq] at ht; subst ht; rw [result] at hr; cases hr), (by intro h; simp [sig] at h)⟩

theorem stack : CStack s0 0 8 := ⟨by decide, by decide, by decide, by decide⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (a b c d e f g h : BitVec 64) (i : BitVec 32) (j : BitVec 64) (ret : Nat) (s : State),
    RetAddr Extracted.program ret ∧
    CCallA (Extracted.program.withExit ret) Extracted.entry sig (vals a b c d e f g h i j) s ∧ (CStack s 0 8) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      (∃ v, Returned sig s s' v ∧ (v = (spec a b c d e f g h i j).toNat))) :=
  ⟨1#64, 2#64, 3#64, 4#64, 5#64, 6#64, 7#64, 8#64, i0, j0, ret, s0, hret, call, stack,
    correctness 1#64 2#64 3#64 4#64 5#64 6#64 7#64 8#64 i0 j0 ret hret s0 call stack⟩

end Witness

end Proof

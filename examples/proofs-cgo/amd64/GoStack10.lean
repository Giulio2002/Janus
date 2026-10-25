import Extracted

/-!
# `Stack10(a, b, c, d, e, f, g, h int64, i int32, j int64) int64` (Go) → `k_stack10` (C, ten
# arguments, four in the argument area) → back to Go, end to end (amd64)

**Guarantee (`correctness`).** For all `a … h`, `j` and 32-bit `i`, every Go call of
`example.com/cgo/cabi.Stack10` — `a`–`h` and `i` in Go's nine integer argument registers
`RAX RBX RCX RDI RSI R8 R9 R10 R11`, `j` in the Go argument slot at `RSP + 8` — satisfying
`GoPre` returns, restores `RSP`, `RBP`, `R14` (`g`), and leaves
`a + 2b + … + 9i + 10j` (mod 2^64, `i` sign-extended) in `RAX`, under the trusted `CgoCall`
contract only.

**How.** The C wrapper loads the ten arguments from the cgo frame, passes six in
`RDI RSI RDX RCX R8 R9` and pushes the other four, and calls `k_stack10`: `wrapper_spec` uses
the callee contract `summary` of `k_stack10`, whose precondition is Janus's System V
classification of the prototype (`ArgsAt … sig.passing`: the argument area at `RSP + 8`),
proved at the call site.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Spec
  Janus.Amd64.FFI Janus.C

namespace Proof

/-! ## The C function `k_stack10` (as in `KStack10.lean`), as a callee summary -/

abbrev ks : Nat := segAddr Extracted.program "k_stack10"

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
    Summary Extracted.program ks (SPre (vals a b c d e f g h i j))
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


/-! ## The cgo wrapper -/

abbrev wrapper : Nat := segAddr Extracted.program "_cgo_a66fe0e77ed3_Cfunc_k_stack10"

def fw (m : Memory) (a k : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * k) 8)
def fi (m : Memory) (a : Nat) : BitVec 32 := BitVec.ofNat 32 (m.readLE (a + 64) 4)

def res (m : Memory) (a : Nat) : Nat :=
  (spec (fw m a 0) (fw m a 1) (fw m a 2) (fw m a 3) (fw m a 4) (fw m a 5) (fw m a 6) (fw m a 7)
    (fi m a) (fw m a 9)).toNat

def WPre (a : BitVec 64) (t : State) : Prop :=
  CStack t 4096 8 ∧ a.toNat + 88 ≤ 2 ^ 48 ∧ t.mem.accessible a.toNat 88 true = true ∧
    (a.toNat + 88 ≤ (t.regs 4).toNat - 4096 ∨ (t.regs 4).toNat + 8 ≤ a.toNat)

def WPost (a : BitVec 64) (t t' : State) : Prop :=
  MemFrame (t.mem.writeLE (a.toNat + 80) 8 (res t.mem a.toNat)) t'.mem
    [((t.regs 4).toNat - 4096, (t.regs 4).toNat)]

set_option maxHeartbeats 4000000 in
theorem wrapper_spec (T a : BitVec 64) :
    CEnsuresC Extracted.program (TopOfStack T) wrapper [a] (WPre a) (WPost a) := by
  intro ret hret t hs ⟨⟨hal, hb, htop, hacc⟩, ha, hfa, hd⟩
  apply ReturnsC.of_reaches
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : t.regs 7 = a := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  simp only [CABI.regSP] at hal hb htop hacc
  have h32 : (t.regs 4 - 32#64).toNat = (t.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₁ ⟨-, f₁, rfl⟩
  apply ReturnsC.of_reaches
  have hz : (t.regs 4).toNat - 64 + 8 + 16 - ((t.regs 4).toNat - 40) = 0 := by omega
  janus64_run [spre_iff, fw, fi, BitVec.toNat_ofNat, hz, Nat.pow_zero, Nat.div_one, Nat.mod_mod]
    calls [summary (fw t.mem a.toNat 0)
    (fw t.mem a.toNat 1) (fw t.mem a.toNat 2) (fw t.mem a.toNat 3) (fw t.mem a.toNat 4)
    (fw t.mem a.toNat 5) (fw t.mem a.toNat 6) (fw t.mem a.toNat 7) (fi t.mem a.toNat)
    (fw t.mem a.toNat 9)]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp [h32]; omega
  · janus64_simp [h32]; janus64_disch
  rintro s₂ ⟨-, f₂, rfl⟩
  apply ReturnsC.of_reaches
  janus64_run
  refine ⟨by assumption, ?_⟩
  simp only [WPost, res, fw, fi, Nat.reducePow, writeLE_mod_8, Nat.mul_zero, Nat.add_zero,
    Nat.reduceMul]
  apply Janus.MemFrame.writeLE_both
  janus_frame

/-! ## The Go side: `Stack10` → `_Cfunc_k_stack10` → `runtime.cgocall` -/

def fnVar : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" + 0x2e)

def alwaysFalse : Nat :=
  ripTarget Extracted.program (segAddr Extracted.program "example.com/cgo/cabi._Cfunc_k_stack10.abi0" + 0x47)

def G (s : State) : Prop := (s.regs 3).toNat + 88 ≤ 2 ^ 48 ∧ GoKept s (s.regs 3).toNat 88 true

def E (s : State) : Memory :=
  s.mem.writeLE ((s.regs 3).toNat + 80) 8 (res s.mem (s.regs 3).toNat)

/-- The Go caller's precondition; `j`, Go's tenth integer argument, is in the stack slot above
the return address. -/
def GoPre (j : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 104 ∧ StackWritable s 144 16 ∧ TlsG s ∧
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = j.toNat ∧
  s.mem.accessible fnVar 8 false = true ∧ s.mem.readLE fnVar 8 = wrapper ∧
  s.mem.accessible alwaysFalse 1 false = true ∧ s.mem.readLE alwaysFalse 1 = 0 ∧
  Outside (s.regs 14).toNat 456 [((s.regs 4).toNat - 144, (s.regs 4).toNat + 16)] ∧
  Outside (s.fsBase.toNat - 8) 8 [((s.regs 4).toNat - 144, (s.regs 4).toNat + 16)] ∧
  Outside fnVar 8 [((s.regs 4).toNat - 144, (s.regs 4).toNat + 16)] ∧
  Outside alwaysFalse 1 [((s.regs 4).toNat - 1168, (s.regs 4).toNat + 16),
    ((s.regs 14).toNat, (s.regs 14).toNat + 456), (s.fsBase.toNat - 8, s.fsBase.toNat)]

set_option maxHeartbeats 4000000 in
theorem go_spec (a b c d e f g h i j : BitVec 64) :
    EnsuresC Extracted.program (CgoSpec wrapper G E) Extracted.entry [a, b, c, d, e, f, g, h, i]
      (GoPre j) (fun _ s' => s'.regs 0 = spec a b c d e f g h (i.setWidth 32) j) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, htop, hst⟩, ⟨hfs, hfsr, hfsg⟩, hj, hfa, hfv, haa, hav,
    hdg, hdt, hdf, hda⟩
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
  have h96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h136 : (s.regs 4 - 136#64).toNat = (s.regs 4).toNat - 136 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h144 : (s.regs 4 - 144#64).toNat = (s.regs 4).toNat - 144 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus64_run [hfsa]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
  · simp only [G, GoKept, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
      cgoStackScratch, gStructSize, outside_cons, outside_nil, and_true]
    janus64_simp [h96, h144]
    refine ⟨by omega, ?_, by omega, by omega, by omega, by omega⟩
    janus64_disch
  rintro s' ⟨-, m, ⟨regs, fl, xm, yh, fs, mx, _, rfl, h4, h5, h14, h15, ⟨⟨hfs1, hfs2⟩, hfsr', hfsg'⟩, -⟩, hmf⟩
  simp only [E, res, fw, fi, cgoClobber, Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.regG,
    Janus.Amd64.GoABI.regFP, Janus.Amd64.GoABI.xmmZero, cgoStackScratch, gStructSize, setRegF,
    ↓reduceIte, Nat.reduceEqDiff, h96, h144] at hmf h4 h5 h14 h15 hfs1 hfs2 hfsr' hfsg'
  have hfsa' : (fs + BitVec.ofNat 64 18446744073709551608).toNat = fs.toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hmf.accessible] at hfsr'
  simp only [Janus.Arm64.Memory.accessible_writeLE] at hfsr'
  apply ReturnsC.of_reaches
  janus64_run [h4, h5, h14, h15, hfsa', hfsg']
  have hw : BitVec.ofNat 32 (i.toNat % 4294967296) = BitVec.setWidth 32 i := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.mod_mod]
  exact ⟨rfl, by rw [hw]⟩

/-! ## Composition -/

theorem refines : (CgoCall Extracted.program).Refines (CgoSpec wrapper G E) := by
  refine CgoCall.refines (fun T a => wrapper_spec T a) ?_ ?_ ?_ ?_
  · rintro s t ret ⟨hb, hacc, hout⟩ he
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true, Janus.Amd64.GoABI.regSP] at hsep
    exact ⟨he.stack, hb, he.keptAcc _ _ _ ⟨hacc, hout⟩, by have := hsep; unfold cgoCStack at this; omega⟩
  · intro s _; rfl
  · rintro s t ret t' ⟨hb, hacc, hout⟩ he _ hpost b hb' hbacc
    have hsep := he.stackSep b 1 false hbacc
    have h1 := hpost.readLE b 1 (by
      simp only [outside_cons, outside_nil, and_true, cgoCStack, Janus.Amd64.GoABI.regSP] at hsep ⊢; omega)
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk : ∀ c n, (s.regs 3).toNat ≤ c → c + n ≤ (s.regs 3).toNat + 88 →
        t.mem.readLE c n = s.mem.readLE c n := fun c n h1 h2 =>
      he.kept c n ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) h1 h2, Outside.of_sub hout h1 h2⟩
    split
    · simp only [res, fw, fi, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
      rw [hk (s.regs 3).toNat 8 (Nat.le_refl _) (by omega),
        hk ((s.regs 3).toNat + 8) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 16) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 24) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 32) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 40) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 48) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 56) 8 (by omega) (by omega),
        hk ((s.regs 3).toNat + 64) 4 (by omega) (by omega),
        hk ((s.regs 3).toNat + 72) 8 (by omega) (by omega)]
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro s ⟨hb, hacc, hout⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`Stack10` end to end**, under the trusted `CgoCall` contract only. -/
theorem correctness (a b c d e f g h i j : BitVec 64) :
    EnsuresC Extracted.program (CgoCall Extracted.program) Extracted.entry [a, b, c, d, e, f, g, h, i]
      (GoPre j) (fun _ s' => s'.regs 0 = spec a b c d e f g h (i.setWidth 32) j) :=
  (go_spec a b c d e f g h i j).refine refines

end Proof

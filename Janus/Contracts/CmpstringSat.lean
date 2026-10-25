import Janus.Contracts.Cmpstring
import Janus.Tactic

/-!
# The `runtime.cmpstring` contract is satisfiable (arm64)

A byte loop written in A64 (its words below), placed at `A0` in a program with no other code,
meets `CmpstringContract` (proved by symbolic execution, by induction on the remaining length),
and a call state satisfying the contract's precondition exists. So the contract is not
contradictory, and a theorem assuming it is not vacuous.

```
loop: cbz x1, aend ; cbz x3, gt
      ldrb w5, [x0], #1 ; ldrb w6, [x2], #1 ; cmp w5, w6 ; b.lo lt ; b.hi gt
      sub x1, x1, #1 ; sub x3, x3, #1 ; b loop
aend: cbz x3, eq
lt:   movn x0, #0 ; ret
gt:   mov x0, #1 ; ret
eq:   mov x0, #0 ; ret
```
-/

set_option linter.unusedSimpArgs false

namespace Janus.Contracts.CmpstringSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.Cmpstring

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the implementation is placed. -/
abbrev A0 : Nat := 0x100000

/-- The byte loop. -/
def code : List Nat :=
  [0xb4000141, 0xb4000183, 0x38401405, 0x38401446, 0x6b0600bf, 0x540000c3, 0x540000e8, 0xd1000421,
   0xd1000463, 0x17fffff7, 0xb40000a3, 0x92800000, 0xd65f03c0, 0xd2800020, 0xd65f03c0, 0xd2800000,
   0xd65f03c0]

/-- The implementation: `code` at `A0`. -/
def impl : List Segment := [{ name := "cmpstring", base := A0, words := code }]

/-- `toy` linked with `impl`, as a closed program. -/
def prog : Program := { segments := impl, stubs := [], exitAddr := 0 }

theorem link_eq : toy.link impl = prog := rfl

/-- The return of the implementation as `CmpRet`. -/
theorem ret_of (s : State) (R : Nat → W64) (F : Flags) (hR0 : R 0 = cmpResult s)
    (h18 : R 18 = s.regs 18) (h28 : R 28 = s.regs 28) (h29 : R 29 = s.regs 29) :
    CmpRet 16 s { s with regs := R, flags := F, pc := s.regs 30 } := by
  refine ⟨R, F, s.vregs, s.mem, ?_, MemFrame.refl _ _⟩
  simp only [retState]
  congr 1
  funext i
  simp only [callRegs]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · simp only [h, ite_false]
    by_cases h0 : i = 0
    · subst h0; simp [hR0]
    · cases i with
      | zero => exact absurd rfl h0
      | succ j => simp

/-- The loop, from its head with `la` bytes of `a` left. -/
theorem loop (s : State) (hr1 : (s.regs 30).toNat % 4 = 0) (hr2 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
      R 0 = BitVec.ofNat 64 a → R 1 = BitVec.ofNat 64 la → R 2 = BitVec.ofNat 64 b →
      R 3 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
      R 18 = s.regs 18 → R 28 = s.regs 28 → R 29 = s.regs 29 → R 30 = s.regs 30 →
      StrOK s.mem a la → StrOK s.mem b lb →
      strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 2).toNat (s.regs 1).toNat (s.regs 3).toNat →
      ReachesRet prog (s.regs 30) { s with regs := R, flags := F, pc := 0x100000#64 } (CmpRet 16 s) := by
  intro la
  induction la with
  | zero =>
    intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
    janus_run [h0, h1, h2, h3, h30]
    all_goals
      apply ret_of
      all_goals try (simp only [setReg]; simp [h18, h28, h29])
      simp only [cmpResult]
      rw [← hc]
      clear hc
      cases lb <;> simp_all [strCmp] <;> decide
  | succ la ih =>
    intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
    rcases hsa with hsa | ⟨hsa1, hsa2⟩
    · omega
    have ha1 : s.mem.accessible a 1 false = true := Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
    cases lb with
    | zero =>
      janus_run [h0, h1, h2, h3, h30]
      all_goals
        apply ret_of
        all_goals try (simp only [setReg]; simp [h18, h28, h29])
        simp only [cmpResult]
        rw [← hc]
        clear hc
        simp [strCmp]
    | succ lb =>
      rcases hsb with hsb | ⟨hsb1, hsb2⟩
      · omega
      have hb1 : s.mem.accessible b 1 false = true := Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
      have hx : s.mem.readLE a 1 < 256 := by simpa using Memory.readLE_lt s.mem a 1
      have hy : s.mem.readLE b 1 < 256 := by simpa using Memory.readLE_lt s.mem b 1
      janus_run [h0, h1, h2, h3, h30] until [0x100000]
      all_goals first
        | (apply ret_of
           all_goals try (simp only [setReg]; simp [h18, h28, h29])
           simp only [cmpResult]
           rw [← hc]
           clear hc
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
           rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
             Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at *
           rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
             Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at *
           simp only [strCmp]
           split <;> (try split) <;> first | rfl | omega | decide)
        | skip
      rename_i hle
      have heq := hbr
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hle heq
      rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at heq
      rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at heq
      apply ih _ _ (a + 1) (b + 1) lb
      all_goals try (simp only [setReg]; simp [h18, h28, h29, h30])
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · omega
      · omega
      · by_cases hl : la = 0
        · exact Or.inl hl
        · exact Or.inr ⟨Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩
      · by_cases hl : lb = 0
        · exact Or.inl hl
        · exact Or.inr ⟨Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩
      · rw [← hc]
        simp only [strCmp, heq, Nat.lt_irrefl, ite_false]

/-- The byte loop meets the contract. -/
theorem impl_ok : CmpstringContract (toy.link impl) A0 16 := by
  rw [link_eq]
  intro s hpc ⟨⟨hr1, hr2, _⟩, hsa, hsb⟩
  have key := loop s hr1 hr2 (s.regs 1).toNat s.regs s.flags (s.regs 0).toNat (s.regs 2).toNat
    (s.regs 3).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 1).isLt (s.regs 3).isLt rfl rfl rfl rfl
    hsa hsb rfl
  have hs : ({ s with regs := s.regs, flags := s.flags, pc := 0x100000#64 } : State) = s := by
    cases s; simp only at hpc ⊢; rw [hpc]
  rw [hs] at key
  exact key

/-- The witness call state: two empty strings, `SP = 0x1800` in a writable region, `X30` outside
the code. -/
def wstate : State :=
  { regs := fun i => if i = 30 then 0x200000#64 else 0#64, sp := 0x1800#64,
    pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨0x1000, 0x1000, true⟩]⟩ }

theorem wstate_pre : CmpstringPre 16 wstate := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    Or.inl (by decide), Or.inl (by decide)⟩

/-- `CmpstringContract` is satisfiable: an implementation meets it and a call state satisfies its
precondition. -/
theorem cmpstring_satisfiable : ∃ impl : List Segment, CmpstringContract (toy.link impl) A0 16 ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ CmpstringPre 16 s :=
  ⟨impl, impl_ok, wstate, rfl, wstate_pre⟩

end Janus.Contracts.CmpstringSat

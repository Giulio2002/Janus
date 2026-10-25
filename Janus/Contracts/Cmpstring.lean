import Janus.Contracts.Alloc

/-!
# The contract of `runtime.cmpstring` (arm64)

Go compares strings with `runtime.cmpstring(a, b string) int` (assembly in
`internal/bytealg/compare_arm64.s`, `cmpbody`): `-1`, `0` or `+1` as `a` is below, equal to or
above `b` in the bytewise lexicographic order (the Go specification's string order). `min` and
`max` of strings call `runtime.strmin`/`runtime.strmax` (Go code, executed), which call it.

A theorem that uses it leaves it out with `janus extract --contract runtime.cmpstring` and takes
`CmpstringContract` as a hypothesis about the linked program (docs/RUNTIME-CONTRACTS.md, "String
comparison"). The contract is satisfiable: `Janus.Contracts.CmpstringSat` proves a byte-loop
implementation meets it.

* **pre** (`CmpstringPre`): the ABI conditions `CallOK` (admissible `X30`, aligned `SP`, the stack
  window `[SP - stack, SP + 8 + 8·4)` writable) and both strings readable (`StrOK`: length `0`, or
  the bytes `[p, p + n)` in one region below `2^48`), with `a = (X0, X1)` and `b = (X2, X3)`.
* **post**: the call returns to `X30` with `X0` the two's-complement `strCmp`, `SP`, `X18`, `X28`,
  `X29` preserved, every other register, the flags and the SIMD registers arbitrary, and memory
  changed at most in the callee's stack window (`calleeStack`; the real function writes nothing).
-/

namespace Janus.Contracts.Cmpstring

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts

/-- The bytewise lexicographic comparison of the `la` bytes at `a` with the `lb` bytes at `b`
in memory `m`: `-1`, `0` or `1`. A proper prefix is smaller. -/
def strCmp (m : Memory) (a b : Nat) : Nat → Nat → Int
  | 0, 0 => 0
  | 0, _ + 1 => -1
  | _ + 1, 0 => 1
  | la + 1, lb + 1 =>
    if m.readLE a 1 < m.readLE b 1 then -1
    else if m.readLE b 1 < m.readLE a 1 then 1
    else strCmp m (a + 1) (b + 1) la lb

/-- The `n` bytes at `p` can be read: `n = 0`, or they lie in one region below `2^48`. -/
def StrOK (m : Memory) (p n : Nat) : Prop :=
  n = 0 ∨ (m.accessible p n false = true ∧ p + n ≤ 2 ^ 48)

/-- The precondition of `runtime.cmpstring(a, b)` (`a = (X0, X1)`, `b = (X2, X3)`). -/
def CmpstringPre (stack : Nat) (s : State) : Prop :=
  CallOK s stack 4 ∧ StrOK s.mem (s.regs 0).toNat (s.regs 1).toNat ∧
    StrOK s.mem (s.regs 2).toNat (s.regs 3).toNat

/-- The comparison result of the call state `s`. -/
def cmpResult (s : State) : W64 :=
  BitVec.ofInt 64 (strCmp s.mem (s.regs 0).toNat (s.regs 2).toNat (s.regs 1).toNat (s.regs 3).toNat)

/-- How `runtime.cmpstring` returns. -/
@[reducible] def CmpRet (stack : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
    s' = retState s junk [cmpResult s] f v m ∧ MemFrame s.mem m (calleeStack s stack 4)

/-- `runtime.cmpstring` at `addr` of `p` (arm64), using at most `stack` bytes below `SP`. -/
def CmpstringContract (p : Program) (addr stack : Nat) : Prop :=
  Summary p addr (CmpstringPre stack) (CmpRet stack)

attribute [janus_exec, janus_post] cmpResult

/-- `strCmp` is `-1`, `0` or `1`. -/
theorem strCmp_cases (m : Memory) (a b la lb : Nat) :
    strCmp m a b la lb = -1 ∨ strCmp m a b la lb = 0 ∨ strCmp m a b la lb = 1 := by
  induction la generalizing a b lb with
  | zero => cases lb <;> simp [strCmp]
  | succ la ih =>
    cases lb with
    | zero => simp [strCmp]
    | succ lb =>
      simp only [strCmp]
      split
      · simp
      · split
        · simp
        · exact ih _ _ _

/-- `strCmp` reads only the bytes of the two strings. -/
theorem strCmp_frame (m m' : Memory) (a b la lb : Nat)
    (h : ∀ x, (a ≤ x ∧ x < a + la) ∨ (b ≤ x ∧ x < b + lb) → m'.readLE x 1 = m.readLE x 1) :
    strCmp m' a b la lb = strCmp m a b la lb := by
  induction la generalizing a b lb with
  | zero => cases lb <;> simp [strCmp]
  | succ la ih =>
    cases lb with
    | zero => simp [strCmp]
    | succ lb =>
      simp only [strCmp]
      rw [h a (Or.inl ⟨Nat.le_refl _, by omega⟩), h b (Or.inr ⟨Nat.le_refl _, by omega⟩),
        ih (a + 1) (b + 1) lb (fun x hx => h x (by omega))]

/-- A store outside both strings does not change the comparison. -/
theorem strCmp_writeLE (m : Memory) (c n v a b la lb : Nat)
    (h1 : la = 0 ∨ a + la ≤ c ∨ c + n ≤ a) (h2 : lb = 0 ∨ b + lb ≤ c ∨ c + n ≤ b) :
    strCmp (m.writeLE c n v) a b la lb = strCmp m a b la lb :=
  strCmp_frame m _ a b la lb fun x hx =>
    Memory.readLE_writeLE_of_disjoint _ _ (by omega)

/-- The sign bit of a comparison result is set exactly for `-1`. -/
theorem cmp_msb (c : Int) (h : c = -1 ∨ c = 0 ∨ c = 1) :
    (BitVec.ofInt 64 c).getLsbD 63 = decide (c < 0) := by
  rcases h with rfl | rfl | rfl <;> decide

end Janus.Contracts.Cmpstring

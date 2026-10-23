import Janus.Arm64.MemoryLemmas

/-! Tests for register and memory lemmas. -/

namespace JanusTests.MemoryLemmas

open Janus.Arm64

/-! Registers: concrete register numbers discharge the `≠ 31` side conditions by `simp`. -/

example (s : State) (v : W64) : (s.writeZR 3 v).readZR 3 = v := by simp
example (s : State) (v : W64) : (s.writeZR 3 v).readZR 4 = s.readZR 4 := by simp
example (s : State) (v : W64) : (s.writeZR 31 v) = s := by simp
example (s : State) (v : W64) : (s.writeZR 31 v).readZR 31 = 0 := by simp
example (s : State) (v : W64) : (s.writeSP 31 v).readSP 31 = v := by simp
example (s : State) (v w : W64) : ((s.writeZR 3 v).writeSP 31 w).readZR 3 = v := by simp
example (s : State) (v w : W64) : ((s.writeZR 3 v).writeSP 31 w).sp = w := by simp
example (s : State) (v w : W64) : ((s.writeSP 31 w).writeZR 5 v).sp = w := by simp
example (s : State) (v w : W64) :
    ((s.writeZR 0 v).writeZR 1 w).regs 0 = v ∧ ((s.writeZR 0 v).writeZR 1 w).regs 1 = w := by
  simp
example (s : State) (v : W64) :
    (s.writeZR 7 v).pc = s.pc ∧ (s.writeZR 7 v).mem = s.mem ∧ (s.writeZR 7 v).flags = s.flags := by
  simp

/-! Memory: concrete computation by `decide`. -/

def m0 : Memory := ⟨fun _ => 0, [⟨0x1000, 16, true⟩, ⟨0x2000, 8, false⟩]⟩

example : (m0.writeLE 0x1000 4 0xdeadbeef).readLE 0x1000 4 = 0xdeadbeef := by decide
example : (m0.writeLE 0x1000 8 0x1122334455667788).readLE 0x1004 4 = 0x11223344 := by decide
example : m0.accessible 0x1000 16 true = true := by decide
example : m0.accessible 0x1008 16 false = false := by decide
example : m0.accessible 0x2000 8 true = false := by decide
example : load m0 0x2000 8 = .ok 0 := rfl
example : store m0 0x2000 8 5 = .error (.readOnly 0x2000 8) := rfl
example : store m0 0x0ff8 8 5 = .error (.outsideAllocation 0x0ff8 8) := rfl

/-! Address-space bound and per-byte permissions. -/

/-- A region that extends past `2^48` (here past `2^64`) is not usable: accesses inside it fault,
so no access wraps around `2^64`. -/
def mWrap : Memory := ⟨fun _ => 0, [⟨2 ^ 64 - 4, 8, true⟩]⟩
example : load mWrap (2 ^ 64 - 4) 8 = .error (.outsideAllocation (2 ^ 64 - 4) 8) := rfl
/-- A tagged address (top byte `1`) never has accessible memory, so it cannot alias. -/
def mTag : Memory := ⟨fun _ => 0, [⟨0x1000, 8, true⟩, ⟨2 ^ 56 + 0x1000, 8, true⟩]⟩
example : mTag.accessible 0x1000 8 true = true := by decide
example : mTag.accessible (2 ^ 56 + 0x1000) 8 false = false := by decide
/-- The last bytes below `2^48` are fine; one byte more is not. -/
def mTop : Memory := ⟨fun _ => 0, [⟨2 ^ 48 - 16, 16, true⟩, ⟨2 ^ 48 - 16, 17, true⟩]⟩
example : mTop.accessible (2 ^ 48 - 8) 8 true = true := by decide
example : mTop.accessible (2 ^ 48 - 8) 9 false = false := by decide
/-- A writable region overlapping a read-only one does not make the read-only bytes writable. -/
def mRO : Memory := ⟨fun _ => 0, [⟨0x2000, 8, false⟩, ⟨0x2000, 16, true⟩]⟩
example : store mRO 0x2000 8 7 = .error (.readOnly 0x2000 8) := rfl
example : store mRO 0x2004 8 7 = .error (.readOnly 0x2004 8) := rfl
example : mRO.accessible 0x2008 8 true = true := by decide
example (m : Memory) (a n : Nat) (w : Bool) (h : m.accessible a n w = true) : a + n ≤ 2 ^ 48 :=
  m.accessible_bound h

/-! Memory: symbolic. -/

example (m : Memory) (a v : Nat) : (m.writeLE a 8 v).readLE a 8 = v % 2 ^ 64 :=
  Memory.readLE_writeLE_self m a 8 v

/-- An 8-byte write read back as two 4-byte halves. -/
example (m : Memory) (a v : Nat) :
    (m.writeLE a 8 v).readLE a 4 = v % 2 ^ 32 ∧
    (m.writeLE a 8 v).readLE (a + 4) 4 = v / 2 ^ 32 % 2 ^ 32 := by
  constructor
  · rw [Memory.readLE_writeLE_inside _ _ (Nat.le_refl a) (by omega)]; simp
  · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
    simp only [Nat.add_sub_cancel_left]

/-- Two 4-byte reads assemble the 8-byte read. -/
example (m : Memory) (a : Nat) : m.readLE a 8 = m.readLE a 4 + 2 ^ 32 * m.readLE (a + 4) 4 :=
  Memory.readLE_eight m a

/-- A write below does not disturb a read above. -/
example (m : Memory) (a v : Nat) : (m.writeLE a 8 v).readLE (a + 8) 8 = m.readLE (a + 8) 8 :=
  Memory.readLE_writeLE_of_disjoint _ _ (Or.inr (Nat.le_refl _))

/-- STP-style: one 16-byte write equals two 8-byte writes. -/
example (m : Memory) (a lo hi : Nat) (hlo : lo < 2 ^ 64) :
    m.writeLE a 16 (lo + 2 ^ 64 * hi) = (m.writeLE a 8 lo).writeLE (a + 8) 8 hi := by
  rw [Memory.writeLE_add m a 8 8, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt hlo, Nat.zero_add, ← Memory.writeLE_mod m a 8 (lo + _),
    Nat.add_mul_mod_self_left, Memory.writeLE_mod]

/-- Store then load, and stores keep the region list. -/
example (m m' : Memory) (a v : Nat) (h : store m a 8 v = .ok m') :
    load m' a 8 = .ok (v % 2 ^ 64) ∧ m'.regions = m.regions :=
  ⟨load_store_self m v h, store_regions m v h⟩

example (m m' : Memory) (a v : Nat) (h : store m a 8 v = .ok m') :
    load m' (a + 16) 4 = load m (a + 16) 4 :=
  load_store_of_disjoint m v h (Or.inr (by omega))

example (m : Memory) (a : Nat) (h : m.accessible a 16 true = true) :
    m.accessible (a + 8) 8 false = true :=
  m.accessible_weaken (m.accessible_mono h (by omega) (by omega))

example (m : Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 := Memory.readLE_lt m a 8

end JanusTests.MemoryLemmas

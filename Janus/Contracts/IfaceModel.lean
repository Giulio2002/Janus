import Janus.Spec.Type

/-!
# A model of the interface runtime, for the non-vacuity of its contracts

The interface contracts (`Janus.Contracts.Iface`, `Janus.Contracts.IfaceAmd64`) are hypotheses
of the theorems that use them. A hypothesis that no code can satisfy would make such a theorem
vacuous, so every contract comes with a proof that it **is** satisfiable
(`Janus.Contracts.IfaceSat`, `Janus.Contracts.IfaceSatAmd64`): a model `R0` of the runtime that
satisfies the laws (`R0_laws`), machine code that satisfies the contract for `R0`, and a call
state that satisfies the contract's precondition (so the contract's postcondition is reached).

`R0` is a small world, not a description of the Go runtime: one ordinary type `TD` (8 bytes, no
pointers, `TFlagRegularMemory`, not direct), one interface type `ID` that `TD` implements with
the itab `TAB`, a box slot `BOX`, and two empty caches; everything inside one runtime range
`[0x10000, 0x11000)`. That suffices: a contract is a `∀`-statement over call states, and its
non-vacuity needs one model, one implementation and one state.

The witness memory `wmem` holds `R0`'s environment (`Env0`), the descriptors of a type
assertion (`DTA`: cache `TAC`, interface `ID`, `CanFail`) and of an interface switch (`DIS`:
cache `ISC`, one case `ID`), a value slot `VAL`, a stack at `[0x40000, 0x50000)` and a goroutine
at `0x50000` whose stack guard is `0`.
-/

namespace Janus.Contracts.IfaceModel

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Spec.Type

/-! ## Addresses -/

/-- The model's one ordinary type descriptor. -/
def TD : Nat := 0x10000
/-- The model's one interface type descriptor. -/
def ID : Nat := 0x10100
/-- The itab of `(ID, TD)`. -/
def TAB : Nat := 0x10200
/-- The box slot every conversion returns. -/
def BOX : Nat := 0x10300
/-- An empty type-assertion cache (`runtime.emptyTypeAssertCache`). -/
def TAC : Nat := 0x10400
/-- An empty interface-switch cache (`runtime.emptyInterfaceSwitchCache`). -/
def ISC : Nat := 0x10500
/-- A type-assertion descriptor (in user data). -/
def DTA : Nat := 0x30000
/-- An interface-switch descriptor with the one case `ID` (in user data). -/
def DIS : Nat := 0x30100
/-- A value slot (in user data) holding `TD`-values for the comparisons. -/
def VAL : Nat := 0x30200

/-- The descriptor bytes the model's environment fixes. -/
def Desc (m : Memory) : Prop :=
  m.readLE TD 8 = 8 ∧ m.readLE (TD + 8) 8 = 0 ∧ m.readLE (TD + 20) 1 = 8 ∧
    m.readLE ID 8 = 8 ∧ m.readLE (ID + 20) 1 = 0 ∧ m.readLE (ID + 64) 8 = 1 ∧
    m.readLE TAB 8 = ID ∧ m.readLE (TAB + 8) 8 = TD

/-- The model's environment: its metadata readable (`[0x10000, 0x10300)`), its heap writable
(`[0x10300, 0x11000)`), the descriptor bytes in place. -/
def Env0 (m : Memory) (_ : W64) : Prop :=
  m.accessible 0x10000 0x300 false = true ∧ m.accessible BOX 0xd00 true = true ∧ Desc m

/-- The model. -/
def R0 : IfaceModel where
  itab i t := if i = ID ∧ t = TD then some TAB else none
  eq _ m x y := m.readLE x 8 == m.readLE y 8
  Comparable t m x y := t = TD ∧ m.accessible x 8 false = true ∧ m.accessible y 8 false = true
  IsType t := t = TD ∨ t = ID
  IsInter i := i = ID
  Env := Env0
  priv := [(0x10000, 0x11000)]
  depth := 64

@[simp] theorem R0_priv : R0.priv = [(0x10000, 0x11000)] := rfl
@[simp] theorem R0_depth : R0.depth = 64 := rfl
@[simp] theorem R0_env (m : Memory) (g : W64) : R0.Env m g = Env0 m g := rfl
@[simp] theorem R0_isType (t : Nat) : R0.IsType t = (t = TD ∨ t = ID) := rfl
@[simp] theorem R0_isInter (i : Nat) : R0.IsInter i = (i = ID) := rfl
@[simp] theorem R0_itab (i t : Nat) : R0.itab i t = if i = ID ∧ t = TD then some TAB else none := rfl
@[simp] theorem R0_eq (t : Nat) (m : Memory) (x y : Nat) :
    R0.eq t m x y = (m.readLE x 8 == m.readLE y 8) := rfl
@[simp] theorem R0_comparable (t : Nat) (m : Memory) (x y : Nat) :
    R0.Comparable t m x y = (t = TD ∧ m.accessible x 8 false = true ∧ m.accessible y 8 false = true) :=
  rfl

theorem inPriv {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n R0.priv :=
  ⟨(0x10000, 0x11000), by simp, h1, h2⟩

/-- The laws hold for `R0`. -/
theorem R0_laws : R0.Laws where
  env_frame m m' g h ha := by
    obtain ⟨h1, h2, d1, d2, d3, d4, d5, d6, d7, d8⟩ := h
    have hr : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → m'.readLE a n = m.readLE a n :=
      fun a n h1 h2 => ha.readLE (inPriv h1 h2)
    refine ⟨by rw [ha.accessible]; exact h1, by rw [ha.accessible]; exact h2,
      (hr TD 8 (by simp [TD]) (by simp [TD])).trans d1,
      (hr (TD + 8) 8 (by simp [TD]) (by simp [TD])).trans d2,
      (hr (TD + 20) 1 (by simp [TD]) (by simp [TD])).trans d3,
      (hr ID 8 (by simp [ID]) (by simp [ID])).trans d4,
      (hr (ID + 20) 1 (by simp [ID]) (by simp [ID])).trans d5,
      (hr (ID + 64) 8 (by simp [ID]) (by simp [ID])).trans d6,
      (hr TAB 8 (by simp [TAB]) (by simp [TAB])).trans d7,
      (hr (TAB + 8) 8 (by simp [TAB]) (by simp [TAB])).trans d8⟩
  type_desc m g t h ht := by
    obtain ⟨h1, -, -⟩ := h
    rcases ht with rfl | rfl
    · exact ⟨by decide, by decide, Memory.accessible_mono _ h1 (by decide) (by decide),
        inPriv (by decide) (by decide)⟩
    · exact ⟨by decide, by decide, Memory.accessible_mono _ h1 (by decide) (by decide),
        inPriv (by decide) (by decide)⟩
  inter_desc m g i h hi := by
    obtain ⟨h1, -, -, -, -, -, -, d6, -⟩ := h
    simp only [R0_isInter] at hi
    subst hi
    refine ⟨Or.inr rfl, by decide, Memory.accessible_mono _ h1 (by decide) (by decide),
      inPriv (by decide) (by decide), ?_⟩
    simp only [interMethods]; rw [d6]; decide
  itab_ne i t tab h := by
    simp only [R0_itab] at h
    split at h
    · cases h; decide
    · cases h
  regular m g t x y h ht hreg hnd hx hy := by
    obtain ⟨-, -, d1, -, d3, d4, d5, -⟩ := h
    rcases ht with rfl | rfl
    · simp only [tySize, d1] at hx hy ⊢
      exact ⟨⟨rfl, hx, hy⟩, rfl⟩
    · simp [isRegularMemory, tyTFlag, d5] at hreg
  direct m g t x y h ht hreg hd := by
    obtain ⟨-, -, -, -, d3, -, d5, -⟩ := h
    rcases ht with rfl | rfl
    · simp only [isDirectIface, tyTFlag, d3] at hd; exact absurd hd (by decide)
    · simp [isRegularMemory, tyTFlag, d5] at hreg

/-- `R0`'s interface switch: a case list of `ID`s takes case `0` exactly for `TD`. -/
theorem switchCase_R0 (t : Nat) (cs : List Nat) (hcs : ∀ c ∈ cs, c = ID) :
    switchCase R0 t cs = if t = TD ∧ cs ≠ [] then (0, TAB) else (cs.length, 0) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc : c = ID := hcs c (by simp)
    subst hc
    rw [switchCase_cons, ih fun c' h => hcs c' (by simp [h])]
    by_cases ht : t = TD
    · simp [ht]
    · simp [ht]

/-! ## The witness memory -/

/-- The non-zero bytes of the witness memory, as `(address, byte)`. -/
def wtable : List (Nat × Nat) :=
  [ -- TD: Size_ = 8, PtrBytes = 0, TFlag = TFlagRegularMemory
    (TD, 8), (TD + 20, 8),
    -- ID: Size_ = 8, len(Methods) = 1
    (ID, 8), (ID + 64, 1),
    -- TAB: Inter = ID = 0x10100, Type = TD = 0x10000
    (TAB + 1, 0x01), (TAB + 2, 0x01), (TAB + 10, 0x01),
    -- DTA: Cache = TAC = 0x10400, Inter = ID = 0x10100, CanFail = 1
    (DTA + 1, 0x04), (DTA + 2, 0x01), (DTA + 9, 0x01), (DTA + 10, 0x01), (DTA + 16, 1),
    -- DIS: Cache = ISC = 0x10500, NCases = 1, Cases[0] = ID = 0x10100
    (DIS + 1, 0x05), (DIS + 2, 0x01), (DIS + 8, 1), (DIS + 17, 0x01), (DIS + 18, 0x01),
    -- VAL: the value 42
    (VAL, 42) ]

/-- The witness memory: the bytes of `wtable` (zero elsewhere) in the regions: model metadata
(read-only), model heap, user data, stack, goroutine (read-only). -/
def wmem : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((wtable.lookup a).getD 0),
    [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨0x30000, 0x1000, true⟩,
     ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

/-- The witness stack pointer. -/
def wsp : Nat := 0x48000
/-- The witness goroutine. -/
def wg : Nat := 0x50000
/-- The witness return address. -/
def wret : Nat := 0x200000

theorem wmem_env (g : W64) : Env0 wmem g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem wmem_taDesc : TADescOK R0 wmem DTA := by
  refine ⟨by decide, by decide, by decide, by simp only [R0_isInter, taInter]; decide, ?_⟩
  show TACacheOK R0 wmem (wmem.readLE DTA 8) (taInter wmem DTA)
  rw [show wmem.readLE DTA 8 = TAC by decide]
  exact TACacheOK.empty (by decide) (by decide) (inPriv (by decide) (by decide)) (by decide) (by decide)

theorem wmem_isDesc : ISDescOK R0 wmem DIS [ID] := by
  refine ⟨by decide, by decide, by decide, by decide, fun i hi => ?_, by simp, ?_⟩
  · simp at hi; subst hi; show wmem.readLE (DIS + 16) 8 = ID; decide
  · rw [show wmem.readLE DIS 8 = ISC by decide]
    exact ISCacheOK.empty (by decide) (by decide) (inPriv (by decide) (by decide)) (by decide) (by decide)

/-! ## The environment under stores -/

/-- A writable range is readable. -/
theorem acc_read_of_write {m : Memory} {a n : Nat} (h : m.accessible a n true = true) :
    m.accessible a n false = true := by
  obtain ⟨⟨r, hr, h1, h2, h3, -⟩, -⟩ := (Memory.accessible_iff m a n true).1 h
  exact Memory.accessible_of_mem m hr h1 h2 h3

/-- A store outside the model's metadata `[0x10000, 0x10300)` keeps the environment. -/
theorem Env0.writeLE {m : Memory} {g : W64} (h : Env0 m g) {a n : Nat} (v : Nat)
    (ha : 0x10300 ≤ a ∨ a + n ≤ 0x10000) : Env0 (m.writeLE a n v) g := by
  obtain ⟨h1, h2, d1, d2, d3, d4, d5, d6, d7, d8⟩ := h
  have hr : ∀ b k, 0x10000 ≤ b → b + k ≤ 0x10300 → (m.writeLE a n v).readLE b k = m.readLE b k :=
    fun b k hb1 hb2 => Memory.readLE_writeLE_of_disjoint m v (by omega)
  refine ⟨by rw [Memory.accessible_writeLE]; exact h1, by rw [Memory.accessible_writeLE]; exact h2,
    (hr TD 8 (by simp [TD]) (by simp [TD])).trans d1,
    (hr (TD + 8) 8 (by simp [TD]) (by simp [TD])).trans d2,
    (hr (TD + 20) 1 (by simp [TD]) (by simp [TD])).trans d3,
    (hr ID 8 (by simp [ID]) (by simp [ID])).trans d4,
    (hr (ID + 20) 1 (by simp [ID]) (by simp [ID])).trans d5,
    (hr (ID + 64) 8 (by simp [ID]) (by simp [ID])).trans d6,
    (hr TAB 8 (by simp [TAB]) (by simp [TAB])).trans d7,
    (hr (TAB + 8) 8 (by simp [TAB]) (by simp [TAB])).trans d8⟩

/-! ## Bytes of a store, read back -/

theorem bytes_writeLE_self (m : Memory) (a n v i : Nat) (hi : i < n) :
    (m.writeLE a n v).bytes (a + i) = BitVec.ofNat 8 (v / 256 ^ i) := by
  simp only [Memory.writeLE]
  rw [ite_eq_left ⟨by omega, by omega⟩, show a + i - a = i by omega]

theorem byte_of_readLE (m : Memory) : ∀ (n b i : Nat), i < n →
    BitVec.ofNat 8 (m.readLE b n / 256 ^ i) = m.bytes (b + i)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, b, 0, _ => by
    apply BitVec.eq_of_toNat_eq
    rw [Memory.readLE, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one, Nat.add_zero]
    have := (m.bytes b).isLt
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this, Nat.add_zero]
  | n + 1, b, i + 1, h => by
    rw [show b + (i + 1) = b + 1 + i by omega, ← byte_of_readLE m n (b + 1) i (by omega),
      Memory.readLE, Nat.pow_succ, Nat.mul_comm (256 ^ i), ← Nat.div_div_eq_div_mul]
    congr 2
    have := (m.bytes b).isLt
    omega

/-- A store of a copy of `n` bytes, read back byte by byte. -/
theorem bytes_writeLE_readLE (m : Memory) (a b n i : Nat) (hi : i < n) :
    (m.writeLE a n (m.readLE b n)).bytes (a + i) = m.bytes (b + i) := by
  rw [bytes_writeLE_self _ _ _ _ _ hi, byte_of_readLE _ _ _ _ hi]

end Janus.Contracts.IfaceModel

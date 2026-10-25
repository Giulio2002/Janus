import Janus.Contracts.Hash
import Janus.Contracts.HashAmd64
import Janus.Contracts.IfaceModel

/-!
# Models of the equality, hashing and typed-memory runtime, for the non-vacuity of its contracts

The contracts of `Janus.Contracts.Mem`, `Janus.Contracts.Hash` (and their amd64 counterparts)
are hypotheses of the theorems that use them. A hypothesis no code can satisfy would make such a
theorem vacuous, so every contract comes with a proof that it **is** satisfiable
(`Janus.Contracts.MemSat`, `Janus.Contracts.HashSat`, `…Amd64`): a model that satisfies the laws,
machine code that satisfies the contract for it, and a call state that satisfies the contract's
precondition.

The models are small worlds, not descriptions of the Go runtime:

* `M0 : MemModel`: no private memory, an environment that always holds;
* `H0 : HashModel`: every byte hash returns its seed (`mem h n v = h`), `typehash` of the one
  hashable type `TD` (the 8-byte, pointer-free, `TFlagRegularMemory` type of
  `Janus.Contracts.IfaceModel`, whose `Equal` word is set here) returns its seed as well; its
  environment is `IfaceModel.Env0` with that `Equal` word, and its private memory is the model
  runtime range `[0x10000, 0x11000)`;
* the interface contracts use `IfaceModel.R0`.

The witness memory `wmem` extends `IfaceModel.wmem` with the inputs the contracts read: the
value `VAL` (42, from `IfaceModel`), a string header `STR` (`VAL`, length 8), an `any` value `EFV
= (TD, VAL)`, a non-empty interface value `IFV = (TAB, VAL)`, the write-barrier flag `WB` (off),
a `memequal_varlen`/`memhash_varlen` closure `VLEN` (size 8) and a 64-byte destination `DST`.
-/

namespace Janus.Contracts.EqHashModel

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Spec.Type Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash Janus.Contracts.IfaceModel

/-! ## Addresses (user data, besides `IfaceModel`'s `DTA`, `DIS`, `VAL`) -/

/-- A string header `(VAL, 8)`. -/
def STR : Nat := 0x30300
/-- An `any` value `(TD, VAL)`. -/
def EFV : Nat := 0x30400
/-- A non-empty interface value `(TAB, VAL)`. -/
def IFV : Nat := 0x30500
/-- The write-barrier flag word (zero: off). -/
def WB : Nat := 0x30600
/-- A funcval `(0, 8)`: a `memequal_varlen` / `memhash_varlen` closure of size 8. -/
def VLEN : Nat := 0x30700
/-- A 64-byte destination. -/
def DST : Nat := 0x30800

/-! ## The models -/

/-- The typed-memory model: no private memory, an environment that always holds. -/
def M0 : MemModel where
  Env _ _ := True
  priv := []

theorem M0_laws : M0.Laws := ⟨fun _ _ _ _ _ => trivial⟩

/-- The hashing model's environment: `IfaceModel.Env0` and `TD`'s `Equal` word non-zero. -/
def HEnv0 (m : Memory) (g : W64) : Prop := Env0 m g ∧ m.readLE (TD + 24) 8 = 1

/-- The hashing model: every hash is its seed (see the module documentation). -/
def H0 : HashModel where
  mem h _ _ := h % 2 ^ 64
  mem32 h _ := h % 2 ^ 64
  mem64 h _ := h % 2 ^ 64
  TypeHash _ _ _ h r := r = h % 2 ^ 64
  Hashable t _ _ := t = TD
  Env := HEnv0
  priv := [(0x10000, 0x11000)]

@[simp] theorem H0_mem (h n v : Nat) : H0.mem h n v = h % 2 ^ 64 := rfl
@[simp] theorem H0_mem32 (h v : Nat) : H0.mem32 h v = h % 2 ^ 64 := rfl
@[simp] theorem H0_mem64 (h v : Nat) : H0.mem64 h v = h % 2 ^ 64 := rfl
@[simp] theorem H0_typeHash (t : Nat) (m : Memory) (p h r : Nat) :
    H0.TypeHash t m p h r = (r = h % 2 ^ 64) := rfl
@[simp] theorem H0_hashable (t : Nat) (m : Memory) (p : Nat) : H0.Hashable t m p = (t = TD) := rfl
@[simp] theorem H0_env (m : Memory) (g : W64) : H0.Env m g = HEnv0 m g := rfl
@[simp] theorem H0_priv : H0.priv = [(0x10000, 0x11000)] := rfl

theorem H0_laws : H0.Laws where
  mem_lt h _ _ := Nat.mod_lt _ (by decide)
  mem32_lt h _ := Nat.mod_lt _ (by decide)
  mem64_lt h _ := Nat.mod_lt _ (by decide)
  env_frame m m' g h ha := by
    obtain ⟨he, h24⟩ := h
    exact ⟨R0_laws.env_frame m m' g he ha,
      (ha.readLE (inPriv (by simp [TD]) (by simp [TD]))).trans h24⟩
  type_desc m g t p h ht := by
    obtain ⟨⟨h1, -, -⟩, h24⟩ := h
    simp only [H0_hashable] at ht
    subst ht
    refine ⟨by decide, by decide, Memory.accessible_mono _ h1 (by decide) (by decide),
      inPriv (by decide) (by decide), ?_⟩
    simp only [tyEqual, h24]; decide
  regular m g t p h r _ _ _ := by
    simp only [H0_typeHash, HashModel.regHash, H0_mem, H0_mem32, H0_mem64]
    split
    · exact Iff.rfl
    · split <;> exact Iff.rfl

/-! ## The witness memory -/

/-- The non-zero bytes of the witness memory: `IfaceModel.wtable`, `TD.Equal = 1`, and the
inputs. -/
def wtable : List (Nat × Nat) :=
  IfaceModel.wtable ++
  [ -- TD.Equal = 1
    (TD + 24, 1),
    -- STR: ptr = VAL = 0x30200, len = 8
    (STR + 1, 0x02), (STR + 2, 0x03), (STR + 8, 8),
    -- EFV: type = TD = 0x10000, data = VAL = 0x30200
    (EFV + 2, 0x01), (EFV + 9, 0x02), (EFV + 10, 0x03),
    -- IFV: itab = TAB = 0x10200, data = VAL
    (IFV + 1, 0x02), (IFV + 2, 0x01), (IFV + 9, 0x02), (IFV + 10, 0x03),
    -- VLEN: code word 0, size 8
    (VLEN + 8, 8) ]

/-- The witness memory: the bytes of `wtable` (zero elsewhere) in `IfaceModel.wmem`'s regions:
model metadata (read-only), model heap, user data, stack, goroutine (read-only). -/
def wmem : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((wtable.lookup a).getD 0), IfaceModel.wmem.regions⟩

theorem wmem_regions : wmem.regions =
    [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨0x30000, 0x1000, true⟩,
     ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩] := rfl

theorem wmem_env0 (g : W64) : Env0 wmem g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem wmem_henv (g : W64) : HEnv0 wmem g := ⟨wmem_env0 g, by decide⟩

theorem wmem_wbOff : WriteBarrierOff wmem WB := by unfold WriteBarrierOff; decide

end Janus.Contracts.EqHashModel

/-! ## Moving a proved implementation into another program

A satisfiability proof runs a model implementation in a program of its own (`IfaceSat.withCode`).
A witness for an example's theorem needs the same implementation at the contract's address in
the example's linked program. `Summary.of_codeIn` moves the `Summary`: a run only reads the
program at the addresses it executes, so a program `P` that has the same instruction wherever `p`
has one (and no stub and not its exit address there) runs every `p`-run alike (`CodeIn`). For a
single-segment `p` and `P = Q.link [seg]` that follows from `Q` having nothing at the segment's
addresses (`codeIn_link`, decided by the kernel for a concrete `Q`). -/

namespace Janus.Contracts.EqHashModel

section Arm64
open Janus Janus.Arm64 Janus.Tactic

/-- `P` has `p`'s instructions (see the section comment). -/
def CodeIn (p P : Program) : Prop :=
  ∀ pc w, p.fetch pc = some w → P.fetch pc = some w ∧ P.stubAt pc = none ∧ pc ≠ P.exitAddr

theorem Steps.of_codeIn {p P : Program} (hc : CodeIn p P) {s s' : State} {k : Nat}
    (h : Program.Steps p s k s') : Program.Steps P s k s' := by
  induction h with
  | refl => exact .refl _
  | step _ _ hf hst _ ih =>
    obtain ⟨hf', hs', hx'⟩ := hc _ _ hf
    exact .step hx' hs' hf' hst ih

theorem Summary.of_codeIn {p P : Program} (hc : CodeIn p P) {a : Nat} {pre : State → Prop}
    {post : State → State → Prop} (h : Summary p a pre post) : Summary P a pre post := by
  intro s hpc hpre
  obtain ⟨k, s', hst, hret, hq⟩ := h s hpc hpre
  exact ⟨k, s', Steps.of_codeIn hc hst, hret, hq⟩

theorem fetchIn_append_none {l₁ : List Segment} (l₂ : List Segment) {pc : Nat}
    (h : Program.fetchIn l₁ pc = none) : Program.fetchIn (l₁ ++ l₂) pc = Program.fetchIn l₂ pc := by
  induction l₁ with
  | nil => rfl
  | cons seg rest ih =>
    simp only [List.cons_append, Program.fetchIn] at h ⊢
    split
    · rename_i hc
      rw [if_pos hc] at h
      split
      · rename_i w hw; rw [hw] at h; cases h
      · rename_i hw; rw [hw] at h; exact ih h
    · rename_i hc; rw [if_neg hc] at h; exact ih h

theorem fetchIn_single_some {seg : Segment} {pc w : Nat} (h : Program.fetchIn [seg] pc = some w) :
    ∃ i, i < seg.words.length ∧ pc = seg.base + 4 * i := by
  simp only [Program.fetchIn] at h
  split at h
  · rename_i hc
    split at h
    · rename_i w' hw
      refine ⟨(pc - seg.base) / 4, ?_, by omega⟩
      exact (List.getElem?_eq_some_iff.1 hw).1
    · cases h
  · cases h

/-- The single-segment program of `seg`. -/
def segProg (seg : Segment) : Program := { segments := [seg], stubs := [], exitAddr := 0 }

/-- `Q.link [seg]` has the instructions of `segProg seg` when `Q` has no code, no stub and not
its exit address at the segment's words. -/
theorem codeIn_link (Q : Program) (seg : Segment)
    (h : ∀ i < seg.words.length, Q.fetch (seg.base + 4 * i) = none ∧
      Q.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ Q.exitAddr) :
    CodeIn (segProg seg) (Q.link [seg]) := by
  intro pc w hf
  obtain ⟨i, hi, rfl⟩ := fetchIn_single_some hf
  obtain ⟨h1, h2, h3⟩ := h i hi
  refine ⟨?_, by simpa using h2, by simpa using h3⟩
  show Program.fetchIn (Q.segments ++ [seg]) _ = _
  rw [fetchIn_append_none _ h1]; exact hf

end Arm64

section Amd64
open Janus.Amd64 Janus.Amd64.Tactic

/-- `P` has `p`'s instructions (amd64). -/
def CodeIn64 (p P : Janus.Amd64.Program) : Prop :=
  ∀ pc w, p.fetch pc = some w → P.fetch pc = some w ∧ P.stubAt pc = none ∧ pc ≠ P.exitAddr

theorem Steps.of_codeIn64 {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {s s' : State} {k : Nat}
    (h : Janus.Amd64.Program.Steps p s k s') : Janus.Amd64.Program.Steps P s k s' := by
  induction h with
  | refl => exact .refl _
  | step _ _ hf hst _ ih =>
    obtain ⟨hf', hs', hx'⟩ := hc _ _ hf
    exact .step hx' hs' hf' hst ih

theorem Summary.of_codeIn64 {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {a : Nat}
    {pre : State → Prop} {post : State → State → Prop} (h : Summary p a pre post) :
    Summary P a pre post := by
  intro s hpc hpre
  obtain ⟨k, s', hst, hret, hq⟩ := h s hpc hpre
  exact ⟨k, s', Steps.of_codeIn64 hc hst, hret, hq⟩

theorem fetchIn_append_none64 {l₁ : List Janus.Amd64.Segment} (l₂ : List Janus.Amd64.Segment)
    {pc : Nat} (h : Janus.Amd64.Program.fetchIn l₁ pc = none) :
    Janus.Amd64.Program.fetchIn (l₁ ++ l₂) pc = Janus.Amd64.Program.fetchIn l₂ pc := by
  induction l₁ with
  | nil => rfl
  | cons seg rest ih =>
    simp only [List.cons_append, Janus.Amd64.Program.fetchIn] at h ⊢
    split
    · rename_i hc; rw [if_pos hc] at h; cases h
    · rename_i hc; rw [if_neg hc] at h; exact ih h

/-- The single-segment program of `seg` (amd64). -/
def segProg64 (seg : Janus.Amd64.Segment) : Janus.Amd64.Program :=
  { segments := [seg], stubs := [], exitAddr := 0 }

/-- `Q.link [seg]` has the instructions of `segProg64 seg` when `Q` has no code, no stub and not
its exit address at the segment's bytes (amd64). -/
theorem codeIn_link64 (Q : Janus.Amd64.Program) (seg : Janus.Amd64.Segment)
    (h : ∀ i < seg.bytes.length, Q.fetch (seg.base + i) = none ∧
      Q.stubAt (seg.base + i) = none ∧ seg.base + i ≠ Q.exitAddr) :
    CodeIn64 (segProg64 seg) (Q.link [seg]) := by
  intro pc w hf
  have hr : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length := by
    simp only [segProg64, Janus.Amd64.Program.fetch, Janus.Amd64.Program.fetchIn] at hf
    split at hf
    · assumption
    · cases hf
  obtain ⟨h1, h2, h3⟩ := h (pc - seg.base) (by omega)
  rw [show seg.base + (pc - seg.base) = pc by omega] at h1 h2 h3
  refine ⟨?_, by simpa using h2, by simpa using h3⟩
  show Janus.Amd64.Program.fetchIn (Q.segments ++ [seg]) _ = _
  rw [fetchIn_append_none64 _ h1]; exact hf

end Amd64

end Janus.Contracts.EqHashModel

namespace Janus.Contracts.EqHashModel

open Janus Janus.Arm64 Janus.Contracts.Mem Janus.Contracts.IfaceModel

/-- The amd64 witness memory: `wmem` with the witness return address `wret = 0x200000` in the
word at `[RSP] = [wsp]` (where a `CALL` put it). -/
def wmem64 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((wsp + 2, 0x20) :: wtable).lookup a).getD 0), IfaceModel.wmem.regions⟩

theorem wmem64_ret : wmem64.readLE wsp 8 = wret := by decide

theorem wmem64_env0 (g : W64) : Env0 wmem64 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem wmem64_henv (g : W64) : HEnv0 wmem64 g := ⟨wmem64_env0 g, by decide⟩

theorem wmem64_wbOff : WriteBarrierOff wmem64 WB := by unfold WriteBarrierOff; decide

end Janus.Contracts.EqHashModel

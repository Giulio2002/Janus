import Extracted

/-!
# `CountKeys(m)` returns `len(m)` (arm64)

**Guarantee.** For every representation `M` of maps satisfying the layout laws `M.Laws`, every
map value `m` holding the abstract map `f` (`IsMap`: nil and empty, or represented by `M`)
and every Go call state, the call returns (never faulting) and its result is the number of keys
of `f` (the length of any listing of them). No runtime function is called: `len(m)` compiles to
`0` for a nil map and otherwise a load of the header's first word (`Map.used`), which the law
`MapModel.Laws.len` says is the number of entries.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map

namespace Proof

theorem correctness {V : Type} (M : MapModel (BitVec 64) V) (hl : M.Laws)
    (m : BitVec 64) (f : AMap (BitVec 64) V) :
    Ensures Extracted.program Extracted.entry [m]
      (fun s => IsMap M s.mem m.toNat f)
      (fun _ s' => ∀ ks, Keys f ks → (s'.regs 0).toNat = ks.length) := by
  intro ret hret s hs hmap
  janus_intro hs
  by_cases h0 : m.toNat = 0
  · have hf : f = AMap.empty := by unfold IsMap at hmap; simpa [h0] using hmap
    subst hf
    janus_run
    intro ks hks; rw [hks.eq_nil_of_empty]; rfl
  · have hrep := (isMap_of_ne h0).1 hmap
    obtain ⟨hacc, hbnd, hlen⟩ := hl.len _ _ _ hrep
    janus_run
    intro ks hks; rw [hlen ks hks]


namespace Witness

open Janus.Contracts.MapModel0

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000


def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

theorem hpre : IsMap (ME (BitVec 64)) s0.mem (0 : BitVec 64).toNat emp := by
  simp [IsMap, emp]

/-- All hypotheses of `correctness` hold together at a concrete call: a nil map (the model `ME`, the empty map). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64), (ME (BitVec 64)).Laws ∧ RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s ∧
    (IsMap (ME (BitVec 64)) s.mem m.toNat emp) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (∀ ks, Keys emp ks → (s'.regs 0).toNat = ks.length)) :=
  ⟨ret, s0, 0, ME_laws _, hret, setup, hpre,
    correctness (ME (BitVec 64)) (ME_laws _) 0 emp ret hret s0 setup hpre⟩

end Witness

end Proof

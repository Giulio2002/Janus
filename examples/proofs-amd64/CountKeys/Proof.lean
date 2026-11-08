import Janus
import Extracted

/-!
# `CountKeys(m)` returns `len(m)` (amd64)

**Guarantee.** For every representation `M` of maps satisfying the layout laws `M.Laws`, every
map value `m` holding the abstract map `f` (`IsMap`: nil and empty, or represented by `M`) and `[RSP, RSP + 8)` readable (`RET`)
and every Go call state, the call returns (never faulting) and its result is the number of keys
of `f` (the length of any listing of them). No runtime function is called: `len(m)` compiles to
`0` for a nil map and otherwise a load of the header's first word (`Map.used`), which the law
`MapModel.Laws.len` says is the number of entries.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map

namespace Proof

theorem correctness {V : Type} (M : MapModel (BitVec 64) V) (hl : M.Laws)
    (m : BitVec 64) (f : AMap (BitVec 64) V) :
    Ensures Extracted.program Extracted.entry [m]
      (fun s => StackWritable s 0 8 ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => ∀ ks, Keys f ks → (s'.regs 0).toNat = ks.length) := by
  intro ret hret s hs ⟨⟨_, hb, hst⟩, hmap⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hb hst
  by_cases h0 : m.toNat = 0
  · have hf : f = AMap.empty := by unfold IsMap at hmap; simpa [h0] using hmap
    subst hf
    janus64_run
    intro ks hks; rw [hks.eq_nil_of_empty]; rfl
  · have hrep := (isMap_of_ne h0).1 hmap
    obtain ⟨hacc, hbnd, hlen⟩ := hl.len _ _ _ hrep
    janus64_run
    intro ks hks; rw [hlen ks hks]

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The nil map, holding the empty abstract map. -/
def m : BitVec 64 := 0#64
def f : AMap (BitVec 64) (BitVec 64) := AMap.empty

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then m else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ IsMap (ME (BitVec 64)) s0.mem m.toNat f :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold IsMap; simp [m]; rfl⟩

/-- All hypotheses of `correctness` hold together (the nil map, empty). -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (M : MapModel (BitVec 64) (BitVec 64)) (m : BitVec 64), M.Laws ∧ RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s ∧
    (StackWritable s 0 8 ∧ IsMap M s.mem m.toNat Witness.f) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∀ ks : List (BitVec 64), Keys Witness.f ks → (s'.regs 0).toNat = ks.length) :=
  ⟨ret, s0, ME (BitVec 64), m, ME_laws _, hret, setup, hpre,
    correctness (ME (BitVec 64)) (ME_laws _) m f ret hret s0 setup hpre⟩

end Witness

end Proof

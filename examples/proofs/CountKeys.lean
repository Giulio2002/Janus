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

end Proof

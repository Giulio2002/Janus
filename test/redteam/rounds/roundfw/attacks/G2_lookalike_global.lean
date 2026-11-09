import Extracted

/-! Attack (G2_lookalike_global): a precondition that names a global the extraction does not record.
`GlobalsInit` is then unsatisfiable, so any conclusion follows (here `False`), while the
statement reads as a claim about `karatsubaCut`. janus-audit must reject the name. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => GlobalsInit Extracted.program.globals s.mem ["example.com/basic.kаratsubaCut"])
      (fun _ _ => False) := by
  intro ret hret s hs h
  exfalso
  obtain ⟨g, hg, -⟩ := h _ (List.mem_singleton_self _)
  have hn : globalNamed Extracted.program.globals "example.com/basic.kаratsubaCut" = none := by decide
  rw [hn] at hg
  cases hg

end Proof

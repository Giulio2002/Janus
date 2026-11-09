import Extracted
import Janus.Backdoor

/-! R1 `inject` / `inject-dep`: a statement built on an injected `Janus.*` module, which the
auditor would treat as trusted framework code. -/

theorem R1.Inject.claim : Janus.Backdoor.Holds ∧ Extracted.entry = Extracted.entry := ⟨trivial, rfl⟩

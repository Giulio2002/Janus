import Janus.Tactic.Attr
import Janus.Tactic.Basic
import Janus.Tactic.Data
import Janus.Tactic.Core
import Janus.Tactic.Common
import Janus.Tactic.Disasm

/-!
# Janus proof automation

See `docs/PROOFS.md`. Entry points: `janus_intro`, `janus_run`, `janus_step`, `janus_disch`, `janus_frame`
(`Janus.Tactic.Core`), the goal predicates `Reaches`, `ReachesRet`, `Summary`
(`Janus.Tactic.Basic`), and the spec vocabulary in `Janus.Spec`.
-/

import Janus.Tactic.Attr
import Janus.Tactic.Basic
import Janus.Tactic.Data
import Janus.Tactic.Core
import Janus.Tactic.Common
import Janus.Tactic.Disasm
import Janus.Tactic.Ring
import Janus.Tactic.Carry
import Janus.Tactic.RingTac
import Janus.Tactic.Recursion

/-!
# Janus proof automation

See `docs/PROOFS.md`. Entry points: `janus_intro`, `janus_run`, `janus_step`, `janus_disch`, `janus_frame`
(`Janus.Tactic.Core`), the goal predicates `Reaches`, `ReachesRet`, `Summary`
(`Janus.Tactic.Basic`), and the spec vocabulary in `Janus.Spec`.
-/

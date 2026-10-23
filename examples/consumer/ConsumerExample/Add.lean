import Extracted
import ConsumerExample.Spec

/-!
# `example.com/basic.Add` computes `addSpec`

Verify against an extraction of `example.com/basic.Add` (see README.md).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace ConsumerExample.Add

theorem correctness : Computes Extracted.program Extracted.entry addSpec := by
  intro x y ret hret s hs _
  janus_intro hs
  janus_run [addSpec]

end ConsumerExample.Add

import Extracted
/-! ATTACK A9: inside `namespace Proof`, `Extracted.program` resolves to `Proof.Extracted.program`
(a fake program that "returns" immediately because its exitAddr is the entry). The verifier's
"mentions Extracted." warning stays silent. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
def Extracted.program : Program := { segments := [], stubs := [], exitAddr := _root_.Extracted.entry }
-- Ported to the RetAddr form of `Ensures` (F4 makes the original "exitAddr := entry returns at
-- once" proof impossible). The shadow is the point: inside `namespace Proof`, `Extracted.program`
-- below resolves to `Proof.Extracted.program`, a definition the proof controls.
theorem correctness : Extracted.program.exitAddr = _root_.Extracted.entry := rfl
end Proof

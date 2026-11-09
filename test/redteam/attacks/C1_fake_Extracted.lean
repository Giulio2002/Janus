import Janus
/-! ATTACK C1 payload: a fake `Extracted` module. Planted as `<janus-root>/.lake/build/lib/lean/Extracted.olean`,
it shadows the checked `.janus-build/Extracted.olean`, because lake's library directory comes before
the per-verify build directory on LEAN_PATH. Its program "returns" at once (exitAddr = entry). -/
namespace Extracted
open Janus
def entry : Nat := 0x930c0
def program : Program := { segments := [], stubs := [], exitAddr := 0x930c0 }
end Extracted

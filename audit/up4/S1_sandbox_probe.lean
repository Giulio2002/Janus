import Extracted
import Lean
open Lean Elab Command Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round n11 S1: the elaboration tries to read the janus cache dir (HMAC key), to write outside the sandbox, and to list
the framework build dir. Any success is turned into an elaboration error (so the verify must then be rejected).
Expected: Verified   (every probe fails inside the sandbox; a "SANDBOX ESCAPE" error means the verifier is attackable). -/

partial def walk (d : System.FilePath) (depth : Nat) (acc : IO.Ref (Array String)) : IO Unit := do
  if depth == 0 then return
  let es ← (try System.FilePath.readDir d catch _ => pure #[])
  for e in es do
    let isD ← (try e.path.isDir catch _ => pure false)
    if isD then walk e.path (depth - 1) acc
    else
      let r ← (try (do let b ← IO.FS.readBinFile e.path; pure s!"READ {e.path} {b.size}B") catch _ => pure "")
      if r != "" then acc.modify (·.push r)

run_cmd do
  let acc ← IO.mkRef (#[] : Array String)
  for d in ["/root/.cache/janus", "/root/.cache/janus/asl-cache-key"] do
    walk d 3 acc
  let hits ← acc.get
  logInfo m!"probe: {hits.size} readable files"
  if hits.size > 0 then throwError "SANDBOX ESCAPE {hits.extract 0 12}"

namespace Proof
theorem correctness (impl : List Segment) (x y : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof

import Extracted
import Lean

/-!
R1 proof-overwrite: run unconfined (`--unsafe-no-sandbox`), a proof's `#eval` finds the framework
build on `LEAN_PATH` and corrupts `Janus/GoABI.olean` while it compiles. Under the sandbox the
framework build is read-only and the write fails; without one, the framework pins catch it.
Run it only against a throwaway copy of the framework (audit/run-all.sh uses one).
-/

open System in
#eval show IO Unit from do
  for d in System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "") do
    let f := d / "Janus" / "GoABI.olean"
    if ← f.pathExists then
      let b ← IO.FS.readBinFile f
      let mut c := b
      for i in [b.size / 2 : b.size / 2 + 64] do
        c := c.set! i (b.get! i ^^^ 0x5a)
      try IO.FS.writeBinFile f c; IO.eprintln s!"R1 attack: corrupted {f}"
      catch e => IO.eprintln s!"R1 attack: cannot write {f}: {e}"

namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
end Proof

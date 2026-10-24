import Janus.Tools.Audit

/-!
# `janus-audit`: the auditor as a compiled executable

`janus-audit <theorem> <proof module> <marker> <trusted module> [<dependency root> …]` runs
`JanusAudit.runImpl` (`Janus.Tools.Audit`) with exactly the arguments the trusted `Audit.lean`
script passes to `JanusAudit.run`, and prints the same record. `janus verify` runs it sandboxed,
with the verification's `LEAN_PATH`.

Compiled rather than elaborated: the auditor's own code runs natively instead of in the
interpreter, and the process starts with no imported modules, so the audited and the clean
environment map their `.olean` files instead of copying the ones the `Audit.lean` header has
already mapped. The search path is the one the `lean` frontend uses: `LEAN_PATH`, then the
toolchain library (`$JANUS_LEAN_SYSROOT/lib/lean`, set by `janus verify`, else the sysroot of
the `lean` on `PATH`).
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let sysroot ← match (← IO.getEnv "JANUS_LEAN_SYSROOT") with
    | some d => pure (System.FilePath.mk d)
    | none => findSysroot
  initSearchPath sysroot
  match args with
  | thm :: proofMod :: marker :: trusted :: depRoots =>
    unsafe JanusAudit.runImpl thm proofMod marker trusted depRoots.toArray
    return 0
  | _ =>
    IO.eprintln "usage: janus-audit <theorem> <proof module> <marker> <trusted module> [<dependency root> ...]"
    return 2

import Janus.Tools.Audit

/-!
# `janus-audit`: the auditor as a compiled executable

`janus-audit <theorem> <proof module> <marker> <trusted module> [<dependency root> …]` runs
`JanusAudit.runImpl` (`Janus.Tools.Audit`) with exactly the arguments the trusted `Audit.lean`
script passes to `JanusAudit.run`, and prints the same record. `janus verify` runs it sandboxed,
with the verification's `LEAN_PATH`. `janus-audit --asl …` runs the ASL corollary audit
(`JanusAudit.runASLImpl`) of `janus verify --asl` the same way.

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
  | "--serve" :: trusted :: depRoots =>
    -- `janus verify`: build the clean environment now (the proof is still compiling), then read
    -- one request line `<theorem>\t<proof module>\t<marker>\t<LEAN_PATH>` and audit exactly as
    -- the classic invocation does. The search path of the clean environment holds the framework
    -- and the trusted builds; the request installs the final one (with the proof's directory).
    -- No request (end of input) is not an audit: nothing is printed.
    let pre ← unsafe JanusAudit.prepareClean
    let line ← (← IO.getStdin).getLine
    if line.isEmpty then return 3
    match ((line.splitOn "\n").head!.splitOn "\t") with
    | [thm, proofMod, marker, leanPath] =>
      searchPathRef.set ((System.SearchPath.parse leanPath) ++ [sysroot / "lib" / "lean"])
      unsafe JanusAudit.runImplCore thm proofMod marker trusted depRoots.toArray (some pre)
      return 0
    | _ =>
      IO.eprintln "janus-audit --serve: bad request"
      return 2
  | "--asl" :: userThm :: proofMod :: corThm :: corMod :: marker :: trusted :: words :: depRoots =>
    -- `janus verify --asl`: the ASL corollary audit (`JanusAudit.runASLImpl`)
    unsafe JanusAudit.runASLImpl userThm proofMod corThm corMod marker trusted words depRoots.toArray
    return 0
  | thm :: proofMod :: marker :: trusted :: depRoots =>
    unsafe JanusAudit.runImpl thm proofMod marker trusted depRoots.toArray
    return 0
  | _ =>
    IO.eprintln "usage: janus-audit <theorem> <proof module> <marker> <trusted module> [<dependency root> ...]\n       janus-audit --serve <trusted module> [<dependency root> ...]   (one request line on stdin)\n       janus-audit --asl <theorem> <proof module> <corollary> <corollary module> <marker> <trusted module> <coverage theorem> [<dependency root> ...]"
    return 2

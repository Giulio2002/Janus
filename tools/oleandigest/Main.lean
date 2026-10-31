import Lean
open Lean

/-!
# `janus-olean-digest`: strip the message log from compiled Lean modules (scripts/gate-cachecmp.py, docs/TESTING.md)

    janus-olean-digest OUTDIR OLEAN...

A `.olean` is one compacted object graph. Lean 4.34 stores the module's message log (the linter warnings,
`Lean.Linter.lintLogExt`) in it together with the ABSOLUTE source path, so the same module built in two directories differs in
bytes though every declaration is the same. For each argument this tool loads the module, removes every entry array of that one
extension, re-serializes the rest with Lean's own `saveModuleData` into `OUTDIR/<i>.stripped` (a fresh compaction: its bytes do
not depend on the original's layout) and prints one tab-separated line

    <i> <olean path> <original size> <re-serialization size of the UNSTRIPPED module> <message-log entries> <stripped size>

The caller (gate-cachecmp.py) takes the SHA-256 of the stripped file (the whole file: header, every constant, every other
extension's entries, the compiled code), and checks that the original has no bytes the module data does not account for
(original size = unstripped re-serialization size, same header). Nothing is parsed by name here, so no name needs framing.
Any failure to read or write a module is an error message on stderr and a non-zero exit (the caller fails closed).
-/

def lintExt : Name := `Lean.Linter.lintLogExt

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | [_] => do IO.eprintln "usage: janus-olean-digest OUTDIR OLEAN..."; return 2
  | outdir :: files => do
    let mut rc : UInt32 := 0
    let mut i := 0
    for p in files do
      try
        let (md, _) ← readModuleData p
        let sz := (← System.FilePath.metadata p).byteSize.toNat
        let full := System.FilePath.mk outdir / s!"{i}.full"
        saveModuleData full `JanusOleanDigest md
        let fullSz := (← System.FilePath.metadata full).byteSize.toNat
        IO.FS.removeFile full
        let lint := md.entries.foldl (fun n (nm, es) => if nm == lintExt then n + es.size else n) 0
        let stripped : ModuleData := { md with entries := md.entries.filter (fun (nm, _) => nm != lintExt) }
        let out := System.FilePath.mk outdir / s!"{i}.stripped"
        saveModuleData out `JanusOleanDigest stripped
        let strSz := (← System.FilePath.metadata out).byteSize.toNat
        IO.println s!"{i}\t{p}\t{sz}\t{fullSz}\t{lint}\t{strSz}"
      catch e =>
        IO.eprintln s!"janus-olean-digest: {p}: {e}"
        rc := 1
      i := i + 1
    return rc

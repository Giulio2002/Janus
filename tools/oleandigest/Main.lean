import Lean
open Lean

/-!
# `janus-olean-digest`: a layout-independent digest of compiled Lean modules (scripts/gate-cachecmp.py, docs/SOUNDNESS.md)

A `.olean` is one compacted object graph. Two builds of the same source in different directories differ in bytes (not in
content) because Lean 4.34 stores the module's message log (the linter warnings) in it together with the absolute source
path: the graph shifts after the string. This tool digests the CONTENT: for every `.olean` argument it re-serializes each
piece of the module separately with Lean's own `saveModuleData` into a scratch file (a fresh compaction of just that piece,
so its bytes do not depend on where the piece sat in the original file or on the other pieces) and hashes those bytes.
Pieces: `core` = imports, constant names, ALL constants (kind, name, universe parameters, type, value), extra constant
names; and one piece per environment extension entry array (`ext:<name>`: simp sets, instances, attributes, reducibility,
IR / compiled-code declarations, the message log, ...). Output, one line per piece:  `<olean> <piece> <digest> <bytes>`.
The digest is two independent 64-bit hashes of the piece's bytes (an equality check for two builds of one source, not a
collision-resistant commitment).
-/

def fnv (bs : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for b in bs do
    h := (h ^^^ b.toUInt64) * 1099511628211
  return h

def mix2 (bs : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0x9e3779b97f4a7c15
  for b in bs do
    h := mixHash h b.toUInt64
  return h

def pieceDigest (tmp : System.FilePath) (data : ModuleData) : IO (String × Nat) := do
  saveModuleData tmp `JanusOleanDigest data
  let bs ← IO.FS.readBinFile tmp
  IO.FS.removeFile tmp
  return (s!"{(fnv bs).toNat}-{(mix2 bs).toNat}", bs.size)

def main (args : List String) : IO UInt32 := do
  let mut rc : UInt32 := 0
  let tmp : System.FilePath := (← IO.currentDir) / s!".janus-olean-digest-{← IO.monoNanosNow}.tmp"
  for p in args do
    try
      let (md, _) ← readModuleData p
      let core : ModuleData := { md with entries := #[] }
      let (d, n) ← pieceDigest tmp core
      IO.println s!"{p} core {d} {n}"
      for (nm, es) in md.entries do
        let piece : ModuleData := { md with imports := #[], constNames := #[], constants := #[], extraConstNames := #[], entries := #[(nm, es)] }
        let (d, n) ← pieceDigest tmp piece
        IO.println s!"{p} ext:{nm} {d} {n}"
    catch e =>
      IO.eprintln s!"janus-olean-digest: {p}: {e}"
      rc := 1
  return rc

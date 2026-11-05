import Janus

/-! # Tree-shaped `Extracted` programs and the auditor's identity check (U-BIGEXTRACT)

A code segment, data object or global of more than 4096 elements is generated as a tree of definitions joined by `++`
(`def seg0_words_0 : List Nat := …`, `def seg0_words : List Nat := seg0_words_0 ++ …`, `segments := [seg0]`). The auditor
checks `Extracted.program` against the independently elaborated `JanusTrusted.program` with `Meta.isDefEq` (a
`checkIdentity`): that unfolds every chunk, so the chunks are covered through `program` with no extra check, and a
different chunk under the SAME name is a different value. These examples run that exact check on two trees:
equal content (even split differently) is defeq, any other content is not. -/

namespace JanusTests.ChunkIdentity

open Lean Meta

namespace TA
def seg0_words_0 : List Nat := [1, 2, 3]
def seg0_words_1 : List Nat := [4, 5]
def seg0_words : List Nat := seg0_words_0 ++ seg0_words_1
def seg0 : Janus.Segment := { name := "f", base := 0, words := seg0_words }
def program : Janus.Program := { segments := [seg0], stubs := [], exitAddr := 0 }
end TA

/- the same tree under another namespace (the trusted copy) -/
namespace TB
def seg0_words_0 : List Nat := [1, 2, 3]
def seg0_words_1 : List Nat := [4, 5]
def seg0_words : List Nat := seg0_words_0 ++ seg0_words_1
def seg0 : Janus.Segment := { name := "f", base := 0, words := seg0_words }
def program : Janus.Program := { segments := [seg0], stubs := [], exitAddr := 0 }
end TB

/- one chunk with another element, same names -/
namespace TC
def seg0_words_0 : List Nat := [1, 2, 3]
def seg0_words_1 : List Nat := [4, 6]
def seg0_words : List Nat := seg0_words_0 ++ seg0_words_1
def seg0 : Janus.Segment := { name := "f", base := 0, words := seg0_words }
def program : Janus.Program := { segments := [seg0], stubs := [], exitAddr := 0 }
end TC

/- the same value split into other chunks -/
namespace TD
def seg0_words_0 : List Nat := [1, 2]
def seg0_words_1 : List Nat := [3, 4, 5]
def seg0_words : List Nat := seg0_words_0 ++ seg0_words_1
def seg0 : Janus.Segment := { name := "f", base := 0, words := seg0_words }
def program : Janus.Program := { segments := [seg0], stubs := [], exitAddr := 0 }
end TD

/- a chunk dropped (a shorter tree) -/
namespace TE
def seg0_words_0 : List Nat := [1, 2, 3]
def seg0_words : List Nat := seg0_words_0
def seg0 : Janus.Segment := { name := "f", base := 0, words := seg0_words }
def program : Janus.Program := { segments := [seg0], stubs := [], exitAddr := 0 }
end TE

def same (a b : Name) : MetaM Bool := withNewMCtxDepth <| isDefEq (.const a []) (.const b [])

run_meta do
  unless ← same `JanusTests.ChunkIdentity.TA.program `JanusTests.ChunkIdentity.TB.program do
    throwError "identical trees must be defeq"
  unless !(← same `JanusTests.ChunkIdentity.TA.program `JanusTests.ChunkIdentity.TC.program) do
    throwError "a different element in a chunk of the same name must not be defeq"
  unless !(← same `JanusTests.ChunkIdentity.TA.program `JanusTests.ChunkIdentity.TE.program) do
    throwError "a dropped chunk must not be defeq"
  unless ← same `JanusTests.ChunkIdentity.TA.program `JanusTests.ChunkIdentity.TD.program do
    throwError "the same list split into other chunks is the same value"

end JanusTests.ChunkIdentity

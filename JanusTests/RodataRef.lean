import Janus

/-! U-RODATA-REF: the extractor now copies the bytes a copied string header points to (the "<nil>" of uint256's `Format`:
header at `.rodata+0x36190`, bytes at `0x4e5c16`), so they are part of `Program.data` and `DataLoaded` pins them. A consumer PROVES
them from the data and cannot assume different ones. Both ISAs. -/

namespace JanusTests.RodataRef

open Janus Janus.Spec

/-- the segment as `janus extract` emits it for the "<nil>" literal -/
def nilSeg : DataSegment := { name := ".rodata+0x2ac16", base := 0x4e5c16, bytes := [0x3c, 0x6e, 0x69, 0x6c, 0x3e] }

def p : Program := { segments := [], stubs := [], exitAddr := 0, data := [nilSeg] }
def q : Amd64.Program := { segments := [], stubs := [], exitAddr := 0, data := [nilSeg] }

theorem nil_bytes {m : Arm64.Memory} (h : p.DataLoaded m) : strBytes m 0x4e5c16 5 = [0x3c, 0x6e, 0x69, 0x6c, 0x3e] := by
  have hs := (h nilSeg (List.mem_singleton_self _)).2
  have h0 := hs 0 (by decide); have h1 := hs 1 (by decide); have h2 := hs 2 (by decide)
  have h3 := hs 3 (by decide); have h4 := hs 4 (by decide)
  simp only [nilSeg, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  simp_all [strBytes, List.range_succ, nilSeg]

theorem nil_bytes64 {m : Arm64.Memory} (h : q.DataLoaded m) : strBytes m 0x4e5c16 5 = [0x3c, 0x6e, 0x69, 0x6c, 0x3e] := by
  have hs := (h nilSeg (List.mem_singleton_self _)).2
  have h0 := hs 0 (by decide); have h1 := hs 1 (by decide); have h2 := hs 2 (by decide)
  have h3 := hs 3 (by decide); have h4 := hs 4 (by decide)
  simp only [nilSeg, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  simp_all [strBytes, List.range_succ, nilSeg]

/-- red team: a consumer cannot assume other bytes for the literal (an assumption `strBytes m litA 5 = "<xyz>"` contradicts
`DataLoaded`; before U-RODATA-REF the segment was missing and any such assumption was consistent). -/
theorem rt_other_bytes {m : Arm64.Memory} (h : p.DataLoaded m) : ¬ strBytes m 0x4e5c16 5 = [0x3c, 0x78, 0x79, 0x7a, 0x3e] := by
  rw [nil_bytes h]; decide

theorem rt_other_bytes64 {m : Arm64.Memory} (h : q.DataLoaded m) : ¬ strBytes m 0x4e5c16 5 = [0x3c, 0x78, 0x79, 0x7a, 0x3e] := by
  rw [nil_bytes64 h]; decide

end JanusTests.RodataRef

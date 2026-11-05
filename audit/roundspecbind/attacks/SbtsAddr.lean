import Extracted

/-!
# The address of `runtime.staticuint64s` in `slicebytetostringSpec` (U-SBTS-POST)

`slicebytetostringSpec st` says a one-byte result is `&staticuint64s[b] = st + 8 b`. `st` must be the extraction's own
`Extracted.dataAddr.«runtime.staticuint64s»` (which `janus extract` emits for `--contract runtime.slicebytetostring`
after checking the object's size and contents, and `janus check` regenerates from the binary). Any other term lets a
statement place the one-byte result anywhere (or makes the contract one no implementation meets). Controls verify,
attacks are rejected. Statements are vacuous on purpose (`fun _ => False`): only the hypotheses are under test.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- CONTROL: the extraction's own address. -/
theorem c1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A1: a forged numeral. -/
theorem a1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec 4096)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A2: an address the statement chooses (a variable). -/
theorem a2 (impl : List Segment) (st : Nat) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec st)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A3: another extracted data symbol (any other constant of `Extracted`). -/
theorem a3 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec (Extracted.dataAddr.«runtime.staticuint64s» + 8))) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A4: the symbol's address taken from a doctored program (`onlySegments`), not the extraction's data. -/
theorem a4 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec (dataAddr (Extracted.program.onlySegments []).data "runtime.staticuint64s"))) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof

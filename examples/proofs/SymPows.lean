import Extracted

/-!
# `SymPows(i uint64) uint64`: a table read through a named data symbol

**Guarantee.** For every 64-bit `i` and every Go call state `s` of `example.com/basic.SymPows`
whose memory holds the package variable `example.com/basic.symPows` (a `[8]uint64` in the writable
`.noptrdata`, here the powers of ten `1, 10, 100, …, 10^7`), the call returns (never faulting or
panicking), obeys the ABI, and `X0 = 10 ^ (i mod 8)`.

The address and size of the variable are not written in this file: `janus extract` generated
them from the binary's symbol table as `Extracted.dataAddr.«example.com/basic.symPows»` and
`Extracted.dataSize.«example.com/basic.symPows»`, so the proof survives a rebuild that moves the
table. `janus verify` regenerates `Extracted.lean` from the binary, so the constants are as
trusted as the extracted code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

abbrev tbl : Nat := Extracted.dataAddr.«example.com/basic.symPows»

/-- The table's memory: readable, `Extracted.dataSize` bytes long, holding `10 ^ k` at slot `k`. -/
def TableHolds (m : Janus.Arm64.Memory) : Prop :=
  m.accessible tbl Extracted.dataSize.«example.com/basic.symPows» false = true ∧
    ∀ k, k < 8 → m.readLE (tbl + 8 * k) 8 = 10 ^ k

/-- The table's entries fit in 64 bits. -/
theorem pow10_lt : ∀ m, m < 8 → 10 ^ m < 18446744073709551616 := by decide

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i] (fun s => TableHolds s.mem)
      (fun _ s' => (s'.regs 0).toNat = 10 ^ (i.toNat % 8)) := by
  intro ret hret s hs ht
  janus_intro hs
  simp only [TableHolds, tbl, Extracted.dataAddr.«example.com/basic.symPows»,
    Extracted.dataSize.«example.com/basic.symPows»] at ht
  obtain ⟨hacc, hval⟩ := ht
  have hm : i.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := hval (i.toNat % 8) hm
  janus_run
  exact Nat.mod_eq_of_lt (pow10_lt _ hm)

end Proof

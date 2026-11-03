import Janus
import Extracted

/-! `example.com/basic.SymPows(i)` on amd64: `10 ^ (i mod 8)`, read from the package variable
`example.com/basic.symPows` (`[8]uint64`, the powers of ten, in the writable `.noptrdata`). The
variable's address and size are the generated `Extracted.dataAddr.«example.com/basic.symPows»` and
`Extracted.dataSize.«example.com/basic.symPows»`, not literals: the proof survives a rebuild that
moves the table. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

abbrev tbl : Nat := Extracted.dataAddr.«example.com/basic.symPows»

/-- The table's memory: readable, `Extracted.dataSize` bytes long, `10 ^ k` at slot `k`. -/
def TableHolds (m : Janus.Arm64.Memory) : Prop :=
  m.accessible tbl Extracted.dataSize.«example.com/basic.symPows» false = true ∧
    ∀ k, k < 8 → m.readLE (tbl + 8 * k) 8 = 10 ^ k

/-- The table's entries fit in 64 bits. -/
theorem pow10_lt : ∀ m, m < 8 → 10 ^ m < 18446744073709551616 := by decide

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 0 8 ∧ TableHolds s.mem)
      (fun _ s' => results 1 s' = [BitVec.ofNat 64 (10 ^ (i.toNat % 8))]) := by
  intro ret hret s hs hpre
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hstk⟩, hacc, ht⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hstk hnw
  simp only [tbl, Extracted.dataAddr.«example.com/basic.symPows»,
    Extracted.dataSize.«example.com/basic.symPows»] at hacc ht
  have hm : i.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := ht (i.toNat % 8) hm
  janus64_run
  rw [Nat.mul_comm 8 (i.toNat % 8)] at h
  rw [h]

end Proof

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

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def i : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then i else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := ⟨fun a => if tbl ≤ a ∧ a < tbl + 64 then BitVec.ofNat 8 (10 ^ ((a - tbl) / 8) / 256 ^ ((a - tbl) % 8)) else wmem64.bytes a, wmem64.regions ++ [⟨tbl, Extracted.dataSize.«example.com/basic.symPows», false⟩]⟩ }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => StackWritable s 0 8 ∧ TableHolds s.mem) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (StackWritable s 0 8 ∧ TableHolds s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (10 ^ (i.toNat % 8))]) :=
  ⟨ret, s0, i, hret, setup, hpre, correctness i ret hret s0 setup hpre⟩

end Witness

end Proof

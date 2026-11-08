import Janus
import Extracted

/-! `example.com/basic.HexDigit(i)` on amd64: byte `i & 15` of the string constant
`"0123456789abcdef"`, which the code loads from `.rodata` (copied into `Extracted.data`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The digit table, as copied from the binary. -/
def digits : Janus.DataSegment := Extracted.data[0]

/-- `digits.base`, the address of the only data object the function loads (layout-independent:
read off `Extracted.data`). -/
def digitsBase : Nat := dataBase Extracted.program 0

theorem digits_base : digits.base = digitsBase := rfl

theorem digits_mem : digits ∈ Extracted.program.data := List.mem_cons_self

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem)
      (fun _ s' => results 1 s' = [BitVec.ofNat 64 (digits.bytes[i.toNat % 16]!)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, hdl⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have hrd := DataLoaded.accessible hdl digits_mem
  have hlen : digits.bytes.length = 256 := by
    set_option maxRecDepth 100000 in decide
  have hbase := digits_base
  simp only [digitsBase, reduceDataBase] at hbase
  rw [hlen, hbase] at hrd
  have hbyte := DataLoaded.byte hdl digits_mem (i.toNat % 16) (by rw [hlen]; omega)
  rw [hbase] at hbyte
  have hlt := Janus.Arm64.Memory.readLE_lt s.mem (digitsBase + i.toNat % 16) 1
  simp only [digitsBase, reduceDataBase] at hlt
  janus64_run
  have hk : i.toNat % 16 < digits.bytes.length := by rw [hlen]; omega
  rw [getElem!_pos digits.bytes (i.toNat % 16) hk]
  rw [hbyte] at hlt
  first | (with_reducible congr 1; with_reducible congr 1) | (congr 1; congr 1)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def i : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then i else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := withData Extracted.program.data wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s => StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (i : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [i] s ∧ (StackWritable s 0 8 ∧ Extracted.program.DataLoaded s.mem) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (digits.bytes[i.toNat % 16]!)]) :=
  ⟨ret, s0, i, hret, setup, hpre, correctness i ret hret s0 setup hpre⟩

end Witness

end Proof

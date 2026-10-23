import Janus
import Extracted

/-! `example.com/basic.HexDigit(i)` on amd64: byte `i & 15` of the string constant
`"0123456789abcdef"`, which the code loads from `.rodata` (copied into `Extracted.data`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The digit table, as copied from the binary. -/
def digits : Janus.DataSegment := Extracted.data[0]

/-- `digits.base`, the address of the string bytes in this binary. -/
def digitsBase : Nat := 0x4abe84

theorem digits_base : digits.base = digitsBase := by decide

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
  simp only [digitsBase] at hbase
  rw [hlen, hbase] at hrd
  have hbyte := DataLoaded.byte hdl digits_mem (i.toNat % 16) (by rw [hlen]; omega)
  rw [hbase] at hbyte
  have hlt := Janus.Arm64.Memory.readLE_lt s.mem (digitsBase + i.toNat % 16) 1
  simp only [digitsBase] at hlt
  janus64_run
  have hk : i.toNat % 16 < digits.bytes.length := by rw [hlen]; omega
  rw [getElem!_pos digits.bytes (i.toNat % 16) hk]
  rw [hbyte] at hlt
  congr 1; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Proof

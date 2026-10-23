import Janus
import Extracted

/-! `example.com/basic.SetOne256(z)` on amd64: `*z = [4]uint64{1, 0, 0, 0}`, copied from a
32-byte `.rodata` constant through `X14` (`MOVUPS`). `z` must not overlap the constant (on
hardware a writable buffer cannot share a page with read-only data; the model's regions may
overlap, so this is stated) nor the return-address slot. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

def one : Janus.DataSegment := Extracted.data[0]

/-- `one.base`, the address of the constant in this binary. -/
def oneBase : Nat := 0x4b4840

theorem one_base : one.base = oneBase := by decide

theorem one_mem : one ∈ Extracted.program.data := List.mem_cons_self

theorem readLE_32_16 (m : Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 16 + 2 ^ 128 * m.readLE (a + 16) 16 :=
  Janus.Arm64.Memory.readLE_add m a 16 16

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Extracted.program.DataLoaded s.mem ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Disjoint z 32 (BitVec.ofNat 64 oneBase) 32)
      (fun _ s' => valueAt s' z 32 = 1) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hzw, hz⟩, hdl, hds, hdd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hacc hnw hds hdd
  have hrd := DataLoaded.accessible hdl one_mem
  have hlen : one.bytes.length = 32 := by decide
  have hbase := one_base
  simp only [oneBase] at *
  rw [hlen, hbase] at hrd
  have h0 := DataLoaded.readLE hdl one_mem 0 16 (by rw [hlen]; omega)
  have h1 := DataLoaded.readLE hdl one_mem 16 16 (by rw [hlen]; omega)
  rw [hbase] at h0 h1
  rw [show listLE (one.bytes.drop 0) 16 = 1 by decide] at h0
  rw [show listLE (one.bytes.drop 16) 16 = 0 by decide] at h1
  simp only [Nat.add_zero, Nat.reduceAdd] at h0 h1
  simp only [valueAt]
  janus64_run [readLE_32_16]

end Proof

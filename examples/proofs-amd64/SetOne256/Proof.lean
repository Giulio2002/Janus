import Janus
import Extracted

/-! `example.com/basic.SetOne256(z)` on amd64: `*z = [4]uint64{1, 0, 0, 0}`, copied from a
32-byte `.rodata` constant through `X14` (`MOVUPS`). `z` must not overlap the constant (on
hardware a writable buffer cannot share a page with read-only data; the model's regions may
overlap, so this is stated) nor the return-address slot. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

def one : Janus.DataSegment := Extracted.data[0]

/-- `one.base`, the address of the only data object the function loads (layout-independent:
read off `Extracted.data`). -/
def oneBase : Nat := dataBase Extracted.program 0

theorem one_base : one.base = oneBase := rfl

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
  simp only [oneBase, reduceDataBase] at *
  rw [hlen, hbase] at hrd
  have h0 := DataLoaded.readLE hdl one_mem 0 16 (by rw [hlen]; omega)
  have h1 := DataLoaded.readLE hdl one_mem 16 16 (by rw [hlen]; omega)
  rw [hbase] at h0 h1
  rw [show listLE (one.bytes.drop 0) 16 = 1 by decide] at h0
  rw [show listLE (one.bytes.drop 16) 16 = 0 by decide] at h1
  simp only [Nat.add_zero, Nat.reduceAdd] at h0 h1
  simp only [valueAt]
  janus64_run [readLE_32_16]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def z : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then z else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := withData Extracted.program.data wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Extracted.program.DataLoaded s.mem ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Disjoint z 32 (BitVec.ofNat 64 oneBase) 32) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Extracted.program.DataLoaded s.mem ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Disjoint z 32 (BitVec.ofNat 64 oneBase) 32) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ valueAt s' z 32 = 1) :=
  ⟨ret, s0, z, hret, setup, hpre, correctness z ret hret s0 setup hpre⟩

end Witness

end Proof

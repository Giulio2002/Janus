import Janus
import Extracted

/-! `example.com/basic.Table(i)` on amd64: entry `i & 7` of a constant `[8]uint64` table. The
code copies the 64-byte `.rodata` literal into its frame with four `MOVUPS` through `X14` and
loads `t[i&7]` from the frame. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The Go source's table. -/
def table : List (BitVec 64) :=
  [0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
   0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917]

def lit : Janus.DataSegment := Extracted.data[0]

/-- `lit.base`, the address of the table literal in this binary. -/
def litBase : Nat := 0x4b6ee0

theorem lit_base : lit.base = litBase := by decide

theorem lit_mem : lit ∈ Extracted.program.data := List.mem_cons_self

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 72 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Disjoint (s.regs regSP - 72) 80 (BitVec.ofNat 64 litBase) 64)
      (fun _ s' => results 1 s' = [table[i.toNat % 8]!]) := by
  intro ret hret s hs hpre
  simp only [litBase] at *
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, hdl, hdd⟩ := hpre
  simp only [regSP] at hacc hle hnw hdd
  have h72 : (72 : BitVec 64).toNat = 72 := rfl
  simp only [Disjoint, BitVec.toNat_sub, h72, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hdd
  have hdd' : (s.regs 4).toNat - 72 + 80 ≤ litBase ∨ litBase + 64 ≤ (s.regs 4).toNat - 72 := by
    simp only [litBase]
    have := (s.regs 4).isLt; omega
  clear hdd
  have hrd := DataLoaded.accessible hdl lit_mem
  have hlen : lit.bytes.length = 64 := by decide
  have hbase := lit_base
  rw [hlen, hbase] at hrd
  simp only [litBase] at hrd hdd' hbase
  have h0 := DataLoaded.readLE hdl lit_mem 0 16 (by rw [hlen]; omega)
  rw [hbase, show listLE (lit.bytes.drop 0) 16 = 25387941959461950912960554715935082707 by decide] at h0
  have h1 := DataLoaded.readLE hdl lit_mem 16 16 (by rw [hlen]; omega)
  rw [hbase, show listLE (lit.bytes.drop 16) 16 = 10877752339986815226299666075844817360 by decide] at h1
  have h2 := DataLoaded.readLE hdl lit_mem 32 16 (by rw [hlen]; omega)
  rw [hbase, show listLE (lit.bytes.drop 32) 16 = 252991557357635113187930604456282952567 by decide] at h2
  have h3 := DataLoaded.readLE hdl lit_mem 48 16 (by rw [hlen]; omega)
  rw [hbase, show listLE (lit.bytes.drop 48) 16 = 84431081469421953577864348762426331357 by decide] at h3
  have hk : i.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize hkk : i.toNat % 8 = k at hk ⊢
  janus64_run
  rw [hkk]
  have hsp := hle
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals
    generalize hr : (s.regs 4).toNat - 72 = r at *
    have e1 : (s.regs 4).toNat - 56 = r + 16 := by omega
    have e2 : (s.regs 4).toNat - 40 = r + 32 := by omega
    have e3 : (s.regs 4).toNat - 24 = r + 48 := by omega
    have e4 : (s.regs 4).toNat - 8 = r + 64 := by omega
    rw [e1, e2, e3, e4]
    simp (disch := omega) only [readLE_writeLE_inside, readLE_writeLE_disjoint, Nat.zero_mul,
      Nat.add_zero, Nat.reduceMul, Nat.add_sub_add_left, Nat.add_sub_cancel_left, Nat.sub_self]
    decide

end Proof

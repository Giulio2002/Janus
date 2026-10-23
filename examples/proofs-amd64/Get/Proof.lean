import Janus
import Extracted

/-! `example.com/basic.Get(xs []uint64, i int)` on amd64: `xs[i]` when `i < len(xs)` (unsigned), a bounds panic otherwise. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- In bounds: the element at index `i` is returned. The slice must not overlap the frame
slots the function writes (`[RSP-8, RSP+16)`: saved `RBP`, return address, spilled pointer). -/
theorem correctness (ptr len cap i : BitVec 64) (hi : i.toNat < len.toNat) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => StackWritable s 8 16 ∧ Buffer s ptr (8 * len.toNat) false ∧
        Disjoint ptr (8 * len.toNat) (s.regs regSP - 8) 24)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (valueAt s (ptr + 8 * i) 8)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, ⟨hbw, hb⟩, hd⟩ := hpre
  simp only [regSP] at hacc hle hnw hd
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [Disjoint, BitVec.toNat_sub, h8] at hd
  have hd' : ptr.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat := by
    have := (s.regs 4).isLt; omega
  clear hd
  have hidx : (ptr + 8 * i).toNat = ptr.toNat + i.toNat * 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, h8]; omega
  simp only [valueAt, hidx]
  janus64_run

/-- Out of bounds (unsigned `i ≥ len`): `runtime.panicBounds`. -/
theorem panics (ptr len cap i : BitVec 64) (hi : len.toNat ≤ i.toNat) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [ptr, len, cap, i] s)
    (hpre : StackWritable s 16 16) : Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  janus64_run

end Proof

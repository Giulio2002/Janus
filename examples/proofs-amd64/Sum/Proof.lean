import Janus
import Extracted

/-! `example.com/basic.Sum(xs []uint64)` on amd64: the sum of the elements, modulo `2^64`.

```
MOVQ AX, 8(SP)        ; spill
XORL CX, CX ; XORL DX, DX ; JMP head
body: ADDQ (AX)(CX*8), DX ; INCQ CX
head: CMPQ BX, CX ; JGT body       ; signed len > i
MOVQ DX, AX ; RET
```

The loop is proved by induction on the remaining iterations from the loop head (`loop`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The loop head (`CMPQ BX, CX`) in this binary. -/
def loopHead : Nat := 0x489412

/-- `Σ_{j<n} word(a + 8 (k + j))`. -/
def sumFrom (m : Memory) (a k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m.readLE (a + 8 * k) 8 + sumFrom m a (k + 1) n

/-- The loop head `loopHead`, with `i = k` in `CX`, the running sum in `DX`: the call returns
`DX + Σ` of the remaining `n = len - k` elements. -/
theorem loop (ptr len : BitVec 64) (hlen : len.toNat < 2 ^ 63) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (m : Memory)
    (hb : ptr.toNat + 8 * len.toNat ≤ 2 ^ 48) (hm : m.accessible ptr.toNat (8 * len.toNat) false = true) :
    ∀ n k (acc : BitVec 64) (t : State), k + n = len.toNat →
      t.rip = BitVec.ofNat 64 loopHead → t.regs 0 = ptr → t.regs 3 = len → t.regs 1 = BitVec.ofNat 64 k →
      t.regs 2 = acc → t.mem = m → m.accessible (t.regs 4).toNat 8 false = true →
      m.readLE (t.regs 4).toNat 8 = ret →
      Reaches (Extracted.program.withExit ret) t (IsReturn fun t' =>
        t'.regs 0 = acc + BitVec.ofNat 64 (sumFrom m ptr.toNat k n) ∧ t'.regs 4 = t.regs 4 + 8 ∧
        t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15) := by
  intro n
  induction n
  case zero =>
    intro k acc t hk h_rip h0 h3 h1 h2 hmem hsp hra
    have hk' : k < 2 ^ 63 := by omega
    simp only [loopHead] at h_rip
    janus64_run
    simp [sumFrom]
  case succ n ih =>
    intro k acc t hk h_rip h0 h3 h1 h2 hmem hsp hra
    have hk' : k < 2 ^ 63 := by omega
    simp only [loopHead] at h_rip
    janus64_run until [loopHead]
    refine Reaches.mono (ih (k + 1) (acc + BitVec.ofNat 64 (m.readLE (ptr.toNat + k * 8) 8)) _
      (by omega) (by rfl) (by simp [setRegF, h0]) (by simp [setRegF, h3]) (by simp [setRegF])
      (by simp [setRegF]) rfl (by simpa [setRegF] using hsp) (by simpa [setRegF] using hra)) ?_
    intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned t' =>
      simp only [isReturn_returned, setRegF] at ho ⊢
      obtain ⟨e0, e4, e5, e14, e15⟩ := ho
      refine ⟨?_, by simpa using e4, by simpa using e5, by simpa using e14, e15⟩
      rw [e0, sumFrom, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_comm 8 k]

/-- A store outside the summed words does not change their sum. -/
theorem sumFrom_writeLE (m : Memory) (a b v : Nat) :
    ∀ n k, (b + 8 ≤ a + 8 * k ∨ a + 8 * (k + n) ≤ b) →
      sumFrom (m.writeLE b 8 v) a k n = sumFrom m a k n := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro k h
    simp only [sumFrom]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint m v (by omega), ih (k + 1) (by omega)]

/-- `Sum(xs)` returns `Σ xs[j] mod 2^64`. The spill slot `8(SP)` must not overlap the slice;
`len < 2^63` holds for every Go slice. -/
theorem correctness (ptr len cap : BitVec 64) (hlen : len.toNat < 2 ^ 63) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap]
      (fun s => StackWritable s 0 16 ∧ Buffer s ptr (8 * len.toNat) false ∧
        Disjoint ptr (8 * len.toNat) (s.regs regSP + 8) 8)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (sumFrom s.mem ptr.toNat 0 len.toNat)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hbw, hb⟩, hd⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hd
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [Disjoint, BitVec.toNat_add, h8] at hd
  have hd' : ptr.toNat + 8 * len.toNat ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat := by
    have := (s.regs 4).isLt; omega
  clear hd
  janus64_run until [loopHead]
  refine Reaches.mono (loop ptr len hlen ret hret _ hbw (by simpa using hb) len.toNat 0 0 _ (by omega) (by rfl)
    (by simp [setRegF, h_a0]) (by simp [setRegF, h_a1]) (by simp [setRegF]) (by simp [setRegF]) rfl
    ?_ ?_) ?_
  · simp (config := { decide := true }) only [↓reduceIte, setRegF, Janus.Arm64.Memory.accessible_writeLE]
    exact accessible_sub hacc (by decide) (by omega) (by omega)
  · simp (config := { decide := true }) only [↓reduceIte, setRegF]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), h_ret]
  · intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned t' =>
      simp only [isReturn_returned, setRegF] at ho ⊢
      obtain ⟨e0, e4, e5, e14, e15⟩ := ho
      refine ⟨⟨by simpa using e4, by simpa using e5, by simpa using e14, by simpa using e15⟩, ?_⟩
      simp only [results, intArgRegs, List.take, List.map, e0]
      rw [sumFrom_writeLE _ _ _ _ _ _ (by omega)]; simp

end Proof

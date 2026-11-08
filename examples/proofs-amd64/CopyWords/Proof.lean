import Janus
import Extracted

/-! `example.com/basic.CopyWords(dst, src []uint64) int` on amd64: copies
`n = min(len(dst), len(src))` words from `src` to `dst` and returns `n`.

```
MOVQ AX, 8(SP) ; MOVQ DI, 32(SP)          ; spills
CMPQ SI, BX ; CMOVQGT BX, SI ; XORL CX, CX ; JMP head
body: MOVQ (DI)(CX*8), DX ; MOVQ DX, (AX)(CX*8) ; INCQ CX
head: CMPQ CX, SI ; JLT body
MOVQ SI, AX ; RET
```

The loop is proved by induction on the remaining iterations from the loop head (`loop`), with
the memory kept abstract: the invariant says which words are already copied and that the
source words are untouched. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The loop head (`CMPQ CX, SI`), 0x20 bytes into the function (layout-independent: derived
from `Extracted.entry`). -/
def loopHead : Nat := Extracted.entry + 0x20

theorem loop (d s n : Nat) (hn : n < 2 ^ 63) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (m0 : Memory) (hdw : d + 8 * n ≤ 2 ^ 48) (hsw : s + 8 * n ≤ 2 ^ 48)
    (hdisj : d + 8 * n ≤ s ∨ s + 8 * n ≤ d) :
    ∀ r k (M : Memory) (t : State), k + r = n →
      t.rip = BitVec.ofNat 64 loopHead → t.regs 0 = BitVec.ofNat 64 d →
      t.regs 7 = BitVec.ofNat 64 s → t.regs 6 = BitVec.ofNat 64 n →
      t.regs 1 = BitVec.ofNat 64 k → t.mem = M →
      M.accessible d (8 * n) true = true → M.accessible s (8 * n) false = true →
      M.accessible (t.regs 4).toNat 8 false = true →
      (d + 8 * n ≤ (t.regs 4).toNat ∨ (t.regs 4).toNat + 8 ≤ d) →
      M.readLE (t.regs 4).toNat 8 = ret →
      (∀ j, j < n → M.readLE (s + 8 * j) 8 = m0.readLE (s + 8 * j) 8) →
      (∀ j, j < k → M.readLE (d + 8 * j) 8 = m0.readLE (s + 8 * j) 8) →
      Reaches (Extracted.program.withExit ret) t (IsReturn fun t' =>
        t'.regs 0 = BitVec.ofNat 64 n ∧
        (∀ j, j < n → t'.mem.readLE (d + 8 * j) 8 = m0.readLE (s + 8 * j) 8) ∧
        t'.regs 4 = t.regs 4 + 8 ∧ t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧
        t'.xmm 15 = t.xmm 15) := by
  intro r
  induction r
  case zero =>
    intro k M t hk h_rip h0 h7 h6 h1 hmem hda hsa hsp hspd hra hsrc hcp
    have hk' : k < 2 ^ 63 := by omega
    simp only [loopHead] at h_rip
    janus64_run
    exact fun j hj => hcp j (by omega)
  case succ r ih =>
    intro k M t hk h_rip h0 h7 h6 h1 hmem hda hsa hsp hspd hra hsrc hcp
    have hk' : k < 2 ^ 63 := by omega
    simp only [loopHead] at h_rip
    janus64_run until [loopHead]
    have hkn : k < n := by omega
    have hw := fun j (hj : j < n) => Janus.Arm64.Memory.readLE_writeLE_of_disjoint M
      (M.readLE (s + k * 8) 8) (a := d + k * 8) (n := 8) (b := s + 8 * j) (k := 8) (by omega)
    refine Reaches.mono (ih (k + 1) _ _ (by omega) (by simp only [loopHead]; rfl) (by simp [setRegF, h0])
      (by simp [setRegF, h7]) (by simp [setRegF, h6]) (by simp [setRegF]) rfl
      (by simpa using hda) (by simpa using hsa) (by simpa (config := { decide := true }) [setRegF] using hsp)
      (by simpa (config := { decide := true }) [setRegF] using hspd)
      (by simp (config := { decide := true }) only [↓reduceIte, setRegF]; rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hra])
      (fun j hj => by rw [hw j hj, hsrc j hj]) ?_) ?_
    · intro j hj
      by_cases hjk : j = k
      · subst hjk
        rw [Nat.mul_comm 8 j, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt
          (Janus.Arm64.Memory.readLE_lt _ _ 8), Nat.mul_comm j 8, ← hsrc j (by omega), Nat.mul_comm 8 j]
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcp j (by omega)]
    · intro o ho
      cases o with
      | stub _ _ _ => exact ho.elim
      | returned t' =>
        simp only [isReturn_returned, setRegF] at ho ⊢
        obtain ⟨e0, e1, e4, e5, e14, e15⟩ := ho
        exact ⟨e0, e1, by simpa using e4, by simpa using e5, by simpa using e14, e15⟩

/-- `CopyWords(dst, src)` returns `n = min(len(dst), len(src))` and leaves `dst[j] = src[j]`
for `j < n`. The slices must not overlap each other, nor the two spill slots `8(SP)` and
`32(SP)` and the return address the function writes and reads. -/
theorem correctness (dst dlen dcap src slen scap : BitVec 64)
    (hdl : dlen.toNat < 2 ^ 63) (hsl : slen.toNat < 2 ^ 63) :
    Ensures Extracted.program Extracted.entry [dst, dlen, dcap, src, slen, scap]
      (fun s => StackWritable s 0 40 ∧ Buffer s dst (8 * dlen.toNat) true ∧
        Buffer s src (8 * slen.toNat) false ∧ Disjoint dst (8 * dlen.toNat) src (8 * slen.toNat) ∧
        Disjoint dst (8 * dlen.toNat) (s.regs regSP) 40 ∧ Disjoint src (8 * slen.toNat) (s.regs regSP) 40)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (min dlen.toNat slen.toNat)] ∧
        ∀ j, j < min dlen.toNat slen.toNat →
          s'.mem.readLE (dst.toNat + 8 * j) 8 = s.mem.readLE (src.toNat + 8 * j) 8) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hdw, hd⟩, ⟨hsw, hsa⟩, hds, hdsp, hssp⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds hdsp hssp
  janus64_run until [loopHead]
  have hmd : min dlen.toNat slen.toNat ≤ dlen.toNat := Nat.min_le_left _ _
  have hms : min dlen.toNat slen.toNat ≤ slen.toNat := Nat.min_le_right _ _
  have hsp4 := (s.regs 4).isLt
  have hw8 := fun (a k : Nat) (h : a + k ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 40 ≤ a) =>
    fun v (m : Memory) => Janus.Arm64.Memory.readLE_writeLE_of_disjoint m v
      (a := (s.regs 4).toNat + 8) (n := 8) (b := a) (k := k) (by omega)
  have hw32 := fun (a k : Nat) (h : a + k ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 40 ≤ a) =>
    fun v (m : Memory) => Janus.Arm64.Memory.readLE_writeLE_of_disjoint m v
      (a := (s.regs 4).toNat + 32) (n := 8) (b := a) (k := k) (by omega)
  refine Reaches.mono (loop dst.toNat src.toNat (min dlen.toNat slen.toNat) (by omega) ret hret s.mem
    (by omega) (by omega) (by omega) (min dlen.toNat slen.toNat) 0 _ _ (by omega)
    (by simp only [loopHead]; rfl) (by simp [setRegF, h_a0]) (by simp [setRegF, h_a3])
    ?_ (by simp [setRegF]) rfl ?_ ?_ ?_ ?_ ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero _))) ?_
  · simp (config := { decide := true }) only [↓reduceIte, setRegF]
    by_cases h : (dlen.toNat : Int) < slen.toNat
    · rw [if_pos h, Nat.min_eq_left (by omega)]; simp
    · rw [if_neg h, Nat.min_eq_right (by omega)]; simp
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact accessible_sub hd (by decide) (by omega) (by omega)
  · simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact accessible_sub hsa (by decide) (by omega) (by omega)
  · simp (config := { decide := true }) only [↓reduceIte, setRegF, Janus.Arm64.Memory.accessible_writeLE]
    exact accessible_sub hacc (by decide) (by omega) (by omega)
  · simp (config := { decide := true }) only [↓reduceIte, setRegF]; omega
  · simp (config := { decide := true }) only [↓reduceIte, setRegF]
    rw [hw32 _ _ (by omega), hw8 _ _ (by omega), h_ret]
  · intro j hj
    rw [hw32 _ _ (by omega), hw8 _ _ (by omega)]
  · intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned t' =>
      simp (config := { decide := true }) only [↓reduceIte, isReturn_returned, setRegF] at ho ⊢
      obtain ⟨e0, e1, e4, e5, e14, e15⟩ := ho
      refine ⟨⟨e4, e5, e14, e15⟩, ?_, e1⟩
      simp only [results, intArgRegs, List.take, List.map, e0]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def dst : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def dlen : BitVec 64 := 2#64
def dcap : BitVec 64 := 2#64
def src : BitVec 64 := 0x30a00#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def slen : BitVec 64 := 3#64
def scap : BitVec 64 := 3#64
theorem hdl : dlen.toNat < 2 ^ 63 := by decide
theorem hsl : slen.toNat < 2 ^ 63 := by decide

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 3 then dlen else if i = 1 then dcap else if i = 7 then src else if i = 6 then slen else if i = 8 then scap else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, dlen, dcap, src, slen, scap] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 40 ∧ Buffer s dst (8 * dlen.toNat) true ∧
        Buffer s src (8 * slen.toNat) false ∧ Disjoint dst (8 * dlen.toNat) src (8 * slen.toNat) ∧
        Disjoint dst (8 * dlen.toNat) (s.regs regSP) 40 ∧ Disjoint src (8 * slen.toNat) (s.regs regSP) 40) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (dst : BitVec 64) (dlen : BitVec 64) (dcap : BitVec 64) (src : BitVec 64) (slen : BitVec 64) (scap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, dlen, dcap, src, slen, scap] s ∧ (dlen.toNat < 2 ^ 63) ∧ (slen.toNat < 2 ^ 63) ∧ (StackWritable s 0 40 ∧ Buffer s dst (8 * dlen.toNat) true ∧
        Buffer s src (8 * slen.toNat) false ∧ Disjoint dst (8 * dlen.toNat) src (8 * slen.toNat) ∧
        Disjoint dst (8 * dlen.toNat) (s.regs regSP) 40 ∧ Disjoint src (8 * slen.toNat) (s.regs regSP) 40) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ results 1 s' = [BitVec.ofNat 64 (min dlen.toNat slen.toNat)] ∧
        ∀ j, j < min dlen.toNat slen.toNat →
          s'.mem.readLE (dst.toNat + 8 * j) 8 = s.mem.readLE (src.toNat + 8 * j) 8) :=
  ⟨ret, s0, dst, dlen, dcap, src, slen, scap, hret, setup, hdl, hsl, hpre, correctness dst dlen dcap src slen scap hdl hsl ret hret s0 setup hpre⟩

end Witness

end Proof

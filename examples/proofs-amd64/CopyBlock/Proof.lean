import Janus
import Extracted

/-! `example.com/basic.CopyBlock(dst, src *[16]uint64)` on amd64: `copy(dst[:], src[:])`, which
the compiler lowers to a call of `runtime.memmove(dst, src, 128)` (skipped when `dst = src`).

```
CMPQ SP, 16(R14) ; JBE morestack ; PUSHQ BP ; MOVQ SP, BP ; SUBQ $0x18, SP
TESTB AL, (AX) ; TESTB AL, (BX)          // nil checks
CMPQ BX, AX ; JEQ done ; MOVL $0x80, CX ; CALL runtime.memmove
done: ADDQ $0x18, SP ; POPQ BP ; RET
```

`runtime.memmove` (Go 1.26, `runtime/memmove_amd64.s`) is executed in full: the length
dispatch (`CMPQ BX, $n` …) selects the 65–128-byte case, which loads eight 16-byte `MOVDQU`
chunks into `X0`–`X7` (four from the front, four from the back) and then stores them. Because
every load precedes every store, the copy is correct for any overlap of `dst` and `src`. For
128 bytes `memmove` reads no CPU-feature global (`runtime.memmoveBits` is only consulted above
256 bytes). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `CopyBlock(dst, src)` leaves the 128 bytes at `dst` equal to the 128 bytes that were at
`src` before the call, whether or not the arrays overlap. The arrays must be accessible
(`dst` writable), and must not overlap the stack slots the function and `memmove` use: `dst`
not `[RSP - 40, RSP + 8)` (the frame and the return address, written or read after the copy),
and `src` not `[RSP - 40, RSP)` (written before the copy). -/
theorem correctness (dst src : BitVec 64) :
    Ensures Extracted.program Extracted.entry [dst, src]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s dst 128 true ∧
        Buffer s src 128 false ∧
        (dst.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ dst.toNat) ∧
        (src.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ src.toNat))
      (fun s s' => valueAt s' dst 128 = valueAt s src 128) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨hdw, hd⟩, ⟨hsw, hsa⟩, hdd, hsd⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hdd hsd
  simp only [valueAt]
  janus64_run
  · -- `dst = src`: `CopyBlock` skips the call
    have := dst.isLt; have := src.isLt
    rw [show dst.toNat = src.toNat by omega]
  · exact copy_step _ _ _ _ 112 16 <| copy_step _ _ _ _ 96 16 <| copy_step _ _ _ _ 80 16 <|
      copy_step _ _ _ _ 64 16 <| copy_step _ _ _ _ 48 16 <| copy_step _ _ _ _ 32 16 <|
      copy_step _ _ _ _ 16 16 <| copy_first _ _ _ _ _

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def dst : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def src : BitVec 64 := 0x30a00#64

def s0 : State :=
  { regs := fun i => if i = 0 then dst else if i = 3 then src else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, src] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s dst 128 true ∧
        Buffer s src 128 false ∧
        (dst.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ dst.toNat) ∧
        (src.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ src.toNat)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (dst : BitVec 64) (src : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [dst, src] s ∧ (StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s dst 128 true ∧
        Buffer s src 128 false ∧
        (dst.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ dst.toNat) ∧
        (src.toNat + 128 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ src.toNat)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ valueAt s' dst 128 = valueAt s src 128) :=
  ⟨ret, s0, dst, src, hret, setup, hpre, correctness dst src ret hret s0 setup hpre⟩

end Witness

end Proof

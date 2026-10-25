import Janus
import Extracted

/-!
# `Eq32(a, b *[32]byte) bool` on amd64: `*a == *b` through `runtime.memequal`

```
CMPQ SP, 16(R14) ; JBE morestack ; PUSHQ BP ; MOVQ SP, BP ; SUBQ $0x18, SP
TESTB AL, (AX) ; TESTB AL, (BX)          // nil checks
MOVL $0x20, CX ; CALL runtime.memequal
ADDQ $0x18, SP ; POPQ BP ; RET
```

**Guarantee.** For all pointers `a`, `b` and every Go call state whose stack check falls through,
with the 40 bytes below `RSP` writable (the frame, the saved `RBP` and the return address of the
call), the 32 bytes at `a` and at `b` readable and outside that window, the call returns and the
`bool` result in `AL` is `true` iff the 32 bytes at `a` equal those at `b`.

**What this covers.** Nothing is assumed about `runtime.memequal`: the proof executes it and
`memeqbody` (`internal/bytealg/equal_amd64.s`): the `a = b` shortcut, then, since `32 < 64`,
the 8-byte `bigloop` three times and `leftover` (the last 8 bytes, `SETEQ`). The SSE/AVX2 loops
are not reached for 32 bytes.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.Mem

/-- The precondition (see the module documentation). -/
def pre (a b : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s a 32 false ∧ Buffer s b 32 false ∧
    (a.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ a.toNat) ∧
    (b.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat ≤ b.toNat)

set_option maxHeartbeats 8000000 in
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b] (pre a b)
      (fun s s' => (s'.regs 0).toNat % 256 =
        (s.mem.readLE a.toNat 32 == s.mem.readLE b.toNat 32).toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, ⟨hle, hnw, hacc⟩, ⟨ha48, ha⟩, ⟨hb48, hb⟩, hda, hdb⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hda hdb
  have ha' := a.isLt
  have hb' := b.isLt
  janus64_run
  all_goals
    have l0 := Janus.Arm64.Memory.readLE_lt s.mem a.toNat 8
    have l1 := Janus.Arm64.Memory.readLE_lt s.mem (a.toNat + 8) 8
    have l2 := Janus.Arm64.Memory.readLE_lt s.mem (a.toNat + 16) 8
    have l3 := Janus.Arm64.Memory.readLE_lt s.mem (a.toNat + 24) 8
    have m0 := Janus.Arm64.Memory.readLE_lt s.mem b.toNat 8
    have m1 := Janus.Arm64.Memory.readLE_lt s.mem (b.toNat + 8) 8
    have m2 := Janus.Arm64.Memory.readLE_lt s.mem (b.toNat + 16) 8
    have m3 := Janus.Arm64.Memory.readLE_lt s.mem (b.toNat + 24) 8
    have hw := readLE_32_eq_iff s.mem a.toNat b.toNat
    simp only [Nat.reducePow] at l0 l1 l2 l3 m0 m1 m2 m3
  · have hab : a.toNat = b.toNat := by omega
    simp [hab]
  all_goals by_cases h : s.mem.readLE a.toNat 32 = s.mem.readLE b.toNat 32
  all_goals simp only [h, beq_self_eq_true, Bool.toNat_true, beq_eq_false_iff_ne.mpr, ne_eq,
    not_false_eq_true, Bool.toNat_false]
  all_goals first
    | (exfalso; have := hw.1 h; omega)
    | (split <;> first | rfl | (exfalso; have := hw.1 h; omega) | (exfalso; apply h; apply hw.2; omega))
    | (exfalso; apply h; apply hw.2; omega)

/-! ## Non-vacuity: the precondition holds for a concrete call, and the result is reached -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness return address (the word at `[RSP]` of `wmem64`). -/
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- Two distinct all-zero 32-byte arrays of the witness memory. -/
def a : BitVec 64 := BitVec.ofNat 64 DST
def b : BitVec 64 := BitVec.ofNat 64 (DST + 32)

/-- The witness call state `Eq32(a, b)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 3 then b
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : pre a b s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ pre a b s :=
  ⟨ret, s0, a, b, hret, setup, hpre⟩

/-- So the guarantee is reached: the two zero arrays compare equal. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness a b ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Witness

end Proof

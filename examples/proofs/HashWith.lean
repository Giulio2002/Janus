import Extracted

/-!
# `HashWith(h Hasher, x uint64) uint64` calls `h.Hash(x)` through the interface's itab

**Guarantee.** For every interface value `(tab, h)` in `X0`, `X1`, every `x` in `X2` and every Go
call state `s` of `example.com/basic.HashWith` in which the stack-growth prologue falls through
(`GuardOK s 0`), `SP` is aligned with `[SP-40, SP+24)` writable (`StackOK s 40 24`: the frame and
the spill slots of `tab` and `h`), and the receiver's 8-byte field `K` at `h` is readable and
outside that window:

* if `tab` is the static itab of `*MulHasher` for `Hasher` (`ItabIs … tab mulItab`: `tab` is its
  address and memory holds its 32 bytes, copied from `.rodata`, read-only), the call returns,
  obeys the ABI, and `X0 = x · K`: the dynamic call reaches `(*MulHasher).Hash`;
* if `tab` is the static itab of `*RotHasher`, it returns `rotl(x, 13) + K`, the result of
  `(*RotHasher).Hash`.

**What it assumes.** Which method the `BLR` reaches is not derived from Go's type system: the
`ItabIs` hypotheses say which itab the interface value carries, and the `Fun[0]` word the code
loads from it is the one in the binary. The extraction (`janus extract … --targets` with both
itabs) copies the itabs and the code of both methods.

**How.** Each method is proved once as a callee `Summary`. `janus_dyn hi` turns `ItabIs` into the
itab's literal address and contents; `janus_run` then loads `Fun[0]`, finds a literal branch
target at the `BLR` and applies that method's summary (`calls [...]`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

abbrev mulItab : String := "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
abbrev rotItab : String := "go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher"

theorem mul_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*MulHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => ∃ v2, s' = { s with
        regs := setReg (setReg s.regs 0 (s.regs 1 * BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8))) 2 v2,
        pc := s.regs 30 }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Memory.accessible_bound _ h0
  janus_run
  exact ⟨_, rfl⟩

theorem rot13 (x : BitVec 64) : BitVec.extractLsb' 51 64 (x ++ x) = x.rotateLeft 13 := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  split <;> split
  · rw [BitVec.getLsbD_eq_getElem (by omega)]
  · omega
  · omega
  · rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega

theorem rot_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*RotHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56)
      (fun s s' => ∃ v1 v2, s' = { s with
        regs := setReg (setReg (setReg s.regs 0
          ((s.regs 1).rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8))) 1 v1) 2 v2,
        pc := s.regs 30 }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Memory.accessible_bound _ h0
  janus_run
  exact ⟨_, _, by rw [rot13]⟩

theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab mulItab ∧ Ptr s.mem h 8 false ∧
        Disjoint h.toNat 8 (s.sp.toNat - 40) 64 ∧ GuardOK s 0 ∧ StackOK s 40 24)
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) ∧
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab rotItab ∧ Ptr s.mem h 8 false ∧
        Disjoint h.toNat 8 (s.sp.toNat - 40) 64 ∧ GuardOK s 0 ∧ StackOK s 40 24)
      (fun s s' => s'.regs 0 = x.rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  constructor
  all_goals
    intro ret hret s hs ⟨hi, ⟨hh, hhb⟩, hd, ⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
    janus_intro hs
    janus_dyn hi
    simp only [Disjoint] at hd
    janus_run calls [mul_summary, rot_summary]

end Proof

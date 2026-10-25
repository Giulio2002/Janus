import Janus
import Extracted

/-!
# `SetNext(n, q *Node)` on amd64: `n.Next = q` through the GC write barrier

**Guarantee.** As for arm64 (`examples/proofs/SetNext.lean`): with `runtime.writeBarrier` off the
call stores `q` at `n` and nothing else; with it on, and room in the current P's write-barrier
buffer (`BarrierOK`), it records `q` and the old `n.Next` in the buffer, advances
`p.wbBuf.next` by 16, and stores `q`.

**What is executed, what is assumed.** The barrier's fast path (`runtime.gcWriteBarrier2`,
`gcWriteBarrier`) is extracted and executed; its flush path `runtime.wbBufFlush` is a contract
that the precondition makes unreachable, so the statement has no contract hypothesis. The field
offsets are read off the barrier's code (`offM`, `offP`, `offNext`, `offEnd`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- Address of `runtime.writeBarrier` (its `enabled` flag), the RIP-relative operand of the
`CMPL $0, …(RIP)` at `SetNext+0xc`, recomputed from the extracted bytes. -/
def wbFlag : Nat := ripTarget Extracted.program (Extracted.entry + 0xc)

/-- The code bytes of the barrier (`gcWriteBarrier<>`). -/
def wbCode : List Nat :=
  ((Extracted.program.segments.find? (·.name == "gcWriteBarrier")).map (·.bytes)).getD []

/-- The little-endian 32-bit displacement at byte `i` of the barrier's code. -/
def disp32 (i : Nat) : Nat :=
  wbCode.getD i 0 + 256 * wbCode.getD (i + 1) 0 + 65536 * wbCode.getD (i + 2) 0 +
    16777216 * wbCode.getD (i + 3) 0

/-- The offsets of `g.m` (`MOVQ 0x30(R14), R13`, an 8-bit displacement), `m.p`,
`p.wbBuf.next` and `p.wbBuf.end`, read off the barrier's code. -/
def offM : Nat := wbCode.getD 0x15 0
def offP : Nat := disp32 0x19
def offNext : Nat := disp32 0x20
def offEnd : Nat := disp32 0x2a

def mOf (s : State) : Nat := s.mem.readLE ((s.regs 14).toNat + offM) 8
def pOf (s : State) : Nat := s.mem.readLE (mOf s + offP) 8
def nextOf (s : State) : Nat := s.mem.readLE (pOf s + offNext) 8
def endOf (s : State) : Nat := s.mem.readLE (pOf s + offEnd) 8

/-- With the barrier enabled: `g.m`, `m.p` and `p.wbBuf.{next,end}` are readable (`next`
writable), the buffer has room for two pointers at `next`, and each of these runtime objects is
separate (`Apart`) from `n.Next` and the stack window; the buffer slots are separate from the cursor field.
(Round 9 S1: this used to require one interval `[lo, hi)` holding all of them and missing `n.Next`
and the stack, which about half of the real calls with the barrier on cannot meet: `g`, `p`,
the goroutine stack and the heap objects interleave in the arena.) -/
def BarrierOK (s : State) (n : Nat) : Prop :=
  s.mem.accessible ((s.regs 14).toNat + offM) 8 false = true ∧
  s.mem.accessible (mOf s + offP) 8 false = true ∧
  s.mem.accessible (pOf s + offNext) 16 true = true ∧
  s.mem.accessible (nextOf s) 16 true = true ∧ nextOf s + 16 ≤ endOf s ∧
  Apart (nextOf s) 16 (pOf s + offNext) 16 ∧
  Apart ((s.regs 14).toNat + offM) 8 n 8 ∧ Apart (mOf s + offP) 8 n 8 ∧
  Apart (pOf s + offNext) 16 n 8 ∧ Apart (nextOf s) 16 n 8 ∧
  Apart ((s.regs 14).toNat + offM) 8 ((s.regs 4).toNat - 136) 144 ∧ Apart (mOf s + offP) 8 ((s.regs 4).toNat - 136) 144 ∧
  Apart (pOf s + offNext) 16 ((s.regs 4).toNat - 136) 144 ∧ Apart (nextOf s) 16 ((s.regs 4).toNat - 136) 144 ∧
  (s.regs 14).toNat + offM + 8 ≤ 2 ^ 48 ∧ mOf s + offP + 8 ≤ 2 ^ 48 ∧ pOf s + offNext + 16 ≤ 2 ^ 48 ∧
  nextOf s + 16 ≤ 2 ^ 48

theorem correctness (n q : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n, q]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 136 8 ∧ Buffer s n 8 true ∧
        s.mem.accessible wbFlag 4 false = true ∧
        Separated [(n.toNat, 8), ((s.regs 4).toNat - 136, 144), (wbFlag, 4)] ∧
        (s.mem.readLE wbFlag 4 ≠ 0 → BarrierOK s n.toNat))
      (fun s s' => s'.mem.readLE n.toNat 8 = q.toNat ∧
        (s.mem.readLE wbFlag 4 = 0 → MemFrame s.mem s'.mem
          [(n.toNat, n.toNat + 8), ((s.regs 4).toNat - 136, (s.regs 4).toNat)]) ∧
        (s.mem.readLE wbFlag 4 ≠ 0 →
          s'.mem.readLE (nextOf s) 8 = q.toNat ∧
          s'.mem.readLE (nextOf s + 8) 8 = s.mem.readLE n.toNat 8 ∧
          s'.mem.readLE (pOf s + offNext) 8 = nextOf s + 16 ∧
          MemFrame s.mem s'.mem [(n.toNat, n.toNat + 8), (nextOf s, nextOf s + 16),
            (pOf s + offNext, pOf s + offNext + 8), ((s.regs 4).toNat - 136, (s.regs 4).toNat)])) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, ⟨hn', hn⟩, hfa, hsep, hbar⟩
  janus64_intro hs
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw ⊢
  janus_eval_nat h_wf : wbFlag
  by_cases hf : s.mem.readLE wbFlag 4 = 0
  all_goals simp only [h_wf, separated_cons, separated_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true] at *
  · janus64_run
    exact ⟨by janus_frame, fun h => h.elim⟩
  · obtain ⟨hb1, hb2, hb3, hb4, hb5, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hh1, hh2, hh3, hh4⟩ := hbar hf
    clear hbar
    janus_eval_nat h_o4 : offM
    janus_eval_nat h_o5 : offP
    janus_eval_nat h_o6 : offNext
    janus_eval_nat h_o7 : offEnd
    simp only [h_o4, h_o5, h_o6, h_o7, mOf, pOf, nextOf, endOf, Spec.Disjoint] at hb1 hb2 hb3 hb4 hb5 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hh1 hh2 hh3 hh4 ⊢
    janus64_run
    exact ⟨fun h => h.elim, by janus_frame⟩

end Proof

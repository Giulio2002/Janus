import Extracted

/-!
# `SetNext(n, q *Node)` stores `q` into `n.Next`, through the GC write barrier

**Guarantee.** For all pointers `n`, `q` and every Go call state of `example.com/basic.SetNext` in
which the stack-growth prologue falls through, `[SP-248, SP)` is writable, the field `n.Next` is
writable, the flag `runtime.writeBarrier.enabled` (a writable global the code reads as a 32-bit
word at `wbFlag`) is readable, and these three are separate:

* **barrier off** (`flag = 0`): the call stores `q` at `n` and changes nothing else (besides the
  stack window);
* **barrier on** (`flag ≠ 0`), when the current P's write-barrier buffer has room for two
  pointers (`BarrierOK`: `g.m`, `m.p`, `p.wbBuf.next/end` readable inside a runtime area `[lo, hi)`
  separate from `n.Next` and the stack): the call records the new pointer `q` and the old value of
  `n.Next` in the two buffer slots at `next`, advances `p.wbBuf.next` by 16, stores `q` at `n`, and
  changes nothing else.

**What is executed, what is assumed.** The barrier's fast path (`runtime.gcWriteBarrier2` and the
shared `gcWriteBarrier`, 43 instructions) is extracted and executed: nothing about it is assumed.
Only its slow path, the buffer flush `runtime.wbBufFlush`, is a contract
(`janus extract --contract runtime.wbBufFlush`), and the precondition (buffer has room) makes it
unreachable, so the statement needs no contract hypothesis. The offsets of `g.m`, `m.p` and the
buffer fields are read off the barrier's code (`ldrOff`), not copied by hand.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- Address of `runtime.writeBarrier` (its `enabled` flag, read as a 32-bit word by the
`ADRP` + `LDR W` at `SetNext+0x1c`), recomputed from the extracted words. -/
def wbFlag : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/basic.SetNext" 7)
    (segWord Extracted.program "example.com/basic.SetNext" 8) 2

/-- The unsigned offset of the `LDR X` at word `i` of the barrier's code (`gcWriteBarrier<>`). -/
def ldrOff (i : Nat) : Nat := bits (segWord Extracted.program "gcWriteBarrier" i) 21 10 * 8
/-- The offsets of `g.m`, `m.p`, `p.wbBuf.next` and `p.wbBuf.end`, read off the barrier's code. -/
def offM : Nat := ldrOff 4
def offP : Nat := ldrOff 5
def offNext : Nat := ldrOff 6
def offEnd : Nat := ldrOff 7

/-- The current `m` (`g.m`), `p` (`m.p`) and write-barrier buffer cursor/limit of a state. -/
def mOf (s : State) : Nat := s.mem.readLE ((s.regs 28).toNat + offM) 8
def pOf (s : State) : Nat := s.mem.readLE (mOf s + offP) 8
def nextOf (s : State) : Nat := s.mem.readLE (pOf s + offNext) 8
def endOf (s : State) : Nat := s.mem.readLE (pOf s + offEnd) 8

/-- With the barrier enabled: `g.m`, `m.p` and `p.wbBuf.{next,end}` are readable (`next`
writable), the buffer has room for two pointers at `next`, all of these lie in the runtime's
memory `[lo, hi)`, which is separate from `n.Next` and the stack window, and the buffer slots are
separate from the cursor field. -/
def BarrierOK (s : State) (n lo hi : Nat) : Prop :=
  s.mem.accessible ((s.regs 28).toNat + offM) 8 false = true ∧
  s.mem.accessible (mOf s + offP) 8 false = true ∧
  s.mem.accessible (pOf s + offNext) 16 true = true ∧
  s.mem.accessible (nextOf s) 16 true = true ∧ nextOf s + 16 ≤ endOf s ∧
  lo ≤ (s.regs 28).toNat + offM ∧ (s.regs 28).toNat + offM + 8 ≤ hi ∧
  lo ≤ mOf s + offP ∧ mOf s + offP + 8 ≤ hi ∧
  lo ≤ pOf s + offNext ∧ pOf s + offNext + 16 ≤ hi ∧
  lo ≤ nextOf s ∧ nextOf s + 16 ≤ hi ∧
  Disjoint (nextOf s) 16 (pOf s + offNext) 16 ∧
  Disjoint lo (hi - lo) n 8 ∧ Disjoint lo (hi - lo) (s.sp.toNat - 248) 248 ∧ hi ≤ 2 ^ 48

theorem correctness (n q : BitVec 64) (lo hi : Nat) :
    Ensures Extracted.program Extracted.entry [n, q]
      (fun s => GuardOK s 0 ∧ StackOK s 248 0 ∧ Ptr s.mem n 8 true ∧
        s.mem.accessible wbFlag 4 false = true ∧
        Separated [(n.toNat, 8), (s.sp.toNat - 248, 248), (wbFlag, 4)] ∧
        (s.mem.readLE wbFlag 4 ≠ 0 → BarrierOK s n.toNat lo hi))
      (fun s s' => s'.mem.readLE n.toNat 8 = q.toNat ∧
        (s.mem.readLE wbFlag 4 = 0 →
          MemFrame s.mem s'.mem [(n.toNat, n.toNat + 8), (s.sp.toNat - 248, s.sp.toNat)]) ∧
        (s.mem.readLE wbFlag 4 ≠ 0 →
          s'.mem.readLE (nextOf s) 8 = q.toNat ∧
          s'.mem.readLE (nextOf s + 8) 8 = s.mem.readLE n.toNat 8 ∧
          s'.mem.readLE (pOf s + offNext) 8 = nextOf s + 16 ∧
          MemFrame s.mem s'.mem [(n.toNat, n.toNat + 8), (nextOf s, nextOf s + 16),
            (pOf s + offNext, pOf s + offNext + 8), (s.sp.toNat - 248, s.sp.toNat)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hn, hn'⟩, hfa, hsep, hbar⟩
  janus_intro hs
  janus_eval_nat h_wf : wbFlag
  by_cases hf : s.mem.readLE wbFlag 4 = 0
  all_goals simp only [h_wf, separated_cons, separated_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, and_true] at *
  · janus_run
    exact ⟨by janus_frame, fun h => h.elim⟩
  · obtain ⟨hb1, hb2, hb3, hb4, hb5, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hd1, hd2, hd3, hhi⟩ := hbar hf
    clear hbar
    janus_eval_nat h_o4 : offM
    janus_eval_nat h_o5 : offP
    janus_eval_nat h_o6 : offNext
    janus_eval_nat h_o7 : offEnd
    simp only [h_o4, h_o5, h_o6, h_o7, mOf, pOf, nextOf, endOf, Disjoint] at hb1 hb2 hb3 hb4 hb5 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hd1 hd2 hd3 hhi ⊢
    janus_run
    exact ⟨fun h => h.elim, by janus_frame⟩

end Proof

import Janus
import Extracted

/-! `example.com/basic.AtomicMax(p *uint64, v uint64) uint64` on amd64: a compare-and-swap
retry loop.

```
      JMP load
retry: MOVQ DX, AX
load:  MOVQ 0(AX), CX ; CMPQ CX, BX ; JAE done          // old := *p; old >= v: done
       MOVQ AX, DX ; MOVQ CX, AX
       LOCK CMPXCHGQ BX, 0(DX) ; SETEQ SI               // CompareAndSwap(p, old, v)
       NOPL ; TESTL SI, SI ; JEQ retry
done:  MOVQ CX, AX ; RET
```

The model is single-threaded: nothing changes `*p` between the load and the `CMPXCHG`, so the
compare-and-swap succeeds the first time and the retry edge is never taken (the symbolic
execution proves the failure branch infeasible). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `AtomicMax(p, v)` returns the old value of `*p` and leaves `*p = max(old, v)` (unsigned).
The word must be writable, 8-byte aligned (as Go aligns every `*uint64`; a locked access
that splits a cache line faults in the model, see `docs/AMD64.md`) and must not overlap the
return-address slot. -/
theorem correctness (p v : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, v]
      (fun s => StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) ∧
        s'.mem.readLE p.toNat 8 = max (s.mem.readLE p.toNat 8) v.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩, hal, hd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hd
  janus64_run
  all_goals omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def p : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def v : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 3 then v else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, v] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64) (v : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, v] s ∧ (StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) ∧
        s'.mem.readLE p.toNat 8 = max (s.mem.readLE p.toNat 8) v.toNat) :=
  ⟨ret, s0, p, v, hret, setup, hpre, correctness p v ret hret s0 setup hpre⟩

end Witness

end Proof

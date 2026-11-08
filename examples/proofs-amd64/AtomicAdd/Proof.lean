import Janus
import Extracted

/-! `example.com/basic.AtomicAdd(p *uint64, d uint64) uint64` on amd64:

```
MOVQ BX, CX ; LOCK XADDQ BX, 0(AX) ; LEAQ 0(CX)(BX*1), AX ; RET
```

`atomic.AddUint64` is inlined as `LOCK XADDQ`, which leaves the old value of `*p` in `BX`;
the new value is recomputed as `old + d`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `AtomicAdd(p, d)` adds `d` to the word at `p` and returns the new value: afterwards
`*p = old + d` (mod 2^64) and the result is the same value. The model is single-threaded, so
`LOCK XADD` is an ordinary read-modify-write. The word must be writable, 8-byte aligned (as Go
aligns every `*uint64`; a locked access that splits a cache line faults in the model, see
`docs/AMD64.md`) and must not overlap the return-address slot. -/
theorem correctness (p d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, d]
      (fun s => StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) + d ∧
        s'.mem.readLE p.toNat 8 = (s'.regs 0).toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hpw, hp⟩, hal, hd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hd
  janus64_run
  exact ⟨BitVec.add_comm _ _, by rw [Nat.add_comm]⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def p : BitVec 64 := 0x30800#64
def d : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 3 then d else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, d] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, d] s ∧ (StackWritable s 0 8 ∧ Buffer s p 8 true ∧ p.toNat % 8 = 0 ∧
        Disjoint p 8 (s.regs regSP) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) + d ∧
        s'.mem.readLE p.toNat 8 = (s'.regs 0).toNat) :=
  ⟨ret, s0, p, d, hret, setup, hpre, correctness p d ret hret s0 setup hpre⟩

end Witness

end Proof

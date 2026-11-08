import Extracted

/-!
# `DotBoth(a, b, c, d uint64) uint64`: a method value and a method expression (value receiver)

**Guarantee.** For all 64-bit `a`, `b`, `c`, `d` and every Go call state `s` of
`example.com/basic.DotBoth` whose memory holds the function's read-only data (`DataLoaded`; the
static funcval of `Vec2.Dot`), whose stack-growth prologues fall through (`GuardOK s 128`, the
guard word outside the stack window) and whose `SP` is aligned with `[SP-192, SP+40)` writable
(the frames of `DotBoth`, `applyVec`, `applyVec2` and the wrapper `Vec2.Dot-fm`, and the
caller's spill area for the four arguments), the call returns (never faulting or panicking),
obeys the ABI, and `X0 = (a, b)·(c, d) + (a, b)·(d, c) = a·c + b·d + a·d + b·c mod 2^64`.

**What is exercised.** `Vec2.Dot` has a value receiver (passed in registers, `X0`, `X1`).
* The method value `v.Dot` is a closure over a copy of `v`: `DotBoth` builds it in its frame (the
  address of the wrapper `Vec2.Dot-fm`, then `a`, `b`); `applyVec` calls it through `blr`, and
  the wrapper reads the receiver through `X26` and calls `Vec2.Dot` directly.
* The method expression `Vec2.Dot` is a function of `(v, w)`: a static funcval in `.rodata`
  (`Vec2.Dot·f`) whose code word is `Vec2.Dot` itself; `applyVec2` calls it through `blr`.

Both calls are resolved by the executor from memory: the first from stores of the code being
proved, the second from the extracted read-only data.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => Extracted.program.DataLoaded s.mem ∧ GuardOK s 128 ∧ StackOK s 192 40 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 192) 232)
      (fun _ s' => (s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_data hd [hw]
  janus_run
  janus_arith


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def wbytes (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (1) else if i = 1 then (2) else if i = 2 then (3) else if i = 3 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64), (2 : BitVec 64), (3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64) (c : BitVec 64) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b, c, d] s ∧ (Extracted.program.DataLoaded s.mem ∧ GuardOK s 128 ∧ StackOK s 192 40 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 192) 232) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64)) := by
  refine ⟨ret, s0, (1), (2), (3), (4), hret, setup, ?pre, correctness (1) (2) (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, dataByte, sp0, g0, hp]
    all_goals decide

end Witness

end Proof

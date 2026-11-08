import Extracted

/-!
# `SwapBig(a, b *Big)`: struct assignment by value (a 64-byte struct)

**Guarantee.** For all pointers `a`, `b` to 64 writable bytes (the eight-word struct `Big`) that
are either the same struct or disjoint, both disjoint from the function's stack window
(`[SP-88, SP)`), and every Go call state of `example.com/basic.SwapBig` satisfying Go's
frame-pointer invariant (`FPConvention`: `X29` is restored arithmetically), the call returns
(never faulting or panicking), obeys the ABI, and afterwards every word `i < 8` of `*a` is word
`i` of `*b` before the call and vice versa. For `a = b` this says the struct is unchanged.

`*a, *b = *b, *a` evaluates both right-hand sides first: the compiler copies `*a` into a frame
temporary (four `ldp`/`stp` pairs), copies `*b` over `*a`, then the temporary over `*b`. No
`memmove` or `duffcopy` is involved.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => FPConvention s ∧ StackOK s 88 0 ∧ Ptr s.mem a 64 true ∧ Ptr s.mem b 64 true ∧
        (a = b ∨ Disjoint a.toNat 64 b.toNat 64) ∧
        Disjoint a.toNat 64 (s.sp.toNat - 88) 88 ∧ Disjoint b.toNat 64 (s.sp.toNat - 88) 88)
      (fun s s' => ∀ i < 8, s'.mem.readLE (a.toNat + 8 * i) 8 = s.mem.readLE (b.toNat + 8 * i) 8 ∧
        s'.mem.readLE (b.toNat + 8 * i) 8 = s.mem.readLE (a.toNat + 8 * i) 8) := by
  intro ret hret s hs ⟨hfp, ⟨hal, hsb, hsa, hw⟩, ⟨ha, ha'⟩, ⟨hb, hb'⟩, hab, hda, hdb⟩
  janus_intro hs
  simp only [Disjoint] at hda hdb
  simp only [FPConvention, regFP] at hfp
  rcases hab with rfl | hab
  all_goals try simp only [Disjoint] at hab
  all_goals janus_run
  all_goals intro i hi8; janus_cases hi8
  all_goals janus_simp


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0x300100) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0x300100 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ (FPConvention s ∧ StackOK s 88 0 ∧ Ptr s.mem a 64 true ∧ Ptr s.mem b 64 true ∧
        (a = b ∨ Disjoint a.toNat 64 b.toNat 64) ∧
        Disjoint a.toNat 64 (s.sp.toNat - 88) 88 ∧ Disjoint b.toNat 64 (s.sp.toNat - 88) 88) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (∀ i < 8, s'.mem.readLE (a.toNat + 8 * i) 8 = s.mem.readLE (b.toNat + 8 * i) 8 ∧
        s'.mem.readLE (b.toNat + 8 * i) 8 = s.mem.readLE (a.toNat + 8 * i) 8)) := by
  refine ⟨ret, s0, (0x300000), (0x300100), hret, setup, ?pre, correctness (0x300000) (0x300100) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof

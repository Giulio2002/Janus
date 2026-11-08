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


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def tab1 : BitVec 64 := BitVec.ofNat 64 (Janus.Spec.dataAddr Extracted.program.data mulItab)
def tab2 : BitVec 64 := BitVec.ofNat 64 (Janus.Spec.dataAddr Extracted.program.data rotItab)

def dataByte (a : Nat) : Option Byte :=
  match Extracted.program.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def wbytes (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩] ++ Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then (tab1) else if i = 1 then (hp) else if i = 2 then (7) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(tab1 : BitVec 64), (hp : BitVec 64), (7 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩
def s1 : State := { s0 with regs := fun i => if i = 0 then tab2 else s0.regs i }

theorem setup1 : CallSetup (Extracted.program.withExit ret) Extracted.entry [(tab2 : BitVec 64), (hp : BitVec 64), (7 : BitVec 64)] s1 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem itab0 : ItabIs Extracted.program.data s0.mem tab1 mulItab := by
  refine ⟨_, rfl, ?_, ?_⟩
  · decide
  · unfold Janus.Spec.SegLoaded; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem itab1 : ItabIs Extracted.program.data s1.mem tab2 rotItab := by
  refine ⟨_, rfl, ?_, ?_⟩
  · decide
  · unfold Janus.Spec.SegLoaded; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rest0 : Ptr s0.mem (hp : BitVec 64) 8 false ∧ Disjoint (hp : BitVec 64).toNat 8 (s0.sp.toNat - 40) 64 ∧ GuardOK s0 0 ∧ StackOK s0 40 24 := by
  simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rest1 : Ptr s1.mem (hp : BitVec 64) 8 false ∧ Disjoint (hp : BitVec 64).toNat 8 (s1.sp.toNat - 40) 64 ∧ GuardOK s1 0 ∧ StackOK s1 40 24 := by
  simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s1, s0, wmem, wbytes, sp0, g0, hp]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nonvacuous : ∃ (ret : Nat) (s s' : State) (tab h x tab2 h2 x2 : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tab, h, x] s ∧
    (ItabIs Extracted.program.data s.mem tab mulItab ∧ Ptr s.mem h 8 false ∧
        Disjoint h.toNat 8 (s.sp.toNat - 40) 64 ∧ GuardOK s 0 ∧ StackOK s 40 24) ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tab2, h2, x2] s' ∧
    (ItabIs Extracted.program.data s'.mem tab2 rotItab ∧ Ptr s'.mem h2 8 false ∧
        Disjoint h2.toNat 8 (s'.sp.toNat - 40) 64 ∧ GuardOK s' 0 ∧ StackOK s' 40 24) ∧
    (Returns (Extracted.program.withExit ret) s fun t =>
      ABIReturn s t ∧ (t.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8))) ∧
    (Returns (Extracted.program.withExit ret) s' fun t =>
      ABIReturn s' t ∧ (t.regs 0 = x2.rotateLeft 13 + BitVec.ofNat 64 (s'.mem.readLE h2.toNat 8))) :=
  ⟨ret, s0, s1, tab1, hp, 7, tab2, hp, 7, hret, setup, ⟨itab0, rest0.1, rest0.2.1, rest0.2.2.1, rest0.2.2.2⟩,
    setup1, ⟨itab1, rest1.1, rest1.2.1, rest1.2.2.1, rest1.2.2.2⟩,
    (correctness tab1 hp 7).1 ret hret s0 setup ⟨itab0, rest0.1, rest0.2.1, rest0.2.2.1, rest0.2.2.2⟩,
    (correctness tab2 hp 7).2 ret hret s1 setup1 ⟨itab1, rest1.1, rest1.2.1, rest1.2.2.1, rest1.2.2.2⟩⟩

end Witness

end Proof

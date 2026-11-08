import Janus
import Extracted

/-! `example.com/basic.HashWith(h Hasher, x)` on amd64: the interface method call `h.Hash(x)`
(`MOVQ 24(AX), DX; CALL DX`), with the itab `tab` in `RAX`, the receiver `h` in `RBX` and `x` in
`RCX`.

For every call state whose stack-growth check falls through, with `[RSP-32, RSP+24)` writable and
the receiver's field `K` (8 bytes at `h`) readable outside it: if `tab` is the static itab of
`*MulHasher` for `Hasher` (`ItabIs`: its address, with its 32 bytes from `.rodata` in read-only
memory), the call returns `x · K`; if it is the itab of `*RotHasher`, it returns
`rotl(x, 13) + K`.

The itab is a hypothesis of the theorem, not something derived from Go's types. Both methods are
proved once as callee summaries; `janus_dyn hi` turns `ItabIs` into the itab's literal address
and words, so `janus64_run` finds a literal `CALL` target and applies that method's summary. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Janus.Spec (ItabIs)

abbrev mulItab : String := "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
abbrev rotItab : String := "go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher"

theorem mul_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*MulHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with
        regs := setRegF (setRegF s.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * s.regs 3)) 4
          (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Janus.Arm64.Memory.accessible_bound _ h0
  janus64_run
  exact ⟨_, rfl⟩

theorem rot_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.(*RotHasher).Hash")
      (fun s => s.mem.accessible (s.regs 0).toNat 8 false = true ∧
        s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ v3 f, s' = { s with
        regs := setRegF (setRegF (setRegF s.regs 0
          ((s.regs 3).rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8))) 3 v3) 4
          (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h0, h1, h2⟩
  have := Janus.Arm64.Memory.accessible_bound _ h0
  janus64_run
  exact ⟨_, _, rfl⟩

theorem correctness (tab h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab mulItab ∧ Buffer s h 8 false ∧
        StackGuardOK s 0 ∧ StackWritable s 32 24 ∧
        ((s.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 32))
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) ∧
    Ensures Extracted.program Extracted.entry [tab, h, x]
      (fun s => ItabIs Extracted.program.data s.mem tab rotItab ∧ Buffer s h 8 false ∧
        StackGuardOK s 0 ∧ StackWritable s 32 24 ∧
        ((s.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 32))
      (fun s s' => s'.regs 0 = x.rotateLeft 13 + BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  constructor
  all_goals
    intro ret hret s hs ⟨hi, ⟨hhb, hh⟩, hg, ⟨hle, hnw, hacc⟩, hd⟩
    janus64_intro hs
    have hgl := hg.load
    have hgb := hg.below
    have hnw2 := hg.noWrap
    have hgr := hg.readable
    simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
    janus_dyn hi
    janus64_run calls [mul_summary, rot_summary]
  rw [BitVec.mul_comm]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def mem : Memory := withData Extracted.program.data wmem64

def tabM : BitVec 64 := BitVec.ofNat 64 (Janus.Spec.dataAddr Extracted.program.data mulItab)
def tabR : BitVec 64 := BitVec.ofNat 64 (Janus.Spec.dataAddr Extracted.program.data rotItab)
def h : BitVec 64 := 0x30800#64
def x : BitVec 64 := 3#64

def s0M : State :=
  { regs := fun r_ => if r_ = 0 then tabM else if r_ = 3 then h else if r_ = 1 then x
      else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

def s0R : State := { s0M with regs := fun r_ => if r_ = 0 then tabR else s0M.regs r_ }

theorem setups0M :
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tabM, h, x] s0M :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i hi; simp at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem itabs0M : ItabIs Extracted.program.data s0M.mem tabM mulItab := by
  refine ⟨_, rfl, ?_, ?_⟩
  · decide +kernel
  · unfold Janus.Spec.SegLoaded; decide +kernel

set_option maxRecDepth 100000 in
theorem rests0M : Buffer s0M h 8 false ∧
    StackGuardOK s0M 0 ∧ StackWritable s0M 32 24 ∧
    ((s0M.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s0M.regs 4).toNat - 32) := by
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

theorem setups0R :
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tabR, h, x] s0R :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i hi; simp at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem itabs0R : ItabIs Extracted.program.data s0R.mem tabR rotItab := by
  refine ⟨_, rfl, ?_, ?_⟩
  · decide +kernel
  · unfold Janus.Spec.SegLoaded; decide +kernel

set_option maxRecDepth 100000 in
theorem rests0R : Buffer s0R h 8 false ∧
    StackGuardOK s0R 0 ∧ StackWritable s0R 32 24 ∧
    ((s0R.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s0R.regs 4).toNat - 32) := by
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

theorem nonvacuous : ∃ (ret : Nat) (s s' : State) (tab h x tab' h' x' : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tab, h, x] s ∧
    (ItabIs Extracted.program.data s.mem tab mulItab ∧ Buffer s h 8 false ∧
        StackGuardOK s 0 ∧ StackWritable s 32 24 ∧
        ((s.regs 4).toNat + 24 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 32)) ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [tab', h', x'] s' ∧
    (ItabIs Extracted.program.data s'.mem tab' rotItab ∧ Buffer s' h' 8 false ∧
        StackGuardOK s' 0 ∧ StackWritable s' 32 24 ∧
        ((s'.regs 4).toNat + 24 ≤ h'.toNat ∨ h'.toNat + 8 ≤ (s'.regs 4).toNat - 32)) ∧
    (Returns (Extracted.program.withExit ret) s fun t =>
      ABIReturn s t ∧ t.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) ∧
    (Returns (Extracted.program.withExit ret) s' fun t =>
      ABIReturn s' t ∧ t.regs 0 = x'.rotateLeft 13 + BitVec.ofNat 64 (s'.mem.readLE h'.toNat 8)) :=
  ⟨ret, s0M, s0R, tabM, h, x, tabR, h, x, hret, setups0M, ⟨itabs0M, rests0M⟩, setups0R,
    ⟨itabs0R, rests0R⟩,
    (correctness tabM h x).1 ret hret s0M setups0M ⟨itabs0M, rests0M⟩,
    (correctness tabR h x).2 ret hret s0R setups0R ⟨itabs0R, rests0R⟩⟩

end Witness

end Proof

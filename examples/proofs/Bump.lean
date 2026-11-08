import Extracted

/-!
# `Bump(d uint64) uint64`: a writable package variable (`counter += d`)

**Guarantee.** For every 64-bit `d` and every Go call state `s` of `example.com/basic.Bump` whose
memory makes the 8 bytes of the package variable `example.com/basic.counter` writable, the call
returns (never faulting or panicking), obeys the ABI, `X0 = counter + d mod 2^64` (with
`counter` read before the call), and afterwards `counter` holds that value: memory is `s.mem`
with exactly that store.

The extractor does not copy writable globals (their contents are not fixed by the binary), so
the precondition states the variable's bytes at the address the code computes; `counter`
recomputes it from the extracted `ADRP`/`LDR` words (`adrpLdTarget`), so the statement does not
depend on where the linker put the variable.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `example.com/basic.counter` (`.noptrbss`): the word the first two instructions
(`ADRP` + `LDR`) read. -/
def counter : Nat :=
  adrpLdTarget Extracted.entry (segWord Extracted.program "example.com/basic.Bump" 0)
    (segWord Extracted.program "example.com/basic.Bump" 1) 3

theorem correctness (d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d] (fun s => s.mem.accessible counter 8 true = true)
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE counter 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE counter 8 ((s.mem.readLE counter 8 + d.toNat) % 2 ^ 64)) := by
  intro ret hret s hs hc
  janus_intro hs
  janus_eval_nat h_c : counter
  rw [h_c] at hc ⊢
  janus_run


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩, ⟨counter, 8, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (1) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(1 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [d] s ∧ (s.mem.accessible counter 8 true = true) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (s.mem.readLE counter 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE counter 8 ((s.mem.readLE counter 8 + d.toNat) % 2 ^ 64))) := by
  refine ⟨ret, s0, (1), hret, setup, ?pre, correctness (1) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp, counter] <;> decide

end Witness

end Proof

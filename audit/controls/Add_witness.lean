import Extracted

/-!
# `Add(x, y uint64) uint64` returns `x + y` modulo `2^64`

**Guarantee.** For all 64-bit inputs `x` and `y`, and for every machine state that is a Go call
of `example.com/basic.Add` with `x` in `X0` and `y` in `X1` (`pc` at the function, any
admissible return address in `X30` (`RetAddr`: 4-aligned, below `2^48`, outside the extracted
code and stubs); all other registers, flags, the stack pointer and all of memory arbitrary),
the compiled arm64 code returns to that address after finitely many instructions, never
faulting or panicking, restores `SP`, `X18`, `X28` (`g`) and `X29` (frame pointer), and leaves
`x + y` (wrapped to 64 bits) in `X0`.

**What it rules out.** Any other result, a fault (undecodable instruction, memory access, jump
outside the extracted code), a panic, or running forever. It says nothing about states that are
not such a call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof

/-! ## Positive control (audit): the precondition is satisfiable and the theorem applies. -/
namespace AuditWitness
open Janus Janus.Arm64 Janus.GoABI
/-- An admissible return address (outside the code). -/
def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def s0 (x y : BitVec 64) : State :=
  { regs := fun i => if i = 0 then x else if i = 1 then y else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := 0x10000, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, []⟩ }
theorem setup (x y : BitVec 64) :
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] (s0 x y) :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ |  i <;> simp [s0] at h ⊢ <;> omega⟩
-- The theorem's conclusion for a concrete call: 2^64-1 + 2 returns 1.
example : ∃ fuel s', (Extracted.program.withExit ret).run fuel (s0 (-1) 2) = .ok (.returned s') ∧
    (s'.regs 0).toNat = 1 := by
  obtain ⟨f, s', h1, _, h2⟩ := Proof.correctness (-1) 2 ret hret (s0 (-1) 2) (setup _ _) trivial
  exact ⟨f, s', h1, by rw [h2]; decide⟩
end AuditWitness

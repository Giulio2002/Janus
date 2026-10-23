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

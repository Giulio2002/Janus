import Extracted

/-!
# The subtracting `Add` violates the `Add` specification

This file is verified against the binary built by `scripts/break-demo.sh`, in which the Go
source of `Add` was changed from `x + y` to `x - y`.

**Guarantee.** It is *not* the case that for all `x`, `y` every Go call of the compiled function
returns `(x + y) mod 2^64`. Concretely, for `x = 0`, `y = 1` and the admissible return address
`0x1000`, a call (built from an arbitrary machine state by `GoABI.setup`) returns `2^64 - 1`,
not `1`. So the specification proved in `Add.lean` is false of this binary, and no proof of it
can be accepted.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness :
    ¬ ∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro h
  -- a concrete admissible return address (outside the code, 4-aligned, below `2^48`)
  have hret : RetAddr Extracted.program 0x1000 := RetAddr.of_check (by decide)
  let s := setup (Extracted.program.withExit 0x1000) Extracted.entry [0#64, 1#64] default
  have hs : CallSetup (Extracted.program.withExit 0x1000) Extracted.entry [0#64, 1#64] s :=
    setup_callSetup _ (by decide)
  -- what the spec claims
  have hspec := (h 0#64 1#64).returns hret hs trivial
  -- what the code does
  have hcode : Returns (Extracted.program.withExit 0x1000) s
      (fun s' => (s'.regs 0).toNat = 2 ^ 64 - 1) := by
    janus_intro hs
    janus_run
  obtain ⟨_, _, _, ⟨_, hbad⟩, hgood⟩ := hspec.unique hcode
  rw [hgood] at hbad
  simp at hbad

end Proof

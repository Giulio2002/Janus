import Extracted

/-!
# The subtracting `Add` violates the `Add` specification

This file is verified against the binary built by `scripts/break-demo.sh`, in which the Go
source of `Add` was changed from `x + y` to `x - y`.

**Guarantee.** It is *not* the case that for all `x`, `y` every Go call of the compiled function
returns `(x + y) mod 2^64`. Concretely, for `x = 0`, `y = 1`, a call (built from an arbitrary
machine state by `GoABI.setup`) returns `2^64 - 1`, not `1`. So the specification proved in
`Add.lean` is false of this binary, and no proof of it can be accepted.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness :
    ¬ ∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro h
  let s := setup Extracted.program Extracted.entry [0#64, 1#64] default
  have hs : CallSetup Extracted.program Extracted.entry [0#64, 1#64] s :=
    setup_callSetup _ (by decide)
  -- what the spec claims
  have hspec := (h 0#64 1#64).returns hs trivial
  -- what the code does
  have hcode : Returns Extracted.program s (fun s' => (s'.regs 0).toNat = 2 ^ 64 - 1) := by
    janus_intro hs
    janus_run
  obtain ⟨_, _, _, ⟨_, hbad⟩, hgood⟩ := hspec.unique hcode
  rw [hgood] at hbad
  simp at hbad

end Proof

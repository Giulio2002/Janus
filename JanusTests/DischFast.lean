import Janus

/-!
# The discharger's two fast paths (Janus/Tactic/Core.lean)

* `dischargeSpAligned`: `(sp ± multiples of 16).toNat % 16 = 0` from the alignment hypothesis, without `omega` (the `baseAddr_sp` goal of every
  stack access of a C function).
* `lowBoundHopeless`: `(v : BitVec 128).toNat < 2 ^ 64` is given up at once when no hypothesis mentions `v` (the `mod64_of_lt` goal of
  `stp d8, d9`), and is still proved when one does.
-/

open Janus Janus.Arm64 Janus.Tactic Lean Elab Tactic Meta

/-- `must_fail_disch T`: `janus_disch` must NOT prove `T` in the current context (the main goal is untouched). -/
elab "must_fail_disch " t:term : tactic => withMainContext do
  let ty ← Term.elabTerm t (some (mkSort Level.zero))
  let m ← mkFreshExprMVar ty
  let proved ← try
      let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| janus_disch)))
      pure gs.isEmpty
    catch _ => pure false
  if proved then throwError "janus_disch proved a goal it must not prove: {ty}"

example (s : Janus.Arm64.State) (h : s.sp.toNat % 16 = 0) :
    (Janus.Arm64.State.sp { s with sp := s.sp - 64#64, pc := 5 }).toNat % 16 = 0 := by janus_disch

example (s : Janus.Arm64.State) (h : s.sp.toNat % 16 = 0) :
    (Janus.Arm64.State.sp { s with sp := s.sp - 64#64 + 32#64, pc := 5 }).toNat % 16 = 0 := by janus_disch

example (s : Janus.Arm64.State) (h : s.sp.toNat % 16 = 0) : (s.sp - 64#64 - 4096#64 + 16#64).toNat % 16 = 0 := by janus_disch

-- a wrap-around changes nothing (2^64 is a multiple of 16)
example (s : Janus.Arm64.State) (h : s.sp.toNat % 16 = 0) : (s.sp - 18446744073709551600#64).toNat % 16 = 0 := by janus_disch

-- an offset that is not a multiple of 16, or no alignment hypothesis: not proved
example (s : Janus.Arm64.State) (h : s.sp.toNat % 16 = 0) : True := by
  must_fail_disch (s.sp - 8#64).toNat % 16 = 0
  trivial
example (s : Janus.Arm64.State) : True := by
  must_fail_disch (s.sp - 64#64).toNat % 16 = 0
  trivial

-- a 128-bit register is not below 2^64 without a hypothesis ...
example (s : Janus.Arm64.State) : True := by
  must_fail_disch (s.vregs 12).toNat < 18446744073709551616
  trivial

-- ... and is when one says so (the fast failure does not fire when a hypothesis mentions the register)
example (s : Janus.Arm64.State) (h : (s.vregs 12).toNat < 18446744073709551616) : (s.vregs 12).toNat < 18446744073709551616 := by janus_disch

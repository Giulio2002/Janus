import Janus.Contracts.ICall
import Janus.Contracts.AllocAmd64

/-!
# An abstract callee: a dynamic interface method call to arbitrary code (amd64)

The amd64 form of `Janus.Contracts.ICall` (read it for the meaning of every part). The call is
`CALL reg` through the itab's `Fun[0]` word; the receiver data word is in `RAX`, the slice in
`RBX` (pointer), `RCX` (length), `RDI` (capacity); the results `n`, `err.tab`, `err.data` come back in
`RAX`, `RBX`, `RCX`. The call returns with `RSP` the call-time value plus 8 (the return address
popped), `RBP` and `R14` (`g`) preserved and `X15` unchanged; everything else is arbitrary.
-/

namespace Janus.Contracts.ICall

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts

/-- The target of an indirect call is an address the executor can branch to (amd64): below `2^47` (canonical user
address). See `Janus.Contracts.ICall.CodePtrOK`; `Ensures` is total, so a theorem states this about the callee's address. -/
def CodePtrOK64 (fn : Nat) : Prop := fn < 2 ^ 47

/-- The precondition of the call (amd64): `CallOK64`, `above ≥ 8 + 8·nargs` with `[RSP, RSP + above)` (the return
address slot and the caller's frame) outside every range of `rt`, and the call-site property `P`. -/
def ICallPre64 (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop) (s : State) : Prop :=
  CallOK64 s stack nargs ∧ 8 + 8 * nargs ≤ above ∧ Outside (s.regs 4).toNat above rt ∧ P s

/-- How the callee returns (amd64). -/
@[reducible] def ICallRet64 (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Janus.Arm64.Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [] f x yh m zh kr ∧ MemFrame s.mem m (rt ++ calleeStack64 s stack nargs) ∧
    (∀ r ∈ keep s, ∀ a, r.1 ≤ a → a < r.1 + r.2 → m.readLE a 1 = s.mem.readLE a 1) ∧
    R (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (junk 0) (junk 3) (junk 1)

/-- The callee at the code address `fn` of `p` (amd64). -/
def ICallContract64 (p : Janus.Amd64.Program) (fn nargs stack above : Nat) (rt : List (Nat × Nat))
    (keep : State → List (Nat × Nat)) (R : Res) (P : State → Prop) : Prop :=
  Summary p fn (ICallPre64 nargs stack above rt P) (ICallRet64 nargs stack rt keep R)

end Janus.Contracts.ICall

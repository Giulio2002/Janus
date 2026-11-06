import Janus.Contracts.Alloc

/-!
# An abstract callee: a dynamic interface method call to arbitrary code (arm64)

`w.Write(p)` through an interface calls the code of whatever dynamic type `w` has. A theorem that
should hold for **every** writer cannot pin the target (`ItabIs`) and cannot extract it. It takes a
**hypothesis about the callee**, `ICallContract p fn stack above rt R P`, for an arbitrary code address
`fn` (the `Fun[0]` word of the itab, linked to the call by a hypothesis `s.mem.readLE (tab + 24) 8 = fn`),
and `janus_run calls [h]` uses it at an indirect call whose target is `fn`.

The callee is **arbitrary Go code**. The contract assumes only what the Go ABI and the call give:

* **pre** (`ICallPre`): `CallOK` (an admissible return address, an aligned `SP`, the stack window
  `[SP - stack, SP + 8 + 8·4)` writable), `above ≥ 32` with `[SP - 8, SP + above)` (the caller's frame:
  the saved frame pointer, the locals, the spill slots) **outside every range of `rt`** (`Outside`), and the
  call-site property `P`. `P` is a hypothesis the *caller* must prove at the call (`provePre`): it is
  the theorem's statement about what the call receives (for `WriteTo`: the arguments are the slice
  passed in).
* **post** (`ICallRet`): the call returns to `X30` with `SP`, `X18`, `X28` and `X29` preserved; every
  other register, the flags, the SIMD registers and the exclusive monitor arbitrary; memory changed at
  most in `rt` (the callee's own memory: it may be the whole heap) and in the callee's stack window
  (`calleeStack`), the bytes `[X1, X1 + X2)` of the slice argument unchanged (`io.Writer.Write` must not
  modify the slice data). The three result registers `X0..X2` satisfy the relation `R` of the
  arguments `X0..X3`, which the theorem chooses (every `R` is covered, so `R` can express nothing or
  anything a particular callee is trusted to do); nothing else is known about them.

Nothing says heap objects, including those reachable from the caller's values, are left alone: the
callee is not assumed to be well behaved beyond the ABI. The contract is satisfiable
(`Janus.Contracts.ICallSat`), and it is a hypothesis of the theorem that uses it, shown in the
printed statement.
-/

namespace Janus.Contracts.ICall

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts

/-- The relation of a callee's three result registers to its four argument registers. -/
abbrev Res := W64 → W64 → W64 → W64 → W64 → W64 → W64 → Prop

/-- The precondition of the call (`X0..X3` the receiver data word and the slice `(ptr, len, cap)`). -/
def ICallPre (stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop) (s : State) : Prop :=
  CallOK s stack 4 ∧ 32 ≤ above ∧ Outside (s.sp.toNat - 8) (above + 8) rt ∧ P s

/-- How the callee returns. -/
@[reducible] def ICallRet (stack : Nat) (rt : List (Nat × Nat)) (R : Res) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
    (ep : Nat → Bool),
    s' = retStateX s junk [] f v m ex ep ∧ MemFrame s.mem m (rt ++ calleeStack s stack 4) ∧
    (∀ x, (s.regs 1).toNat ≤ x → x < (s.regs 1).toNat + (s.regs 2).toNat → m.readLE x 1 = s.mem.readLE x 1) ∧
    R (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (junk 0) (junk 1) (junk 2)

/-- The callee at the code address `fn` of `p`, using at most `stack` bytes below `SP`, in a caller whose
frame extends `above` bytes above `SP`, with its own memory `rt`, results related by `R`, for calls that
satisfy `P`. -/
def ICallContract (p : Program) (fn stack above : Nat) (rt : List (Nat × Nat)) (R : Res)
    (P : State → Prop) : Prop :=
  Summary p fn (ICallPre stack above rt P) (ICallRet stack rt R)

end Janus.Contracts.ICall

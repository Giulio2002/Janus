import Janus.Contracts.Cmpstring
import Janus.Contracts.AllocAmd64

/-!
# The contract of `runtime.cmpstring` (amd64)

The amd64 version of `Janus.Contracts.Cmpstring` (whose module documentation explains it):
`runtime.cmpstring(a, b string) int` (`internal/bytealg/compare_amd64.s`) with `a = (RAX, RBX)`,
`b = (RCX, RDI)` and the result in `RAX`. The comparison `strCmp` and `StrOK` are shared with
arm64. The contract is satisfiable (`Janus.Contracts.CmpstringSatAmd64`).
-/

namespace Janus.Contracts.Cmpstring

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts

/-- The precondition of `runtime.cmpstring(a, b)` on amd64. -/
def CmpstringPre64 (stack : Nat) (s : State) : Prop :=
  CallOK64 s stack 4 ∧ StrOK s.mem (s.regs 0).toNat (s.regs 3).toNat ∧
    StrOK s.mem (s.regs 1).toNat (s.regs 7).toNat

/-- The comparison result of the call state `s` (amd64). -/
def cmpResult64 (s : State) : W64 :=
  BitVec.ofInt 64 (strCmp s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat)

/-- How `runtime.cmpstring` returns (amd64). -/
@[reducible] def CmpRet64 (stack : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Janus.Arm64.Memory),
    s' = retState64 s junk [cmpResult64 s] f x yh m ∧ MemFrame s.mem m (calleeStack64 s stack 4)

/-- `runtime.cmpstring` at `addr` of `p` (amd64), using at most `stack` bytes below `RSP`. -/
def CmpstringContract64 (p : Janus.Amd64.Program) (addr stack : Nat) : Prop :=
  Summary p addr (CmpstringPre64 stack) (CmpRet64 stack)

attribute [janus64_exec, janus64_post] cmpResult64

end Janus.Contracts.Cmpstring

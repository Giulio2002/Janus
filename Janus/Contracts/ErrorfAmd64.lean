import Janus.Contracts.Errorf
import Janus.Contracts.PoolAmd64

/-!
# Contract of `fmt.errorf` for one goroutine (amd64)

The amd64 counterpart of `Janus.Contracts.Errorf` (see that file and docs/RUNTIME-CONTRACTS.md,
"fmt.Errorf"): the same function, the same closed set of formats and the same result, stated with
the amd64 ABIInternal. `fmt.errorf(format string, a []any) error` takes the format in
`RAX`/`RBX` (`regs 0`, `regs 3`), the slice in `RCX`/`RDI`/`RSI` (`regs 1`, `regs 7`, `regs 6`)
and returns the error interface in `RAX`/`RBX` (`regs 0`, `regs 3`). `CALL` pushes the return
address; `RBP`, `R14` (`g`) and `X15` are preserved, every other general register, `X0`–`X14`, the
upper `YMM` halves and the flags are arbitrary afterwards. A call may write `rt` and its stack
window (`liveWin64`).
-/

namespace Janus.Contracts.ErrorfAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf
  Janus.Contracts Janus.Contracts.Pool Janus.Contracts.Errorf Janus.Contracts.PoolAmd64

/-- **`fmt.errorf(format, a)`** (amd64), as `Errorf.ErrorfLive`. -/
def ErrorfLive (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (tErr iErr tInt iWrap Fl Fm B : Nat) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK64 s stack 5 ∧ StackRoom64 s stack 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (s.regs 7).toNat (s.regs 6).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (liveWin64 s stack 5) ∧
      ReadsSafe R L (errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat, (s.regs 6).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (s.regs 14).toNat s.mem
        (liveWin64 s stack 5))
    (fun s s' => PoolAmd64.LiveRet R stack 5 L s s' fun r m =>
      ErrorfPost (Env.mk tErr iErr tInt iWrap) R s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (liveWin64 s stack 5) L b
        (s.regs 14).toNat (r 0).toNat (r 3).toNat m)

end Janus.Contracts.ErrorfAmd64

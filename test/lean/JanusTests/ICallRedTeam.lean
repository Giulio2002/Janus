import Janus

/-!
# Red team for the abstract-callee contract (`ICallContract`, `ICallContract64`)

Rows 1 and 2 of the U-ICALL attack list, as theorems: a return state that violates the contract is **not** an
`ICallRet`, so no callee that returns such a state can satisfy `ICallContract`, and a consumer cannot be fooled by a
callee that clobbers what the ABI says it keeps. (Rows 3 and 4, a call site whose arguments do not satisfy `P` and a
forged target address, are `examples/proofs/WriteToRedTeam.lean`: the tactic refuses.)

* **Row 1, callee clobbers `X28` / `X29` / `SP` (arm64), `R14` / `RBP` (amd64):** `*_clobber_rejected`.
* **Row 2, callee writes our frame (outside `rt` and the callee's stack window):** `*_frame_write_rejected`.

The controls are the satisfiability witnesses (`ICallSat`, `ICallSatAmd64`): the writer there returns a state that
does satisfy `ICallRet`.
-/

namespace JanusTests.ICallRedTeam

open Janus Janus.Contracts Janus.Contracts.ICall

section A64
open Janus.Arm64 Janus.Tactic

/-- Row 1 (arm64): a return state whose `X28` (the goroutine register `g`) differs is not an `ICallRet`. -/
theorem g_clobber_rejected (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (v : W64) (hv : v ≠ s.regs 28) :
    ¬ ICallRet nargs stack rt keep R s { s with regs := setReg s.regs 28 v } := by
  rintro ⟨junk, f, vr, m, ex, ep, hs, -⟩
  have := congrArg (fun t => t.regs 28) hs
  simp [retStateX, callRegs, setReg] at this
  exact hv this

/-- Row 1 (arm64): the frame pointer `X29`. -/
theorem fp_clobber_rejected (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (v : W64) (hv : v ≠ s.regs 29) :
    ¬ ICallRet nargs stack rt keep R s { s with regs := setReg s.regs 29 v } := by
  rintro ⟨junk, f, vr, m, ex, ep, hs, -⟩
  have := congrArg (fun t => t.regs 29) hs
  simp [retStateX, callRegs, setReg] at this
  exact hv this

/-- Row 1 (arm64): the stack pointer. -/
theorem sp_clobber_rejected (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (v : W64) (hv : v ≠ s.sp) :
    ¬ ICallRet nargs stack rt keep R s { s with sp := v } := by
  rintro ⟨junk, f, vr, m, ex, ep, hs, -⟩
  have := congrArg (fun t => t.sp) hs
  simp [retStateX] at this
  exact hv this

/-- Row 2 (arm64): a return state whose memory differs, at an address outside `rt` and the callee's stack window,
from the call state's is not an `ICallRet`. -/
theorem frame_write_rejected (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (m' : Memory) (a : Nat) (hout : Outside a 1 (rt ++ calleeStack s stack nargs))
    (hdiff : m'.readLE a 1 ≠ s.mem.readLE a 1) :
    ¬ ICallRet nargs stack rt keep R s { s with mem := m' } := by
  rintro ⟨junk, f, vr, m, ex, ep, hs, hf, -⟩
  have hm : m' = m := by simpa [retStateX] using congrArg (fun t => t.mem) hs
  subst hm
  exact hdiff (hf.readLE a 1 hout)

end A64

section X64
open Janus.Amd64 Janus.Amd64.Tactic

/-- Row 1 (amd64): `R14` (`g`) clobbered. -/
theorem g_clobber_rejected64 (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (v : W64) (hv : v ≠ s.regs 14) :
    ¬ ICallRet64 nargs stack rt keep R s { s with regs := setRegF s.regs 14 v } := by
  rintro ⟨junk, f, x, yh, m, zh, kr, hs, -⟩
  have := congrArg (fun t => t.regs 14) hs
  simp [retState64, callRegs64, setRegF] at this
  exact hv this

/-- Row 1 (amd64): `RBP` clobbered. -/
theorem bp_clobber_rejected64 (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (v : W64) (hv : v ≠ s.regs 5) :
    ¬ ICallRet64 nargs stack rt keep R s { s with regs := setRegF s.regs 5 v } := by
  rintro ⟨junk, f, x, yh, m, zh, kr, hs, -⟩
  have := congrArg (fun t => t.regs 5) hs
  simp [retState64, callRegs64, setRegF] at this
  exact hv this

/-- Row 2 (amd64). -/
theorem frame_write_rejected64 (nargs stack : Nat) (rt : List (Nat × Nat)) (keep : State → List (Nat × Nat)) (R : Res)
    (s : State) (m' : Janus.Arm64.Memory) (a : Nat) (hout : Outside a 1 (rt ++ calleeStack64 s stack nargs))
    (hdiff : m'.readLE a 1 ≠ s.mem.readLE a 1) :
    ¬ ICallRet64 nargs stack rt keep R s { s with mem := m' } := by
  rintro ⟨junk, f, x, yh, m, zh, kr, hs, hf, -⟩
  have hm : m' = m := by simpa [retState64] using congrArg (fun t => t.mem) hs
  subst hm
  exact hdiff (hf.readLE a 1 hout)

end X64

end JanusTests.ICallRedTeam

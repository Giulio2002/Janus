import Extracted
import Janus.Contracts.SoftFloat

/-!
# `runtime.KeepAlive(x any)` meets `KeepAliveContract` (arm64)

```go
func KeepAlive(x any) { if cgoAlwaysFalse { println(x) } }
```

The contract library says (`Janus/Contracts/SoftFloat.lean`) that `runtime.KeepAlive`, when it is
called as a function (the compiler turns a direct call into an intrinsic, so this happens through a
function value only), returns after changing only its frame, provided `runtime.cgoAlwaysFalse` is
`false`. This file proves that statement for the real function: the code of `runtime.KeepAlive`
extracted from the binary (`artifacts/examples-rtmisc-softf-arm64`; `printlock`, `printeface`,
`printnl` and `printunlock`, which only the dead `if cgoAlwaysFalse` branch calls, are left out with
`--contract 'runtime.print*'`), run from the entry.

**Guarantee.** For every call state that satisfies the contract's precondition (the runtime call
frame `RTPre softEnv 2`, and the byte at the address the code reads, `runtime.cgoAlwaysFalse`,
`false`), the function returns after finitely many steps, keeps `SP`, `X18`, `X28`, `X29`,
`FPCR`, `TPIDR_EL0` and `DCZID_EL0`, and writes only its stack window and the argument spill slots.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Instrument
  Janus.Contracts.SoftFloat

namespace Proof

/-- `runtime.cgoAlwaysFalse`: the address the `ADRP`+`LDRB` at `KeepAlive+0x20` reads. -/
def cgoAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "runtime.KeepAlive" 8)
    (segWord Extracted.program "runtime.KeepAlive" 9) 0

theorem correctness : KeepAliveContract Extracted.program Extracted.entry cgoAddr := by
  intro s hpc ⟨hpre, hcgo, hdis⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  obtain ⟨hc1, hc2, hc3⟩ := hcgo
  simp only [softEnv, softDepth, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hout hd1 hd2 hd3 hst
  janus_eval_nat hC : cgoAddr
  simp only [hC, Spec.Disjoint, softDepth] at hc1 hc2 hc3 hdis
  have hr : ∀ v1 v2 v3, (((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 v1).writeLE (BitVec.toNat s.sp - 40) 8 v2).writeLE
      (BitVec.toNat s.sp + 8) 8 v3).readLE 1432095 1 = 0 := by
    intro v1 v2 v3
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact hc3
  janus_run [hr]
  exact SoftRet.intro 2 s _ _ rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    rfl rfl rfl (by simp only [rtWrites, calleeStack, softEnv, softDepth]; janus_frame) trivial

/-! ## The precondition is satisfiable, and the guarantee is reached

A call with `SP = 0x20000` (`[SP - 512, SP + 0x100)` writable), a goroutine at `0x50000` whose
`stackguard0` is 0, return address `0x200000`, and `runtime.cgoAlwaysFalse` a readable zero byte. -/

namespace Witness

theorem cgoAddr_eq : cgoAddr = 1432095 := by decide

def wsp : Nat := 0x20000
def wg : Nat := 0x50000

def smem : Memory :=
  ⟨fun _ => 0, [⟨wsp - 512, 0x300, true⟩, ⟨wg, 0x100, false⟩, ⟨1432095, 8, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 0x200000 else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := smem }

theorem pre : RTPre softEnv 2 s0 ∧ Misc.CgoAlwaysFalse s0.mem cgoAddr ∧
    Spec.Disjoint cgoAddr 1 (s0.sp.toNat - softDepth) (softDepth + 8 + 8 * 2) := by
  rw [cgoAddr_eq]
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩, ?_⟩, ⟨by decide, by decide, by decide⟩, by unfold Spec.Disjoint; decide⟩
  simp [softEnv, outside_nil]

/-- The hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ s : State, s.pc = BitVec.ofNat 64 Extracted.entry ∧ RTPre softEnv 2 s ∧
    Misc.CgoAlwaysFalse s.mem cgoAddr ∧
    Spec.Disjoint cgoAddr 1 (s.sp.toNat - softDepth) (softDepth + 8 + 8 * 2) :=
  ⟨s0, rfl, pre⟩

/-- So the guarantee is reached: the call returns to `X30`, changing only its frame. -/
theorem returns : ReachesRet Extracted.program (s0.regs regLR) s0
    (fun s' => SoftRet 2 s0 s' fun _ => True) :=
  correctness s0 rfl pre

end Witness

end Proof

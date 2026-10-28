import Janus
import Extracted

/-!
# `runtime.KeepAlive(x any)` meets `KeepAliveContract64` (amd64)

```go
func KeepAlive(x any) { if cgoAlwaysFalse { println(x) } }
```

The amd64 version of `examples/rtmisc/proofs/arm64/KeepAlive.lean`: the code of `runtime.KeepAlive`
extracted from `artifacts/examples-rtmisc-softf-amd64` (`printlock`, `printeface`, `printnl` and
`printunlock`, called only on the dead `if cgoAlwaysFalse` branch, left out with
`--contract 'runtime.print*'`), run from the entry, meets the contract of
`Janus/Contracts/SoftFloatAmd64.lean`.

**Guarantee.** For every call state that satisfies the contract's precondition (the runtime call
frame `RTPre64 softEnv 2`, and the byte at the address the code reads, `runtime.cgoAlwaysFalse`,
`false`, outside the callee's stack window), the function returns after finitely many steps,
pops its return address, keeps `RBP`, `R14`, `X15` and the `MXCSR` controls, and writes only its
stack window and the argument spill slots.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.SoftFloat

namespace Proof

/-- `runtime.cgoAlwaysFalse`: the operand of the `CMPB disp32(%rip), $0` at `KeepAlive+0x18`
(`80 3D disp32 imm8`, 7 bytes). -/
def cgoAddr : Nat :=
  match Extracted.program.fetch (Extracted.entry + 0x18) with
  | some bs =>
    let disp := bs[2]! + 256 * bs[3]! + 65536 * bs[4]! + 16777216 * bs[5]!
    (Extracted.entry + 0x18 + 7 + disp + 2 ^ 64 - (if disp ≥ 2 ^ 31 then 2 ^ 32 else 0)) % 2 ^ 64
  | none => 0

theorem correctness : KeepAliveContract64 Extracted.program Extracted.entry cgoAddr := by
  intro s hpc ⟨hpre, hcgo, hdis⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  obtain ⟨hc1, hc2, hc3⟩ := hcgo
  simp only [softEnv, softDepth, regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra hout
  janus_eval_nat hC : cgoAddr
  simp only [hC, Spec.Disjoint, softDepth] at hc1 hc2 hc3 hdis
  janus64_run
  exact SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
    rfl rfl hdf.symm rfl (by simp only [rtWrites64, MapAmd64.calleeStack, softEnv, softDepth]; janus_frame) trivial

/-! ## The precondition is satisfiable, and the guarantee is reached

A call with `RSP = 0x20000` (`[RSP - 512, RSP + 0x100)` writable, return address `0` at `[RSP]`), a
goroutine at `0x50000` whose `stackguard0` is 0, and `runtime.cgoAlwaysFalse` a readable zero byte. -/

namespace Witness

theorem cgoAddr_eq : cgoAddr = 5526629 := by decide

def wsp : Nat := 0x20000
def wg : Nat := 0x50000

def smem : Janus.Arm64.Memory :=
  ⟨fun _ => 0, [⟨wsp - 512, 0x300, true⟩, ⟨wg, 0x100, false⟩, ⟨5526629, 8, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem pre : RTPre64 softEnv 2 s0 ∧ Misc.CgoAlwaysFalse s0.mem cgoAddr ∧
    Spec.Disjoint cgoAddr 1 ((s0.regs 4).toNat - softDepth) (softDepth + 8 + 8 * 2) := by
  rw [cgoAddr_eq]
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, rfl, rfl,
    by decide, ?_⟩, ⟨by decide, by decide, by decide⟩, by unfold Spec.Disjoint; decide⟩
  simp [softEnv, outside_nil]

/-- The hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ s : State, s.rip = BitVec.ofNat 64 Extracted.entry ∧ RTPre64 softEnv 2 s ∧
    Misc.CgoAlwaysFalse s.mem cgoAddr ∧
    Spec.Disjoint cgoAddr 1 ((s.regs 4).toNat - softDepth) (softDepth + 8 + 8 * 2) :=
  ⟨s0, rfl, pre⟩

/-- So the guarantee is reached: the call returns to the return address, changing only its frame. -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => SoftRet64 2 s0 s' fun _ => True) :=
  correctness s0 rfl pre

end Witness

end Proof

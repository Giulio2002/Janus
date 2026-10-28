import Extracted

/-!
# `SVEField() uint64`: the SVE field of `ID_AA64PFR0_EL1`, whatever the CPU reports (arm64)

```go
func SVEField() uint64 { return PFR0() >> 32 & 0xf }   // PFR0: MRS ID_AA64PFR0_EL1, R0
```

This is how `golang.org/x/sys/cpu` (and `klauspost/cpuid`) reads the CPU's features at EL0: Linux
traps `MRS Xt, ID_AA64*_EL1` and emulates it with a sanitised value (`HWCAP_CPUID`, kernel 4.11 or
later). The model does not know the CPU. The read is a `.syscall` stub whose contract
(`Janus.Kernel.Site.mrs (.idreg crm op2)`) lets it return **any** 64-bit value `v`, recorded in
the trace as the event `.env "ID_AA64PFR0_EL1" v`; the theorem holds for every `v`, so it assumes
no CPU feature.

**Guarantee.** For every kernel state `k` in which Linux emulates the ID registers
(`IdRegsEmulated k`, i.e. `k.idregOK`, a stated hypothesis: otherwise the instruction is `SIGILL`) and every call state
whose stack-growth check falls through and whose 40 bytes below SP are writable, the call returns, and
there is a value `v < 2^64` such that the trace gains exactly the event
`.env "ID_AA64PFR0_EL1" v`, nothing else of the kernel state changes, and the result is the SVE
field of `v`: `v / 2 ^ 32 % 16`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Kernel

namespace Proof

theorem correctness (E : KEnv) :
    EnsuresK Extracted.program E Extracted.entry []
      (fun s k => GuardOK s 0 ∧ StackOK s 40 0 ∧ IdRegsEmulated k)
      (fun _ k s' k' => ∃ v, v < 2 ^ 64 ∧ k' = k.emit (.env "ID_AA64PFR0_EL1" v) ∧
        s'.regs 0 = BitVec.ofNat 64 (v / 2 ^ 32 % 16)) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hid⟩
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run
  refine ⟨.mrs (.idreg 4 0) 0, by rw [siteOf_withExit]; decide, Or.inl ⟨hid, ?_⟩⟩
  rintro s' k' ⟨v, hv, rfl, rfl⟩
  apply ReturnsK.of_reaches
  janus_run
  refine ⟨v, hv, rfl, ?_⟩
  rw [BitVec.and_assoc, show (18446744069414584335#64 &&& 15#64) = 15#64 by decide,
    show (15#64) = BitVec.ofNat 64 (2 ^ 4 - 1) by rfl, SoftFloat.ubfx_eq _ 32 4 (by omega) (by omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-! ## The hypotheses are satisfiable, and the guarantee is reached

A concrete call: return address `0x1000`, `SP = 0x20000` with `[SP - 64, SP)` writable, a goroutine
at `0x50000` whose `stackguard0` is 0, and a kernel that emulates the ID registers. The register
is then read as any value: `correctness` holds for all of them, `returns` is the reachability of
the guarantee in this state. -/

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20000
def wg : Nat := 0x50000

def smem : Memory := ⟨fun _ => 0, [⟨wsp - 64, 64, true⟩, ⟨wg, 0x100, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := smem }

def k0 : Kern := {}
def E0 : KEnv := ⟨[], 1024⟩

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩

theorem pre : GuardOK s0 0 ∧ StackOK s0 40 0 ∧ IdRegsEmulated k0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, rfl⟩

/-- All the hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (k : Kern), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (GuardOK s 0 ∧ StackOK s 40 0 ∧ IdRegsEmulated k) :=
  ⟨ret, s0, k0, hret, setup, pre⟩

/-- So the guarantee is reached in that state, for whatever value the kernel reports. -/
theorem returns : ReturnsK ((Extracted.program).withExit ret) E0
    (fun s' k' => FFI.ABIReturnC s0 s' ∧ ∃ v, v < 2 ^ 64 ∧ k' = k0.emit (.env "ID_AA64PFR0_EL1" v) ∧
      s'.regs 0 = BitVec.ofNat 64 (v / 2 ^ 32 % 16)) (fun _ _ => False) s0 k0 :=
  correctness E0 ret hret s0 k0 setup pre

end Witness

end Proof

import Janus
import Extracted

/-!
# `Pop(x uint64) int` branches on the CPU feature flag `runtime.x86HasPOPCNT` (amd64, v1)

```go
func Pop(x uint64) int { return bits.OnesCount64(x) }
```

With `GOAMD64=v1` the compiler cannot assume `POPCNT`, so it emits a test of the runtime's
feature flag: `MOVZX runtime.x86HasPOPCNT, CX; TESTL CX, CX; JE …` and then either one
`POPCNTQ AX, CX` or a call of the portable `math/bits.OnesCount64` (a SWAR reduction).

**Guarantee, for both values of the flag.** For every `x`, **every `b : Bool`** and every Go
call state in which the stack-growth prologue falls through, 24 bytes of stack below `RSP` (and
the return-address slot) are writable, and the flag byte holds `b` (`Misc.CpuFlag`, apart from
that stack), the call returns, obeys the ABI, and returns the number of set bits of `x`
(`Amd64.popNat 64`, the count `POPCNT` produces). With `b = true` that is the `POPCNT` path; with
`b = false` the portable code, whose result is the same by `PopCount.swarM_eq_popNat`.

**The flag is a stated hypothesis, not a choice.** `runtime.x86HasPOPCNT` is set once by the
runtime from `CPUID` before any user code runs (`internal/cpu`); it is writable data the extractor
does not copy, so the theorem takes its value as the parameter `b`. The model executes `POPCNT`
whatever the CPU, so the `b = true` case means what it says exactly when the runtime set the flag
only on a CPU that has the instruction (docs/SOUNDNESS.md, "CPU feature flags").
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.Misc

/-- `runtime.x86HasPOPCNT`: the byte the `MOVZX` at `Pop+0xe` reads. -/
def hasPOPCNT : Nat := ripTarget Extracted.program (Extracted.entry + 0xe)

theorem correctness (x : BitVec 64) (b : Bool) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 24 8 ∧ CpuFlag s.mem hasPOPCNT b ∧
        Spec.Disjoint hasPOPCNT 1 ((s.regs regSP).toNat - 24) 32)
      (fun _ s' => (s'.regs 0).toNat = popNat 64 x.toNat) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hf, hfd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus_eval_nat hH : hasPOPCNT
  obtain ⟨hf1, hf2, hf3⟩ := hf
  simp only [Spec.Disjoint, regSP] at hfd
  rw [hH] at hf1 hf2 hf3 hfd
  janus64_run
  · -- no POPCNT: the portable math/bits.OnesCount64
    rw [← Janus.Spec.PopCount.swarM_eq_popNat x.toNat x.isLt]
    simp only [Janus.Spec.PopCount.swarM, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod,
      Nat.and_comm, Nat.add_comm, Janus.Spec.PopCount.mod64_mod128]
  · -- POPCNT
    exact Nat.mod_eq_of_lt (by have := Janus.Spec.PopCount.popNat_le 64 x.toNat; omega)

end Proof

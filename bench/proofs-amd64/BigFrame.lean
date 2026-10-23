import Janus
import Extracted

/-!
# Benchmark `BigFrame(x, k uint64) uint64` on amd64: a 520-byte stack frame

The amd64 version of `bench/proofs-arm64/BigFrame.lean`: the `LEAQ -0x188(SP), R12` form of the
stack-guard prologue (`StackGuardOK s 392`), a zeroing loop of 8 × 4 `MOVUPS X15` stores
(16 bytes each), the fill loop of 64 stores, and a load at a symbolic index, split into 64 cases
after the run.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

set_option maxRecDepth 4000000 in
set_option janus.aliasInfo false in
set_option maxHeartbeats 40000000 in
theorem correctness (x k : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, k] 1
      (fun s => StackGuardOK s 392 ∧ StackWritable s 520 8 ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 520 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16))
      (fun r => r = [x + BitVec.ofNat 64 (k.toNat % 64)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, hd⟩
  janus64_intro hs
  simp only [regSP, regG, stackguard0Offset, stackguard0] at *
  janus64_run
  generalize hj : k.toNat % 64 = j at *
  have hlt : j < 64 := hj ▸ Nat.mod_lt _ (by decide)
  janus64_cases hlt
  all_goals janus64_simp
  all_goals (simp only [List.cons.injEq, and_true]; bv_omega)

end Proof

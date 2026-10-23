import Janus
import Extracted

/-!
# Benchmark `Nested(n, m)` on amd64: a doubly nested loop

The amd64 version of `bench/proofs-arm64/Nested.lean`: nested induction over the outer and
inner loop heads (`CMPQ AX, CX` at entry+9, `CMPQ BX, SI` at entry+0x22).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

abbrev outerHead : Nat := Extracted.entry + 0x9
abbrev innerHead : Nat := Extracted.entry + 0x22

/-- `Σ_{j<k} (i·m + j)` -/
def innerSum (i m : W64) : Nat → W64
  | 0 => 0
  | k + 1 => innerSum i m k + (i * m + BitVec.ofNat 64 k)

/-- `Σ_{i<k} Σ_{j<m} (i·m + j)` -/
def outerSum (m : W64) : Nat → W64
  | 0 => 0
  | k + 1 => outerSum m k + innerSum (BitVec.ofNat 64 k) m m.toNat

theorem loops (n m : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State) :
    ∀ r i (S : State), i + r = n.toNat →
      S.rip = BitVec.ofNat 64 outerHead → S.regs 0 = n → S.regs 3 = m →
      S.regs 1 = BitVec.ofNat 64 i → S.regs 2 = outerSum m i →
      S.regs 4 = s.regs 4 → S.regs 5 = s.regs 5 → S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 →
      S.mem = s.mem → s.mem.readLE (s.regs 4).toNat 8 = ret →
      s.mem.accessible (s.regs 4).toNat 8 false = true →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = outerSum m n.toNat) := by
  intro r
  induction r with
  | zero =>
    intro i S hi hpc h0 h3 h1 h2 h4 h5 h14 h15 hm hr ha
    have hi' : i < 2 ^ 64 := by omega
    janus64_run
    subst hi; rfl
  | succ r ih =>
    intro i S hi hpc h0 h3 h1 h2 h4 h5 h14 h15 hm hr ha
    have hi' : i + 1 < 2 ^ 64 := by omega
    janus64_run until [outerHead, innerHead]
    suffices hin : ∀ q k (T : State), k + q = m.toNat →
        T.rip = BitVec.ofNat 64 innerHead → T.regs 0 = n → T.regs 3 = m →
        T.regs 1 = BitVec.ofNat 64 i → T.regs 6 = BitVec.ofNat 64 k →
        T.regs 2 = outerSum m i + innerSum (BitVec.ofNat 64 i) m k →
        T.regs 4 = s.regs 4 → T.regs 5 = s.regs 5 → T.regs 14 = s.regs 14 →
        T.xmm 15 = s.xmm 15 → T.mem = s.mem →
        Reaches (Extracted.program.withExit ret) T (IsReturn fun s' => ABIReturn s s' ∧
          s'.regs 0 = outerSum m n.toNat) by
      apply hin m.toNat 0 _ (by omega)
      all_goals janus64_simp [innerSum]
    intro q
    induction q with
    | zero =>
      intro k T hk tpc t0 t3 t1 t6 t2 t4 t5 t14 t15 tm
      janus64_run until [outerHead, innerHead]
      apply ih (i + 1) _ (by omega)
      all_goals janus64_simp [outerSum]
      all_goals first | rfl | assumption | rw [BitVec.ofNat_add] | rw [show k = m.toNat by omega]
    | succ q ihq =>
      intro k T hk tpc t0 t3 t1 t6 t2 t4 t5 t14 t15 tm
      have hk' : k + 1 < 2 ^ 64 := by omega
      janus64_run until [outerHead, innerHead]
      apply ihq (k + 1) _ (by omega)
      all_goals janus64_simp [innerSum]
      all_goals first | ac_rfl | rw [BitVec.ofNat_add]

theorem correctness (n m : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [n, m] 1 (fun s => StackWritable s 0 8)
      (fun r => r = [outerSum m n.toNat]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run until [outerHead]
  refine Reaches.mono (loops n m ret hret s n.toNat 0 _ (by omega) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp [outerSum])
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    h_ret (Janus.Arm64.Memory.accessible_sub _ hacc (by decide) (by omega) (by omega))) ?_
  intro o ho
  cases o with
  | stub _ _ _ => exact ho.elim
  | returned t' =>
    simp only [isReturn_returned] at ho ⊢
    exact ⟨ho.1, by simp [results, intArgRegs, ho.2]⟩

end Proof

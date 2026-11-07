import Janus
import Extracted

/-! `example.com/basic.CountThenWrite(s Sink, p []byte) (int, error)` on amd64: `n := s.Count(); if n == 0 { return 0, nil };
return s.Write(p)`, two interface calls through the itab (`MOVQ 24(AX), CX; CALL CX` and `MOVQ 32(DX), DX; CALL DX`) to arbitrary
callees. As the arm64 proof (`examples/proofs/CountThenWrite.lean`): two `ICallContract64` hypotheses for two code addresses
`fn₁`, `fn₂` (statement variables, linked to the itab words), `calls [hc1, hc2]`, and a continuation that holds for every
result the first callee returns. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall

theorem correctness (impl : List Janus.Amd64.Segment) (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res)
    (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) →
    ICallContract64 (Extracted.program.link impl) fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn1 ∧ CodePtrOK64 fn2 ∧
        (tab.toNat + 24 + 16 ≤ (s.regs 4).toNat - (48 + stack) ∨ (s.regs 4).toNat + 48 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 48 ∧ SPAligned s ∧
        tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
        Outside (tab.toNat + 24) 16 rt ∧ Outside ((s.regs 4).toNat - 48) 96 rt)
      (fun _ s' => ∃ c a1 a2 a3 e1 e2, R1 w a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R2 w ptr len cap n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 3 = f1 ∧ s'.regs 1 = f2))) := by
  intro hc1 hc2 ret hret s hs ⟨h8, hf1, hf2, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF1, hF2, hot, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [CodePtrOK64] at hf1 hf2
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF1 hF2 hrt hot
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 96 rt := hrt.of_sub (by omega) (by omega)
  janus64_run [hF1, hF2] calls [hc1, hc2]
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inl (by janus_assumption)⟩
  · exact ⟨_, _, _, _, _, _, by janus_assumption, Or.inr ⟨by janus_assumption, _, _, _, by janus_assumption, rfl, rfl, rfl⟩⟩

end Proof

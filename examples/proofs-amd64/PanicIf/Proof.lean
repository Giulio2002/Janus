import Janus
import Extracted

/-! `example.com/basic.PanicIf(x, e any)` on amd64: returns `x+1` for `x ≤ 10`, panics with
exactly `e` (reaches `runtime.gopanic`) for `x > 10`. Example 1 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.PanicAmd64

theorem correctness (P : PanicRuntime) (x etyp edata : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [x, etyp, edata]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 40)
      (fun _ => goClass P)
      (fun _ s' => x.toNat ≤ 10 → s'.regs 0 = x + 1)
      (fun _ v _ => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩) := by
  intro ret hret s hs ⟨hg, hle, hnw, hacc⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · janus64_run
    exact fun _ => trivial
  · have hx' : 10 < x.toNat := by omega
    janus64_run
    refine ⟨⟨etyp.toNat, edata.toNat⟩, ?_, ?_⟩
    · show (⟨etyp.toNat, edata.toNat⟩ : Eface) = ⟨_, _⟩
      simp [setRegF]
    · first | (intro _; rfl) | rfl | trivial

end Proof

import Janus
import Extracted

/-! `example.com/basic.WriteTo(w io.Writer, b []byte) (int, error)` on amd64: `w.Write(b)` through the itab
(`MOVQ 24(AX), DX; CALL DX`), with `w = (tab, data)` in `RAX`, `RBX` and `b = (ptr, len, cap)` in `RCX`, `RDI`, `RSI`.

The same guarantee as the arm64 proof (`examples/proofs/WriteTo.lean`): for **every** code address `fn`, memory `rt` and
relation `R`, if the code at `fn` satisfies `ICallContract64` (the Go ABI only: `RSP` popped, `RBP` and `R14` preserved,
memory changed only in `rt` and the callee's stack, results related by `R` to the arguments),
then `WriteTo` returns, the call is entered with the receiver and slice it received, its results are the callee's
(`R w ptr len cap n e₁ e₂` and `(RAX, RBX, RCX) = (n, e₁, e₂)`). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall

theorem correctness (impl : List Janus.Amd64.Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 32 ∧ SPAligned s ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧ Outside ((s.regs 4).toNat - 48) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 3 = e1 ∧ s'.regs 1 = e2) := by
  intro hc ret hret s hs ⟨h8, hfn, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned, CodePtrOK64] at hfn
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF hrt
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 56 rt := hrt.of_sub (by omega) (by omega)
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  janus64_run [hF] calls [hc]
  case hq =>
    rename_i _ _ hR
    exact ⟨_, _, _, hR, rfl, rfl, rfl⟩

end Proof

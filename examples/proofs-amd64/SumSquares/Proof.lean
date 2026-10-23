import Janus
import Extracted

/-! `example.com/basic.SumSquares` on amd64: `square(x) + square(y)`, through the stack-check
prologue and two calls of the helper `square` (`IMULQ AX, AX; RET`).

`square` is proved once, from any state at its entry, as a callee `Summary`: it returns to the
address on top of the stack with `RAX := RAX · RAX`, `RSP := RSP + 8`, the flags changed and
nothing else. `janus64_run calls [square_summary]` uses it at both call sites instead of
executing the callee. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `square` as a callee: from any state at its entry whose return-address slot `[RSP]` is
readable and holds an address below `2^47`, it returns there with `RAX = RAX · RAX`. -/
theorem square_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.square")
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 * s.regs 0)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32)
      (fun r => r = [x * x + y * y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgb hnw2 hgr
  janus64_run calls [square_summary]
  rw [BitVec.add_comm]

end Proof

import Janus
import Extracted

/-! `example.com/basic.AddThree` on amd64: `Add(Add(x, y), z)`, through the stack-check
prologue and two calls.

The callee `Add` (`ADDQ BX, AX; RET`, extracted with `AddThree`) is proved once, from any state
at its entry, as a `Summary`; `janus64_run calls [add_summary]` uses it at both call sites. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `Add` as a callee: from any state at its entry whose return-address slot `[RSP]` is readable
and holds an address below `2^47`, it returns there with `RAX = RAX + RBX`. -/
theorem add_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.Add")
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 + s.regs 3)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩

theorem correctness (x y z : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, z] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 32 32)
      (fun r => r = [x + y + z]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run calls [add_summary]

end Proof

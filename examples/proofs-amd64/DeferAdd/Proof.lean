import Janus
import Extracted

/-! `example.com/basic.DeferAdd(x, y)` on amd64: `r = x` and an open-coded `defer` of a closure
that adds `y` to `r`; the call returns `x + y`.

For every call state whose stack-growth check falls through, with `[RSP-64, RSP+8)` writable, the
call returns `[x + y]`. The deferred closure's funcval is built in the frame and called at the
exit (`CALL AX`, context in `DX`), so its target is read back from the stack. The
`CALL runtime.deferreturn` block (reached only after a recovered panic) is not extracted, and the
theorem shows it is not reached. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackGuardOK s 0 ∧ StackWritable s 64 8)
      (fun r => r = [x + y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hg, hle, hnw, hacc⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  first | with_reducible congr 1 | congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

end Proof

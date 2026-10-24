import Janus
import Extracted

/-! `example.com/basic.Compose(a, b, x uint64) uint64` on amd64: a non-escaping closure.

For every call state whose stack-growth checks fall through (`StackGuardOK s 56`; the deeper
check is in the callee `twice`) with `[RSP-80, RSP+8)` writable and the guard word outside it,
the call returns `f(f(x)) = a·(a·x + b) + b mod 2^64` for the closure `f(v) = a·v + b`.

The closure captures `a` and `b` and does not escape, so `Compose` builds its funcval (the code
address of `Compose.func1`, then `a`, `b`) in its own frame, without allocating. `twice` calls it
twice (`CALL CX` with the funcval in `DX`), and `Compose.func1` reads the captured variables
through `DX`. Everything the indirect calls depend on is written by the code being proved, so
no hypothesis about the closure is needed. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, x]
      (fun s => StackGuardOK s 56 ∧ StackWritable s 80 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80))
      (fun _ s' => (s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  simp only [BitVec.toNat_mul, BitVec.toNat_add]
  janus64_arith

end Proof

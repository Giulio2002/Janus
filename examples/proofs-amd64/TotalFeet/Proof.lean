import Janus
import Extracted

/-! `example.com/basic.TotalFeet(a, b Feet) uint64` on amd64: a generic function, through its
dictionary.

For every call state whose memory holds the function's read-only data (`DataLoaded`: the
dictionary `..dict.total[Feet]`), whose stack-growth checks fall through (`StackGuardOK s 40`;
the deeper check is in the shape function) with `[RSP-72, RSP+8)` writable and the guard word
outside it, the call returns `30·(a + b) mod 2^64`: the length `a + b` feet in centimetres.

`Meters` and `Feet` have the same GC shape (`uint64`), so `total[Meters]` and `total[Feet]` share
the single body `total[go.shape.uint64]` (`TotalMeters` and `TotalFeet` call the same address);
each caller passes its own dictionary in `RAX`. The shape code loads the dictionary's first word
(the code address of `Feet.Scale`) and calls it (`CALL CX`, the dictionary in `DX`), twice. The
executor reads that word from the extracted dictionary, so the call target is a literal.
(`Feet.Scale` is extracted with `--targets`, `scripts/example-targets.sh`.) -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => Extracted.program.DataLoaded s.mem ∧ StackGuardOK s 40 ∧ StackWritable s 72 8 ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 72))
      (fun _ s' => (s'.regs 0).toNat = 30 * (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_data hd [hacc]
  set_option maxRecDepth 4000 in janus64_run
  simp only [BitVec.toNat_mul]
  janus64_arith

end Proof

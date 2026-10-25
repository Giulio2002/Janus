import Janus
import Extracted

/-! `example.com/basic.DotBoth(a, b, c, d uint64) uint64` on amd64: a method value and a method
expression on a value receiver.

For every call state whose memory holds the function's read-only data (`DataLoaded`; the static
funcval of `Vec2.Dot`), whose stack-growth checks fall through (`StackGuardOK s 120`; the
deepest check is in the wrapper `Vec2.Dot-fm`) with `[RSP-168, RSP+40)` writable (the frames
and the caller's spill area for the four arguments) and the guard word outside it, the call
returns `(a, b)·(c, d) + (a, b)·(d, c) mod 2^64`.

The method value `v.Dot` is a closure over a copy of `v` built in `DotBoth`'s frame (the address
of `Vec2.Dot-fm`, then `a`, `b`), called by `applyVec` through `CALL SI` with the funcval in `DX`;
the wrapper reads the receiver through `DX` and calls `Vec2.Dot` directly. The method
expression `Vec2.Dot` is the static funcval `Vec2.Dot·f` in `.rodata`, whose code word is
`Vec2.Dot`; `applyVec2` calls it through `CALL R8`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => Extracted.program.DataLoaded s.mem ∧ StackGuardOK s 120 ∧ StackWritable s 168 40 ∧
        ((s.regs 4).toNat + 40 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 168))
      (fun _ s' => (s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, hg, ⟨hle, hnw, hacc⟩, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_data hd [hacc]
  set_option maxRecDepth 4000 in janus64_run
  simp only [BitVec.toNat_mul, BitVec.toNat_add]
  janus64_arith

end Proof

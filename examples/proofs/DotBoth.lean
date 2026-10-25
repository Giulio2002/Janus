import Extracted

/-!
# `DotBoth(a, b, c, d uint64) uint64`: a method value and a method expression (value receiver)

**Guarantee.** For all 64-bit `a`, `b`, `c`, `d` and every Go call state `s` of
`example.com/basic.DotBoth` whose memory holds the function's read-only data (`DataLoaded`; the
static funcval of `Vec2.Dot`), whose stack-growth prologues fall through (`GuardOK s 128`, the
guard word outside the stack window) and whose `SP` is aligned with `[SP-192, SP+40)` writable
(the frames of `DotBoth`, `applyVec`, `applyVec2` and the wrapper `Vec2.Dot-fm`, and the
caller's spill area for the four arguments), the call returns (never faulting or panicking),
obeys the ABI, and `X0 = (a, b)·(c, d) + (a, b)·(d, c) = a·c + b·d + a·d + b·c mod 2^64`.

**What is exercised.** `Vec2.Dot` has a value receiver (passed in registers, `X0`, `X1`).
* The method value `v.Dot` is a closure over a copy of `v`: `DotBoth` builds it in its frame (the
  address of the wrapper `Vec2.Dot-fm`, then `a`, `b`); `applyVec` calls it through `blr`, and
  the wrapper reads the receiver through `X26` and calls `Vec2.Dot` directly.
* The method expression `Vec2.Dot` is a function of `(v, w)`: a static funcval in `.rodata`
  (`Vec2.Dot·f`) whose code word is `Vec2.Dot` itself; `applyVec2` calls it through `blr`.

Both calls are resolved by the executor from memory: the first from stores of the code being
proved, the second from the extracted read-only data.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => Extracted.program.DataLoaded s.mem ∧ GuardOK s 128 ∧ StackOK s 192 40 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 192) 232)
      (fun _ s' => (s'.regs 0).toNat =
        (a.toNat * c.toNat + b.toNat * d.toNat + (a.toNat * d.toNat + b.toNat * c.toNat)) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_data hd [hw]
  janus_run
  janus_arith

end Proof

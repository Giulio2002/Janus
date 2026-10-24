import Extracted

/-!
# Benchmark `Mul256(z, x, y *[4]uint64)` on arm64: `z = x·y mod 2^256`

A 256-bit multiplication as an EVM-style integer library implements it (`uint256.Int.Mul`):
the schoolbook product of 4×4 limbs, keeping the 10 partial products that reach the low 256
bits (6 `MUL`/`UMULH` pairs, 4 `MADD`s, carry chains through `ADDS`/`ADC`). The value stored
at `z` is `(X·Y) mod 2^256` for the values `X`, `Y` at `x`, `y` **before** the call, and
nothing outside `z[0..32)` changes. No aliasing assumption at all: the code loads every limb
before it stores, so `z` may equal or overlap `x` or `y` (`z.Mul(z, z)`).

The carry arithmetic after the run is closed by `janus_arith`'s reflective carry procedure
(`Janus.Tactic.Carry`): no product needs to be named, and no bound to be stated.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false)
      (fun s s' =>
        val256 s'.mem z.toNat = val256 s.mem x.toNat * val256 s.mem y.toNat % 2 ^ 256 ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
  janus_intro hs
  janus_run
  janus_arith

end Proof

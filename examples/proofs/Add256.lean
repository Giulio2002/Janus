import Extracted

/-!
# `Add256(z, x, y *[4]uint64)` stores `x + y` modulo `2^256` into `z`, with aliasing

**Guarantee.** For all pointers `z`, `x`, `y` and every Go call state of
`example.com/basic.Add256` with the pointers in `X0`–`X2` such that
* the 32 bytes at `z` are writable and those at `x` and `y` readable (each inside one memory
  region of the caller, not wrapping around `2^64`), and
* every pair of the three pointers is either **equal** or **disjoint** (so `z.Add256(z, z)`,
  `z = x`, `z = y`, `x = y` are all covered; only partial overlap is excluded),

the compiled code returns, obeys the ABI, the 256-bit little-endian value at `z` afterwards is
`(X + Y) mod 2^256`, where `X` and `Y` are the values at `x` and `y` **before** the call, and no
byte outside `z[0..32)` changes (nor the region list).

**What it rules out.** Wrong limbs or carries, reading an input limb after it was overwritten
through an alias, out-of-bounds accesses, writes outside `z`, faults and panics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' =>
        val256 s'.mem z.toNat = (val256 s.mem x.toNat + val256 s.mem y.toNat) % 2 ^ 256 ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  -- one symbolic run per aliasing pattern
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; janus_arith)

end Proof

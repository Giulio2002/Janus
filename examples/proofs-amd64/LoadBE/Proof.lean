import Janus
import Extracted

/-! `example.com/basic/v3.LoadBE(b *[8]byte) uint64` (`binary.BigEndian.Uint64(b[:])`) on amd64
built with `GOAMD64=v3`: one `MOVBE (AX), AX; RET`. For every readable 8-byte buffer at `b`, the
result is the big-endian value of its bytes, `b[0] * 256^7 + ... + b[7]`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- The big-endian value of the `k` bytes of `m` at `a`. -/
def beValue (m : Janus.Arm64.Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (m.bytes a).toNat * 256 ^ k + beValue m (a + 1) k

theorem rev_step (k b r : Nat) (hb : b < 256) :
    Janus.Arm64.revBytesNat (k + 1) (b + 256 * r) = b * 256 ^ k + Janus.Arm64.revBytesNat k r := by
  simp only [Janus.Arm64.revBytesNat]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt hb, Nat.zero_add]

theorem rev_readLE (m : Janus.Arm64.Memory) (k : Nat) :
    ∀ a, Janus.Arm64.revBytesNat k (m.readLE a k) = beValue m a k := by
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    simp only [Janus.Arm64.Memory.readLE, beValue]
    rw [rev_step _ _ _ (m.bytes a).isLt, ih]

theorem correctness (b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [b]
      (fun s => StackWritable s 0 8 ∧ Buffer s b 8 false)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (beValue s.mem b.toNat 8)]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hbw, hb⟩⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  rw [rev_readLE]

end Proof

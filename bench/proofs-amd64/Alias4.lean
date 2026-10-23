import Janus
import Extracted

/-!
# Benchmark `Alias4(a, b, c, d *uint64)` on amd64: four pointers that may alias

The amd64 version of `bench/proofs-arm64/Alias4.lean` (read-modify-write `ADDQ`/`XORQ` with
memory operands). The four words must also not overlap the return-address slot `[RSP]`.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

def rd (m : Memory) (p : W64) : W64 := BitVec.ofNat 64 (m.readLE p.toNat 8)
def wr (m : Memory) (p v : W64) : Memory := m.writeLE p.toNat 8 v.toNat

/-- The Go semantics of `Alias4` on memory. -/
def alias4 (m : Memory) (a b c d : W64) : Memory :=
  let m := wr m a (rd m a + rd m b)
  let m := wr m c (rd m c ^^^ rd m d)
  let m := wr m b (rd m b + rd m c)
  wr m d (rd m a + 1)

def Alias8 (p q : W64) : Prop := p = q ∨ Disjoint p 8 q 8

theorem Alias8.nat {p q : W64} (h : Alias8 p q) :
    p.toNat = q.toNat ∨ p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat :=
  h.imp (congrArg BitVec.toNat) id

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => StackWritable s 0 8 ∧ Buffer s a 8 true ∧ Buffer s b 8 true ∧ Buffer s c 8 true ∧
        Buffer s d 8 true ∧ Alias8 a b ∧ Alias8 a c ∧ Alias8 a d ∧ Alias8 b c ∧ Alias8 b d ∧
        Alias8 c d ∧ Disjoint a 8 (s.regs regSP) 8 ∧ Disjoint b 8 (s.regs regSP) 8 ∧
        Disjoint c 8 (s.regs regSP) 8 ∧ Disjoint d 8 (s.regs regSP) 8)
      (fun s s' =>
        s'.mem.readLE a.toNat 8 = (alias4 s.mem a b c d).readLE a.toNat 8 ∧
        s'.mem.readLE b.toNat 8 = (alias4 s.mem a b c d).readLE b.toNat 8 ∧
        s'.mem.readLE c.toNat 8 = (alias4 s.mem a b c d).readLE c.toNat 8 ∧
        s'.mem.readLE d.toNat 8 = (alias4 s.mem a b c d).readLE d.toNat 8) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨ha', ha⟩, ⟨hb', hb⟩, ⟨hc', hc⟩, ⟨hd', hd⟩, hab, hac, had,
    hbc, hbd, hcd, sa, sb, sc, sd⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw sa sb sc sd
  simp only [alias4, rd, wr]
  rcases hab.nat with hab | hab <;> rcases hac.nat with hac | hac <;>
    rcases had.nat with had | had <;> rcases hbc.nat with hbc | hbc <;>
    rcases hbd.nat with hbd | hbd <;> rcases hcd.nat with hcd | hcd
  all_goals first | (exfalso; omega) |
    (janus64_run; all_goals (simp only [Nat.add_comm, Nat.xor_comm, and_self, BitVec.xor_self, BitVec.toNat_zero,
      Nat.add_zero, Nat.zero_add, Nat.xor_self, true_and, and_true]; janus64_arith))

end Proof

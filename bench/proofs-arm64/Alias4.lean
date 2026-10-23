import Extracted

/-!
# Benchmark `Alias4(a, b, c, d *uint64)` on arm64: four pointers that may alias

```go
*a += *b; *c ^= *d; *b += *c; *d = *a + 1
```

**Guarantee.** For all pointers `a`, `b`, `c`, `d` to writable words, any two of which are
either equal or disjoint, the call returns and the four words afterwards are those of the Go
semantics `alias4` (sequential updates of the memory before the call).

**Stress.** Six pairwise "equal or disjoint" facts give 64 combinations; the 49 inconsistent
ones are refuted by `omega`, and each of the 15 consistent aliasing patterns is executed
separately (12 loads/stores whose read-over-write resolution depends on the pattern).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The word at `p`, and a store of a word. -/
def rd (m : Memory) (p : W64) : W64 := BitVec.ofNat 64 (m.readLE p.toNat 8)
def wr (m : Memory) (p v : W64) : Memory := m.writeLE p.toNat 8 v.toNat

/-- The Go semantics of `Alias4` on memory. -/
def alias4 (m : Memory) (a b c d : W64) : Memory :=
  let m := wr m a (rd m a + rd m b)
  let m := wr m c (rd m c ^^^ rd m d)
  let m := wr m b (rd m b + rd m c)
  wr m d (rd m a + 1)

/-- Two word pointers are equal or do not overlap. -/
def Alias8 (p q : W64) : Prop := p = q ∨ Disjoint p.toNat 8 q.toNat 8

theorem Alias8.nat {p q : W64} (h : Alias8 p q) :
    p.toNat = q.toNat ∨ p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat :=
  h.imp (congrArg BitVec.toNat) id

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, c, d]
      (fun s => Ptr s.mem a 8 true ∧ Ptr s.mem b 8 true ∧ Ptr s.mem c 8 true ∧
        Ptr s.mem d 8 true ∧ Alias8 a b ∧ Alias8 a c ∧ Alias8 a d ∧ Alias8 b c ∧ Alias8 b d ∧
        Alias8 c d)
      (fun s s' =>
        s'.mem.readLE a.toNat 8 = (alias4 s.mem a b c d).readLE a.toNat 8 ∧
        s'.mem.readLE b.toNat 8 = (alias4 s.mem a b c d).readLE b.toNat 8 ∧
        s'.mem.readLE c.toNat 8 = (alias4 s.mem a b c d).readLE c.toNat 8 ∧
        s'.mem.readLE d.toNat 8 = (alias4 s.mem a b c d).readLE d.toNat 8) := by
  intro ret hret s hs ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩, ⟨hd, hd'⟩, hab, hac, had, hbc, hbd, hcd⟩
  janus_intro hs
  simp only [alias4, rd, wr]
  -- one symbolic run per aliasing pattern
  -- one symbolic run per aliasing pattern (as `Nat` facts, for omega)
  rcases hab.nat with hab | hab <;> rcases hac.nat with hac | hac <;>
    rcases had.nat with had | had <;> rcases hbc.nat with hbc | hbc <;>
    rcases hbd.nat with hbd | hbd <;> rcases hcd.nat with hcd | hcd
  all_goals first | (exfalso; omega) |
    (janus_run; all_goals (simp only [Nat.add_comm, Nat.xor_comm, and_self]; janus_arith))

end Proof

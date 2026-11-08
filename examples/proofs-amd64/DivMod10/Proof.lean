import Janus
import Extracted

/-! `example.com/basic.DivMod10(x) (q, r)` on amd64: named results, division by a constant.

For every 64-bit `x`, the results are the quotient and remainder of `x` by 10 (`QuotRem10`):
`q = RAX = ⌊x / 10⌋`, `r = RBX = x mod 10`. The compiled code has no division: it multiplies by
the magic constant `⌈2^67 / 10⌉ = 0xcccccccccccccccd` (`MULQ`, high half in `RDX`), shifts right
by 3 and computes the remainder as `x - 10·q` (two `LEAQ`, `SUBQ`). The theorem shows that this is
the division for all `2^64` inputs. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `q` and `r` are the quotient and remainder of `x` by 10. -/
def QuotRem10 (x q r : BitVec 64) : Prop := q.toNat = x.toNat / 10 ∧ r.toNat = x.toNat % 10

/-- The remainder step `x - (2q + 4·2q)`, which does not wrap when `q = ⌊x / 10⌋`. -/
theorem rem_lemma (x q : BitVec 64) (h : q.toNat = x.toNat / 10) :
    (x - (q + q + (q + q) <<< 2)).toNat = x.toNat % 10 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h]
  omega

theorem correctness (x : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ q m, r = [q, m] ∧ QuotRem10 x q m) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  generalize hq : BitVec.ofNat 64 (14757395258967641293 * x.toNat / 18446744073709551616) >>> 3 = q
  have hq' : q.toNat = x.toNat / 10 := by
    have := x.isLt
    have hlt : 14757395258967641293 * x.toNat / 18446744073709551616 < 2 ^ 64 := by omega
    rw [← hq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.shiftRight_eq_div_pow]
    omega
  exact ⟨hq', rem_lemma x q hq'⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 47#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ q m, (results 2 s') = [q, m] ∧ QuotRem10 x q m) :=
  ⟨ret, s0, x, hret, setup, hpre, correctness x ret hret s0 setup hpre⟩

end Witness

end Proof

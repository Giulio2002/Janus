import Janus.Contracts.LiveStubSlice

/-!
# A variable-size live `memmove` stub (arm64): `memmove(dst = X0, src = X1, n = X2)` for every `1 ≤ n ≤ N` (U-MEMMOVE-UPTO)

`SetFromDecimal` copies chunks of every size `1 … min 19 n`, so its runtime assumption is `R.ok memmove [q, p, sl]` for each of
them. The fixed-size stubs (`memmoveSeg addr n`) serve one size. `memmoveUptoSeg addr N` serves all of `1 … N`: a compare
chain (`CMP X2, #k ; B.EQ Lk` for `k = 1 … N`) dispatches to the straight-line copy of exactly `k` bytes
(`memmoveCodeN k`, load every chunk, then store every chunk, so overlapping ranges are fine) and returns. The proof
splits on `k` and runs the same argument as `janus_live_memmove k`, so a request outside `1 … N` is not served: the tactic
`janus_live_memmove_upto N hok` needs `hok : ∀ args, ok a args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ N`.
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts

/-- `CMP X2, #k` (`SUBS XZR, X2, #k`). -/
def cmpX2 (k : Nat) : Nat := 0xf100005f + k * 1024

/-- `B.EQ` by `off` instructions (forward). -/
def beqFwd (off : Nat) : Nat := 0x54000000 + off * 32

/-- Where the copy of exactly `k` bytes (`1 ≤ k ≤ N`) starts, in instructions from the segment base. -/
def blockStart (N k : Nat) : Nat := 2 * N + 1 + ((List.range (k - 1)).map fun j => (memmoveCodeN (j + 1)).length).sum

/-- The dispatch chain, an unreachable `RET` (for `n` outside `1 … N`), and the copies. -/
def memmoveUptoCode (N : Nat) : List Nat :=
  (List.range N).flatMap (fun j => [cmpX2 (j + 1), beqFwd (blockStart N (j + 1) - (2 * j + 1))]) ++ [0xd65f03c0] ++
  ((List.range N).map fun j => memmoveCodeN (j + 1)).flatten

def memmoveUptoSeg (addr N : Nat) : Segment := ⟨"live-stub.memmove", addr, memmoveUptoCode N⟩

end Janus.Contracts.LiveStub

/-- Split `k ∈ [lo, hi]` into its values by bisection (no `interval_cases`: Mathlib is not a dependency) and run `t` for each
literal value of `k`. -/
syntax "janus_split_k " num num "(" tactic ")" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_split_k $lo:num $hi:num ($t)) => do
    let l := lo.getNat
    let h := hi.getNat
    if l ≥ h then
      `(tactic| (obtain rfl : k = $lo := (by omega); $t))
    else
      let mid := Lean.Syntax.mkNumLit (toString ((l + h) / 2))
      let m1 := Lean.Syntax.mkNumLit (toString ((l + h) / 2 + 1))
      `(tactic| (by_cases hkm : k ≤ $mid
                 · janus_split_k $lo $mid ($t)
                 · janus_split_k $m1 $hi ($t)))

/-- `MemmoveLive linked a 4096 (toyR [] ok)` for the stub `LiveStub.memmoveUptoSeg a N`, when `hok` pins every request the
runtime serves at `a` to `[q, p, k]` with `1 ≤ k ≤ N`: `∀ args, ok a args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ N`. -/
syntax "janus_live_memmove_upto " num term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_memmove_upto $N:num $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
      obtain ⟨q0, p0, k, hargs, hk1, hk2⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 2).toNat = k := hargs.2.2
      have hr2 : s.regs 2 = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by rw [hn]; simp; omega)
      rw [hn] at hs2 hd2 hd4
      change Janus.Tactic.ReachesRet _ _ s _
      janus_split_k 1 $N (
        (janus_run [hr2]; (try rw [hn]);
         open Janus.Contracts.LiveStub in
           refine liveMemRet_writes (copyWrites s.mem (s.regs 0).toNat (s.regs 1).toNat _)
             (copyWrites_sub _ _ _ _) rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hd4 hLm.2.1 ?_;
         all_goals first
           | exact Janus.Contracts.LiveStub.copied_copyWrites _ _ _ _ _
           | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))))

/-- `MemmoveZeroLive linked a d R` (`memmove(dst, src, 0)`) for a `memmove` stub that returns without a memory access when
`X2 = 0`: `LiveStub.memmoveUptoSeg a N` (its compare chain falls through to the `RET`), or the pinned runtime's code
(`LiveSat.memmoveZeroLive_pinned`). For any `d` and `R`. -/
syntax "janus_live_memmove_zero" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_memmove_zero) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨h0, ⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm⟩ := pre
      have hr2 : s.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run [hr2]
      exact Janus.Contracts.liveMemRet_none rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hLm.2.1))

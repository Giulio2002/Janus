import Extracted

/-!
# `List(n int) *Node`: n heap allocations in a loop, for all n (arm64)

```go
type Node struct{ Next *Node; V uint64 }
func List(n int) *Node {
	var head *Node
	for i := 0; i < n; i++ { head = &Node{Next: head, V: uint64(i)} }
	return head
}
```

`runtime.newobject` and `runtime.gcWriteBarrier1` are the **live** contracts of
`Janus/Contracts/Live.lean`, with one runtime hypothesis `R` threaded through every iteration:
the number of allocations is data-dependent, the loop invariant carries the live set `L` and the
budget `b - 16·i`, and each iteration re-establishes it from the postconditions of the previous
iteration's two calls (the barrier flag unknown after each: both branches are executed).

**Guarantee.** For every `n < 2^40`, every runtime satisfying the live contracts with a budget of
`16·n` bytes at the entry, and every call state whose frame is outside the runtime-owned ranges:
the call returns; for `n = 0` the result is `nil`; otherwise it is a 16-byte node inside `R.rt`
whose `V` field is `n - 1`; memory changes only in `R.rt` and the stack window; and the invariant
holds again for some live set that contains the head.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The loop head `CMP R1, R0` (after `MOVD 72(RSP), R0`). -/
abbrev head : Nat := Extracted.entry + 0x40

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem loop (impl : List Segment) (R : RtInv) (b : Nat) (n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hd : Extracted.program.DataLoaded s.mem)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4160 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb' : 4168 ≤ s.sp.toNat) (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 4168) (4168 + 16) true = true)
    (hout : Outside (s.sp.toNat - 4168) 4184 R.rt)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4168) 4184)
    (hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hflag : s.mem.accessible 0x15dc20 4 false = true) (hty : Outside 0x9b3c0 16 R.rt)
    (hn2 : n.toNat < 2 ^ 40)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [0x9b3c0])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1]) :
    ∀ m (S : State) (i : Nat), i + m = n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = n → S.regs 1 = BitVec.ofNat 64 i →
      S.sp = s.sp - 64#64 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.sp - 72#64 → S.regs 18 = s.regs 18 →
      S.mem.readLE (s.sp.toNat - 64) 8 = ret → S.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat →
      S.mem.readLE (s.sp.toNat + 8) 8 = n.toNat →
      MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 16)]) →
      16 * n.toNat ≤ b →
      (∃ L, R.inv (b - 16 * i) L (s.regs 28).toNat (view R.rt L S.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4168, s.sp.toNat + 16)]) ∧
        (0 < i → InRanges (S.regs 2).toNat 16 L ∧ S.mem.readLE ((S.regs 2).toNat + 8) 8 = i - 1)) →
      (i = 0 → S.regs 2 = 0#64) → (0 < i → InRanges (S.regs 2).toNat 16 R.rt) →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ((n.toNat = 0 → (s'.regs 0).toNat = 0) ∧
         (0 < n.toNat → InRanges (s'.regs 0).toNat 16 R.rt ∧ s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = n.toNat - 1) ∧
         ∃ b' L', b - 16 * n.toNat ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
           (0 < n.toNat → InRanges (s'.regs 0).toNat 16 L') ∧
           MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 16)]))) := by
  intro m
  induction m with
  | zero =>
    intro S i hi hpc h0 h1 hsp h28 h29 h18 h_rd64 h_rd72 h_rdn hf hbud hinv hz hpos
    obtain ⟨L, hinv, hLs, hpos'⟩ := hinv
    janus_data hd [hw]
    janus_run
    have hi' : i = n.toNat := by omega
    subst hi'
    refine ⟨fun h => ?_, fun h => ?_, b - 16 * n.toNat, L, by omega, hinv, fun h => (hpos' h).1, hf⟩
    · rw [hz (by omega)]; rfl
    · exact ⟨hpos h, (hpos' h).2⟩
  | succ m ih =>
    intro S i hi hpc h0 h1 hsp h28 h29 h18 h_rd64 h_rd72 h_rdn hf hbud hinv hz hpos
    obtain ⟨L, hinv, hLs, hpos'⟩ := hinv
    janus_data hd [hw]
    janus_run until [head] calls [hnew.pos, hwb]
    all_goals refine ih _ (i + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | assumption
      | exact fun h => h.elim
      | (intro _; assumption)
      | janus_frame
      | (janus_clear_irrel; omega; done)
      | (simp only [BitVec.ofNat_add]; rfl)
      | (refine ⟨L ++ [(_, _ + 16)], ?_, ?_, ?_⟩
         · janus_live
         · intro r hr
           rcases List.mem_append.1 hr with h | h
           · exact hLs r h
           · simp only [List.mem_singleton] at h
             subst h
             simp only [Outside, outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left]
             first | omega | janus_apart
         · intro _
           exact ⟨InRanges.append_right _ (InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _)), by janus_simp⟩)
      | (janus_simp; done)

end Proof

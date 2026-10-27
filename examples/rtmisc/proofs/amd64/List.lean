import Janus
import Extracted

/-!
# `List(n int) *Node`: n heap allocations in a loop, for all n (amd64)

```go
type Node struct{ Next *Node; V uint64 }
func List(n int) *Node {
	var head *Node
	for i := 0; i < n; i++ { head = &Node{Next: head, V: uint64(i)} }
	return head
}
```

`runtime.newobject` and `runtime.gcWriteBarrier1` are the **live** contracts of
`Janus/Contracts/LiveAmd64.lean`, with one runtime hypothesis `R` threaded through every iteration
(see the arm64 proof): the loop invariant carries the live set `L` and the budget `b - 16·i`, and
each iteration re-establishes it from the postconditions of the previous iteration's two calls (the
barrier flag unknown after each: both branches are executed).

**Guarantee.** For every `n < 2^40`, every runtime satisfying the live contracts with a budget of
`16·n` bytes at the entry, and every call state whose frame is outside the runtime-owned ranges:
the call returns; for `n = 0` the result is `nil`; otherwise it is a 16-byte node inside `R.rt`
whose `V` field is `n - 1`; memory changes only in `R.rt` and the stack window; and the invariant
holds again for some live set that contains the head.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor `List` passes to `newobject` (the RIP-relative `LEAQ` at `List+0x3f`) and the
address of the write-barrier flag (the `CMPL` at `List+0x4b`), recomputed from the extracted code. -/
def nodeType : Nat := ripTarget Extracted.program (Extracted.entry + 0x3f)
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x4b)

/-- The loop head `CMPQ CX, AX`. -/
abbrev head : Nat := Extracted.entry + 0x30

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem loop (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hd : Extracted.program.DataLoaded s.mem)
    (hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hb' : 4136 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 16) true = true)
    (hout : Outside ((s.regs 4).toNat - 4136) 4152 R.rt)
    (hga : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4136) 4152)
    (hgr : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hflag : s.mem.accessible flagAddr 4 false = true) (hty : Outside nodeType 16 R.rt)
    (hn2 : n.toNat < 2 ^ 40)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1]) :
    ∀ m (S : State) (i : Nat), i + m = n.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = n → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 4 = s.regs 4 - 40#64 → S.regs 14 = s.regs 14 →
      S.regs 5 = s.regs 4 - 8#64 → S.xmm 15 = s.xmm 15 →
      S.mem.readLE (s.regs 4).toNat 8 = ret → S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      S.mem.readLE ((s.regs 4).toNat + 8) 8 = n.toNat →
      MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)]) →
      16 * n.toNat ≤ b →
      (∃ L, R.inv (b - 16 * i) L (s.regs 14).toNat (view R.rt L S.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)]) ∧
        (0 < i → InRanges (S.regs 2).toNat 16 L ∧ S.mem.readLE ((S.regs 2).toNat + 8) 8 = i - 1)) →
      (i = 0 → S.regs 2 = 0#64) → (0 < i → InRanges (S.regs 2).toNat 16 R.rt) →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ((n.toNat = 0 → (s'.regs 0).toNat = 0) ∧
         (0 < n.toNat → InRanges (s'.regs 0).toNat 16 R.rt ∧ s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = n.toNat - 1) ∧
         ∃ b' L', b - 16 * n.toNat ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
           (0 < n.toNat → InRanges (s'.regs 0).toNat 16 L') ∧
           MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)]))) := by
  intro m
  induction m with
  | zero =>
    intro S i hi hpc h0 h1 hsp h14 h5 hx h_rd64 h_rd72 h_rdn hf hbud hinv hz hpos
    obtain ⟨L, hinv, hLs, hpos'⟩ := hinv
    janus64_data hd [hw]
    janus_eval_nat h_t : nodeType
    janus_eval_nat h_f : flagAddr
    rw [h_t] at hty hok1
    rw [h_f] at hflag
    janus64_run
    have hi' : i = n.toNat := by omega
    subst hi'
    refine ⟨fun h => ?_, fun h => ?_, b - 16 * n.toNat, L, by omega, hinv, fun h => (hpos' h).1, hf⟩
    · rw [hz (by omega)]; rfl
    · exact ⟨hpos h, (hpos' h).2⟩
  | succ m ih =>
    intro S i hi hpc h0 h1 hsp h14 h5 hx h_rd64 h_rd72 h_rdn hf hbud hinv hz hpos
    obtain ⟨L, hinv, hLs, hpos'⟩ := hinv
    have key : ∀ k : Nat, BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := fun k => (BitVec.ofNat_add k 1).symm
    janus64_data hd [hw]
    janus_eval_nat h_t : nodeType
    janus_eval_nat h_f : flagAddr
    rw [h_t] at hty hok1
    rw [h_f] at hflag
    janus64_run until [head] calls [hnew.pos, hwb]
    all_goals janus_split_and
    all_goals refine ih _ (i + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | janus_frame
      | (janus_clear_irrel; omega; done)
      | skip
    all_goals (try janus_simp)
    all_goals first
      | exact key i
      | (intro _; with_reducible assumption)
      | exact ⟨L ++ [(_, _ + 16)], by janus_live,
          fun r hr => by
            rcases List.mem_append.1 hr with h | h
            · have h' := hLs r h
              simpa only [Outside, outside_cons, outside_nil, and_true] using h'
            · simp only [List.mem_singleton] at h
              subst h
              simp only [Nat.add_sub_cancel_left]
              first | omega | janus_apart,
          fun _ => InRanges.append_right _ (InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _))⟩



set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n : BitVec 64)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => StackGuardOK s 4136 ∧ StackWritable s 4136 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4152 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4136) 4152 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧ n.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧ 16 * n.toNat ≤ b)
      (fun s s' => (n.toNat = 0 → (s'.regs 0).toNat = 0) ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat 16 R.rt ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = n.toNat - 1) ∧
        ∃ b' L', b - 16 * n.toNat ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          (0 < n.toNat → InRanges (s'.regs 0).toNat 16 L') ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)])) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty, hn2, hok1, hok2, hinv, hbud⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  janus64_data hd [hw]
  janus_eval_nat h_t : nodeType
  janus_eval_nat h_f : flagAddr
  janus64_run until [head]
  have hls : ∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)] :=
    fun r hr => absurd hr (by simp)
  exact loop impl R b n ret hret s hnew hwb hd hg1 hg2 hg3 hal hb' ha hw hout hga hgr hflag
    hty hn2 hok1 hok2 n.toNat _ 0 (by omega)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_frame) hbud
    ⟨[], by janus_live, hls, fun h => absurd h (by omega)⟩ (fun _ => by janus_simp) (fun h => absurd h (by omega))

end Proof

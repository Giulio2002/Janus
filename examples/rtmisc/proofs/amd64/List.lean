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
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4144 < (s.regs 4).toNat)
    (hal : (s.regs 4).toNat % 8 = 0) (hb' : 4144 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4144) (4144 + 16) true = true)
    (hout : Outside ((s.regs 4).toNat - 4144) 4160 R.rt)
    (hga : Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4160)
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
      MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 16)]) →
      16 * n.toNat ≤ b →
      (∃ L, R.inv (b - 16 * i) L (s.regs 14).toNat (view R.rt L S.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 16)]) ∧
        (0 < i → InRanges (S.regs 2).toNat 16 L ∧ S.mem.readLE ((S.regs 2).toNat + 8) 8 = i - 1)) →
      (i = 0 → S.regs 2 = 0#64) → (0 < i → InRanges (S.regs 2).toNat 16 R.rt) →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ((n.toNat = 0 → (s'.regs 0).toNat = 0) ∧
         (0 < n.toNat → InRanges (s'.regs 0).toNat 16 R.rt ∧ s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = n.toNat - 1) ∧
         ∃ b' L', b - 16 * n.toNat ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
           (0 < n.toNat → InRanges (s'.regs 0).toNat 16 L') ∧
           MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 16)]))) := by
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
    all_goals (try janus64_simp)
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
      (fun s => StackGuardOK s 4144 ∧ StackWritable s 4144 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4144) 4160 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4160 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧ n.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧ 16 * n.toNat ≤ b)
      (fun s s' => (n.toNat = 0 → (s'.regs 0).toNat = 0) ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat 16 R.rt ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = n.toNat - 1) ∧
        ∃ b' L', b - 16 * n.toNat ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          (0 < n.toNat → InRanges (s'.regs 0).toNat 16 L') ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 16)])) := by
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
  have hls : ∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 16)] :=
    fun r hr => absurd hr (by simp)
  exact loop impl R b n ret hret s hnew hwb hd hg1 hg2 hg3 hal hb' ha hw hout hga hgr hflag
    hty hn2 hok1 hok2 n.toNat _ 0 (by omega)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus_frame) hbud
    ⟨[], by janus_live, hls, fun h => absurd h (by omega)⟩ (fun _ => by janus64_simp) (fun h => absurd h (by omega))

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64
open Janus.Contracts.LiveSat (bump_acc)

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")

def implAt : List Amd64.Segment :=
  [{ name := "witness.newobject", base := newA, bytes := newobjectCodeD },
   { name := "witness.gcWriteBarrier1", base := wbA, bytes := wbCode }]

/-- The requests the witness runtime serves: `List(3)`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [nodeType]) ∨ (a = wbA ∧ args = [1])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = wbA := by decide

set_option maxRecDepth 20000 in
theorem model_new : NewobjectLiveContract64 linked newA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hWs := pre.2.2.2.2.2.2
  have hret : Outside (s.regs 4).toNat 8 (toyRt []) := by
    have h := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
    simp only [Nat.add_sub_cancel_left] at h
    exact h
  have hap : Apart 4194304 8 (s.regs 4).toNat 8 := ((inRanges_bump []).apart hret).symm
  change ReachesRet linked _ s _
  janus64_run
  exact finish_newobjectD (tys := []) (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
    (by simp [setRegF, BUMP]) (by simp [BUMP]) pre

set_option maxRecDepth 20000 in
theorem model_wb : WbLiveContract64 linked wbA 4096 R 1 := by
  intro L b s hpc pre
  have ⟨hra, hal, h3, h4, h5⟩ := pre.1
  change ReachesRet linked _ s _
  janus64_run
  exact wb_post64 (tys := []) (ok := ok) (by intro t ht; simp at ht) (by omega) pre.2.2.1 pre.2.2.2.2
    (by simp [retAddrOf])
    (by intro i; simp only [setRegF]; by_cases h4 : i = 4 <;> by_cases h11 : i = 11 <;> simp [h4, h11])
    (by simp) rfl rfl (by simp) rfl rfl rfl

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The bump cell holds `HEAP`; the return address `ret = 0x1000` is at `[RSP]`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4144, 4160, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then 3 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : StackGuardOK s0 4144 ∧ StackWritable s0 4144 16 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4144) 4160 R.rt ∧
    Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4144) 4160 ∧ Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
    s0.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧ (3 : BitVec 64).toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧ 16 * (3 : BitVec 64).toNat ≤ 0x400 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, by decide, ?_, ?_, inv0, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, rfl⟩
  · rw [addr_wb]; exact Or.inr ⟨rfl, rfl⟩

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`List(3)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : Amd64.State),
    NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3] s ∧
    (StackGuardOK s 4144 ∧ StackWritable s 4144 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
      Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4144) 4160 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4160 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      s.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧ (3 : BitVec 64).toNat < 2 ^ 40 ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
      R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
      R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧ 16 * (3 : BitVec 64).toNat ≤ b) :=
  ⟨implAt, R, 0x400, ret, s0, by rw [addr_new]; exact model_new, by rw [addr_wb]; exact model_wb, hret, setup, pre⟩

/-- So the guarantee is reached: `List(3)` returns a non-nil node of value `2` inside `R.rt`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat ≠ 0 ∧ InRanges (s'.regs 0).toNat 16 R.rt ∧
      s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = 2 :=
  (correctness implAt R 0x400 3 (by rw [addr_new]; exact model_new) (by rw [addr_wb]; exact model_wb)
    ret hret s0 setup pre).mono
    fun _ ⟨habi, _, hv, hrest⟩ => by
      obtain ⟨hr, hv2⟩ := hv (by decide)
      refine ⟨habi, ?_, hr, hv2⟩
      intro h0
      obtain ⟨⟨lo, hi⟩, hm, h1, h2⟩ := hr
      rw [h0] at h1 h2
      simp only [rt_eq, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm <;>
        (simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; simp only [HEAP, HEND, BUMP, WBUF] at h1 h2; omega)

end Witness

end Proof

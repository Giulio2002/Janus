import Extracted

/-!
# `StackGrow(n int) int` with a `sync.Pool`-backed stack of words (arm64)

```go
var stackPool sync.Pool // New is nil

type stack struct{ w []uint64 }

func StackGrow(n int) int {
	s, _ := stackPool.Get().(*stack)
	if s == nil {
		s = new(stack)
	}
	defer stackPool.Put(s)
	s.w = slices.Grow(s.w[:0], n)
	return cap(s.w)
}
```

This is `math/big`'s pattern (`getStack`, a deferred `stk.free`, and the growth of the stack's
words): a `Get` with a type assertion, `new` on a miss, `slices.Grow` into the pooled object
(`runtime.growslice`, `runtime.memclrNoHeapPointers` and, storing the new array into the pooled
header, the GC write barrier `runtime.gcWriteBarrier2`), and a deferred `Put` (an open-coded
defer: a closure on the frame, called at the exit).

**Guarantee.** For every live runtime `R` (`Janus.Contracts.Live`),
every implementation of `sync.(*Pool).Get`, `sync.(*Pool).Put` (`PoolGetLive`, `PoolPutLive`,
`Janus/Contracts/Pool.lean`; pooled objects of shape `SliceObj B`: a slice header and its array,
with arbitrary contents and capacity at most `B`), `runtime.newobject`, `runtime.growslice`,
`runtime.memclrNoHeapPointers` and `runtime.gcWriteBarrier2` satisfying the live contracts for
`R`, every live set `L` and budget `bud` at which the invariant holds, and every Go call state with
`n < 2^40` in which the stack window `[SP-4288, SP+24)` is writable and apart from `R.rt` and the
live objects, the call returns, and

* the result is the capacity of the pooled stack after the growth: `cap` if `n ≤ cap`, else
  `growCap8 n cap` (Go's growth rule), for the capacity `cap ≤ B` the object had;
* memory changed only in `R.rt` and the stack window, **no object of `L` changed**;
* the runtime's invariant holds again for the live set `L` extended by the old backing array
  (`ex`, the one range the pooled stack's growth leaves: the collector, not the program, frees it)
  and a budget `b' ≤ bud`: the pooled header and the new array went back to the pool.

**Assumptions (all in the statement).** The contracts (docs/RUNTIME-CONTRACTS.md, "sync.Pool"),
for one goroutine (docs/SOUNDNESS.md, "The single-threaded assumption"); the budget covers the
allocations (`24` bytes for a new header, `8 · growCap8 n c` for the array, for every capacity `c ≤ B`
below `n` the pool may hold); the runtime serves the requests the function makes (`R.ok`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool
  Janus.Contracts Janus.Contracts.Pool

namespace Proof

/-- The address of `stackPool` (`ADRP`+`ADD` at `StackGrow+0x2c`). -/
def poolAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program "example.com/basic.StackGrow" 11)
    (segWord Extracted.program "example.com/basic.StackGrow" 12) 0

/-- The type word of `*stack` (`ADRP`+`ADD` at `StackGrow+0x38`), which the type assertion compares
with. -/
def ptrType : Nat :=
  adrpLdTarget (Extracted.entry + 0x38) (segWord Extracted.program "example.com/basic.StackGrow" 14)
    (segWord Extracted.program "example.com/basic.StackGrow" 15) 0

/-- The type descriptor of `stack` (`ADRP`+`ADD` at `StackGrow+0x50`), `newobject`'s argument. -/
def stkType : Nat :=
  adrpLdTarget (Extracted.entry + 0x50) (segWord Extracted.program "example.com/basic.StackGrow" 20)
    (segWord Extracted.program "example.com/basic.StackGrow" 21) 0

/-- The type descriptor of `uint64` (`ADRP`+`ADD` at `StackGrow+0xdc`), `growslice`'s element type. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0xdc) (segWord Extracted.program "example.com/basic.StackGrow" 55)
    (segWord Extracted.program "example.com/basic.StackGrow" 56) 0

/-- The address of `runtime.writeBarrier` (its `enabled` flag, read as a 32-bit word by the `ADRP` +
`LDR W` at `StackGrow+0x12c`). -/
def wbFlag : Nat :=
  adrpLdTarget (Extracted.entry + 0x12c) (segWord Extracted.program "example.com/basic.StackGrow" 75)
    (segWord Extracted.program "example.com/basic.StackGrow" 76) 2

/-- The address of the closure's code, `StackGrow.deferwrap1` (`ADRP`+`ADD` at `StackGrow+0x68`). -/
def wrapAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x68) (segWord Extracted.program "example.com/basic.StackGrow" 26)
    (segWord Extracted.program "example.com/basic.StackGrow" 27) 0

/-- The frame bookkeeping tactic: a goal `Outside a n X → Outside a n Y ∧ …` about lists of the form
`rt ++ [ranges]` is arithmetic over the atom `Outside a n rt`. -/
macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack] at h ⊢; grind))

/-- A range inside the window is outside the runtime. -/
theorem outside_rt_of_win {rt : List (Nat × Nat)} {lo hi a n : Nat} (h : LiveSep [(lo, hi)] rt)
    (h1 : lo ≤ a) (h2 : a + n ≤ hi) : Outside a n rt :=
  Outside.of_sub (h _ (List.mem_singleton_self _)) h1 (by simp only; omega)

/-- The slots of `StackGrow`'s frame (entry `SP` is `sp0`, its own `SP` `sp0 - 144`) that it keeps
across its calls: the closure `{StackGrow.deferwrap1, &stackPool, *stack, s}` at `sp0 - 48` and the
pointer to it at `sp0 - 16` (the open-coded defer), the argument `n` it spilled at `sp0 + 8`, the
saved `LR` at `sp0 - 144` and the frame pointer at `sp0 - 152`. -/
def Slots (sp0 fn pool T d n ret fp : Nat) (m : Memory) : Prop :=
  m.readLE (sp0 - 48) 8 = fn ∧ m.readLE (sp0 - 40) 8 = pool ∧ m.readLE (sp0 - 32) 8 = T ∧
    m.readLE (sp0 - 24) 8 = d ∧ m.readLE (sp0 - 16) 8 = sp0 - 48 ∧ m.readLE (sp0 + 8) 8 = n ∧
    m.readLE (sp0 - 144) 8 = ret % 2 ^ 64 ∧ m.readLE (sp0 - 152) 8 = fp

/-- A call (at most five arguments) from `StackGrow`'s frame, or from the deferred wrapper's frame
below it, keeps those slots: they lie in the function's window, apart from the runtime, and outside the
callee's. (`spc` is the caller's `SP`: `sp0 - 144`, or `sp0 - 192` in the wrapper.) -/
theorem Slots.step {rt : List (Nat × Nat)} {sp0 spc k fn pool T d n ret fp : Nat} {m m' : Memory}
    (hwrt : LiveSep [(sp0 - 4288, sp0 + 24)] rt) (hsp : 4288 ≤ sp0) (hk : k ≤ 5)
    (hc : spc = sp0 - 144 ∨ spc + 8 + 8 * k + 8 ≤ sp0 - 152) (hcl : sp0 - 4288 ≤ spc - 4096)
    (h : Slots sp0 fn pool T d n ret fp m)
    (hfr : MemFrame m m' (rt ++ [(spc - 4096, spc - 8), (spc + 8, spc + 8 + 8 * k)])) :
    Slots sp0 fn pool T d n ret fp m' := by
  have hrd : ∀ x, sp0 - 4288 ≤ x → x + 8 ≤ sp0 + 24 → spc - 8 ≤ x →
      (x + 8 ≤ spc + 8 ∨ spc + 8 + 8 * k ≤ x) → m'.readLE x 8 = m.readLE x 8 := fun x hx1 hx2 hx3 hx4 => by
    refine hfr.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨Outside.of_sub (hwrt _ (List.mem_singleton_self _)) hx1 (by simp only; omega), ?_, ?_⟩ <;> omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e1
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e2
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e3
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e4
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e5
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e6
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e7
  · rw [hrd _ (by omega) (by omega) (by omega) (by omega)]; exact e8

/-- The slots survive a store that misses each of them. -/
theorem Slots.of_write {sp0 fn pool T d n ret fp : Nat} {m : Memory} (h : Slots sp0 fn pool T d n ret fp m)
    (a k v : Nat) (hd : ∀ x, (x = sp0 - 48 ∨ x = sp0 - 40 ∨ x = sp0 - 32 ∨ x = sp0 - 24 ∨ x = sp0 - 16 ∨
      x = sp0 + 8 ∨ x = sp0 - 144 ∨ x = sp0 - 152) → a + k ≤ x ∨ x + 8 ≤ a) :
    Slots sp0 fn pool T d n ret fp (m.writeLE a k v) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
  have h1 := hd (sp0 - 48) (by omega); have h2 := hd (sp0 - 40) (by omega)
  have h3 := hd (sp0 - 32) (by omega); have h4 := hd (sp0 - 24) (by omega)
  have h5 := hd (sp0 - 16) (by omega); have h6 := hd (sp0 + 8) (by omega)
  have h7 := hd (sp0 - 144) (by omega); have h8 := hd (sp0 - 152) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e1
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e2
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e3
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e4
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e5
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e6
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e7
  · rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact e8

/-- An opaque wrapper: a hypothesis `Hid P` is not scanned by the executor's side-condition
dischargers (a hypothesis with `accessible` facts inside, e.g. a `MemFrame`, would be). -/
@[irreducible] def Hid (P : Prop) : Prop := P

theorem Hid.mk {P : Prop} (h : P) : Hid P := by unfold Hid; exact h
theorem Hid.get {P : Prop} (h : Hid P) : P := by unfold Hid at h; exact h

/-- The postcondition. -/
def Post (R : RtInv) (B : Nat) (n : BitVec 64) (L : List (Nat × Nat)) (bud : Nat) (s s' : State) : Prop :=
  ∃ cap0, cap0 ≤ B ∧
    (s'.regs 0).toNat = (if n.toNat ≤ cap0 then cap0 else growCap8 n.toNat cap0) ∧
    ∃ ex b', FreshFrom ex L ∧ b' ≤ bud ∧
      MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) ∧
      LiveFrame s.mem s'.mem L [] ∧
      R.inv b' (L ++ ex) (s.regs 28).toNat (view R.rt (L ++ ex) s'.mem)

/-- Everything the proof of `correctness` knows at the entry state `s` and about the runtime. -/
structure World (impl : List Segment) (R : RtInv) (B : Nat) (n : BitVec 64) (L : List (Nat × Nat))
    (bud ret : Nat) (s : State) : Prop where
  get : PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get")
    4096 R ptrType (SliceObj B)
  put : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
    4096 R ptrType (SliceObj B)
  new : NewobjectLiveContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") 4096 R
  grow : GrowsliceLiveContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.growslice") 4096 R
  clr : MemclrNoHeapPointersLive (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R
  wb : WbLiveContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2
  ty : s.mem.readLE stkType 8 = 24 ∧ s.mem.readLE (stkType + 8) 8 = 8
  hret : RetAddr (Extracted.program.link impl) ret
  lr : s.regs 30 = BitVec.ofNat 64 ret
  g1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  g2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true
  g3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4288 < s.sp.toNat
  al : s.sp.toNat % 16 = 0
  b4 : 4288 ≤ s.sp.toNat
  a4 : s.sp.toNat + 24 ≤ 2 ^ 48
  w4 : s.mem.accessible (s.sp.toNat - 4288) (4288 + 24) true = true
  go : Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4288, s.sp.toNat + 24) :: R.rt)
  wrt : LiveSep [(s.sp.toNat - 4288, s.sp.toNat + 24)] R.rt
  wL : LiveSep L [(s.sp.toNat - 4288, s.sp.toNat + 24)]
  rt0 : ∀ r ∈ R.rt, 0 < r.1
  pin : poolAddr + 40 ≤ s.sp.toNat - 4288 ∨ s.sp.toNat + 24 ≤ poolAddr
  sin : Outside stkType 16 R.rt
  sL : Outside stkType 16 [(s.sp.toNat - 4288, s.sp.toNat + 24)]
  u64 : Outside u64Type 16 R.rt
  facc : s.mem.accessible wbFlag 4 false = true
  okG : R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr]
  okP : R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr]
  okN : R.ok (Extracted.program.contractAddr "runtime.newobject") [stkType]
  okGr : ∀ p c, c ≤ B → c < n.toNat →
    R.ok (Extracted.program.contractAddr "runtime.growslice") [p, n.toNat, c, n.toNat - c, u64Type]
  okClr : ∀ q c, c ≤ B → c < n.toNat →
    R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [q + 8 * c, 8 * (n.toNat - c)]
  okWb : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2]
  new0 : s.mem.readLE (poolAddr + newOffset) 8 = 0
  u64v : s.mem.readLE u64Type 8 = 8 ∧ s.mem.readLE (u64Type + 8) 8 = 0
  u64acc : s.mem.accessible u64Type 16 false = true
  u64W : Outside u64Type 16 [(s.sp.toNat - 4288, s.sp.toNat + 24)]
  fl : ∀ b L g v, R.inv b L g v → Outside wbFlag 4 L
  inv : R.inv bud L (s.regs 28).toNat (view R.rt L s.mem)
  n40 : n.toNat < 2 ^ 40
  bud : ∀ c, c ≤ B → c < n.toNat → 24 + 8 * growCap8 n.toNat c ≤ bud
  capB : ∀ c, c ≤ B → c < n.toNat → growCap8 n.toNat c ≤ B
  B40 : B < 2 ^ 40

/-- The goal at a state `S` inside `StackGrow`: it returns, with the postcondition. -/
def Goal {impl R B n L bud ret s} (_ : World impl R B n L bud ret s) (S : State) : Prop :=
  Reaches ((Extracted.program.link impl).withExit ret) S
    (IsReturn fun s' => ABIReturn s s' ∧ Post R B n L bud s s')

/-! ## The header of a pooled stack -/

/-- The numeric facts of a pooled stack `{ptr = newp, len = 0, cap = capN}` at `d`. -/
def HdrPure (B d newp capN : Nat) : Prop :=
  0 < d ∧ d % 8 = 0 ∧ d + 24 ≤ 2 ^ 48 ∧ capN ≤ B ∧ B < 2 ^ 40 ∧ newp % 8 = 0 ∧
    newp + 8 * capN ≤ 2 ^ 48 ∧ Disjoint d 24 newp (8 * capN)

/-- ... and in memory `m`: its header `{ptr, 0, capN}` (the pointer word is stored last), the header
and the array writable. -/
def HdrOK (B d newp capN : Nat) (m : Memory) : Prop :=
  HdrPure B d newp capN ∧ m.accessible d 24 true = true ∧
    (0 < capN → m.accessible newp (8 * capN) true = true) ∧
    m.readLE (d + 8) 8 = 0 ∧ m.readLE (d + 16) 8 = capN

/-- The ranges such a stack owns. -/
def rsOf (d newp capN : Nat) : List (Nat × Nat) :=
  (d, d + 24) :: (if capN = 0 then [] else [(newp, newp + 8 * capN)])

theorem sliceObj_of_hdr {B d newp capN : Nat} {m : Memory} (h : HdrOK B d newp capN m) :
    SliceObj B (m.writeLE d 8 newp) d (rsOf d newp capN) := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, ha, hb, hlen, hcap⟩ := h
  have e0 : (m.writeLE d 8 newp).readLE d 8 = newp := by
    rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  have e1 : (m.writeLE d 8 newp).readLE (d + 8) 8 = 0 := by
    rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact hlen
  have e2 : (m.writeLE d 8 newp).readLE (d + 16) 8 = capN := by
    rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact hcap
  unfold SliceObj
  simp only [Memory.accessible_writeLE, e0, e1, e2]
  exact ⟨h0, h1, h2, ha, Nat.zero_le _, h3, h4, h5, h6, hb, h7, rfl⟩

/-! ## The tail: the closure, the deferred `Put` and the return -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem tail2 {impl : List Segment} {R : RtInv} {B : Nat} {n : BitVec 64} {L : List (Nat × Nat)}
    {bud ret : Nat} {s : State} (W : World impl R B n L bud ret s)
    (S : State) (m2 : Memory) (d capN newp cap0 b2 : Nat) (L2 ex : List (Nat × Nat))
    (hpc : S.pc = 603556#64) (hmem : S.mem = m2) (hsp : S.sp = s.sp - 144#64) (hg : S.regs 28 = s.regs 28)
    (hx18 : S.regs 18 = s.regs 18) (hx1 : (S.regs 1).toNat = d) (hx2 : (S.regs 2).toNat = capN)
    (hx5 : (S.regs 5).toNat = newp)
    (hSl : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m2)
    (hF : MemFrame s.mem m2 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]))
    (hLF : LiveFrame s.mem m2 L [])
    (hdrt : InRanges d 24 R.rt) (hLd : LiveSep L [(d, d + 24)]) (hH : HdrOK B d newp capN m2)
    (hrs : ∀ r ∈ rsOf d newp capN, r ∈ L2) (hdL : (d, d + 24) ∈ L2) (hLsub : ∀ r ∈ L, r ∈ L2)
    (hrsrt : ∀ x ∈ rsOf d newp capN, InRanges x.1 (x.2 - x.1) R.rt)
    (hL2W : LiveSep L2 [(s.sp.toNat - 4288, s.sp.toNat + 24)])
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 m2))
    (hdrop : Pool.dropAll L2 (rsOf d newp capN) = L ++ ex) (hfresh : FreshFrom ex L)
    (hb2 : b2 ≤ bud) (hcap0 : cap0 ≤ B)
    (hcapN : capN = if n.toNat ≤ cap0 then cap0 else growCap8 n.toNat cap0) :
    Goal W S := by
  unfold Goal
  obtain ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hret, hlr, hg1, hg2, hg3, hal, hb4, ha4, hw4, hgo, hwrt,
    hwL, hrt0, hpin, hsin, hsL, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hu64v, hu64acc, hu64W, hfl, hinv0, hn40,
    hbud, hcapB, hB40⟩ := W
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  rw [hP] at hokP
  have hSh := sliceObj_of_hdr hH
  obtain ⟨⟨hd0, hd8, hd48, -⟩, hdacc24, -⟩ := hH
  have hSlAll := hSl
  obtain ⟨hSl1, hSl2, hSl3, hSl4, hSl5, hSl6, hSl7, hSl8⟩ := hSl
  have hdW := InRanges.disjoint hdrt (hwrt _ (List.mem_singleton_self _))
  simp only at hdW
  have hgw : m2.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true, outside_append] at hgo ⊢
      exact ⟨hgo.2, hgo.1⟩)
  subst hmem
  have hdacc : S.mem.accessible d 8 true = true := Memory.accessible_mono _ hdacc24 (Nat.le_refl _) (by omega)
  have hdaccf : S.mem.accessible d 8 false = true := Memory.accessible_sub _ hdacc24 (Or.inl rfl) (Nat.le_refl _) (by omega)
  subst hx1 hx2 hx5
  have hwS : S.mem.accessible (s.sp.toNat - 4288) (4288 + 24) true = true := by
    rw [hF.accessible]; exact hw4
  have hgS : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by
    rw [hF.accessible]; exact hg2
  have hgo' := hgo
  simp only [outside_cons, outside_nil, and_true] at hgo'
  have hgd := InRanges.disjoint hdrt hgo'.2
  have hpack := Hid.mk (And.intro hSh (And.intro hF (And.intro hLF (And.intro hrs (And.intro hdL
    (And.intro hLsub (And.intro hrsrt (And.intro hL2W (And.intro hinv (And.intro hdrop (And.intro hfresh
    (And.intro hb2 (And.intro hcap0 (And.intro hcapN (And.intro hLd hdrt)))))))))))))))
  have hpack2 := Hid.mk (And.intro hput hokP)
  clear hSh hF hLF hrs hdL hLsub hrsrt hL2W hinv hdrop hfresh hb2 hcap0 hcapN hLd hdrt hput hokP
  clear hget hnew hgrow hclr hwb hRty hokGr hokClr hokG hokN hokWb hinv0 hsin hsL hu64 hfacc hpin
  janus_run [hdacc, hdaccf, hSl1, hSl2, hSl3, hSl4, hSl5, hSl6, hsp, hg, hgw] until [Extracted.program.contractAddr "sync.(*Pool).Put"]
  obtain ⟨hSh, hF, hLF, hrs, hdL, hLsub, hrsrt, hL2W, hinv, hdrop, hfresh, hb2, hcap0, hcapN, hLd, hdrt⟩ :=
    hpack.get
  obtain ⟨hput, hokP⟩ := hpack2.get
  have hdinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 (S.mem.writeLE (BitVec.toNat (S.regs 1)) 8 (BitVec.toNat (S.regs 5)))) :=
    RtInv.inv_frame' (ws := [(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 8)]) (m := S.mem)
      (((MemFrame.refl S.mem [(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 8)]).writeLE
        (BitVec.toNat (S.regs 5)) (List.mem_singleton_self _) (Nat.le_refl _) (by simp))) (fun r hr => Or.inr (by
          simp only [List.mem_singleton] at hr; rw [hr]
          exact ⟨(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 24), hdL, Nat.le_refl _, by simp⟩)) hinv
  have hqP : S.mem.readLE (s.sp.toNat - 48 + 8) 8 = 1547840 := by
    have := hSl2; rwa [show s.sp.toNat - 40 = s.sp.toNat - 48 + 8 by omega] at this
  have hqT : S.mem.readLE (s.sp.toNat - 48 + 16) 8 = 685248 := by
    have := hSl3; rwa [show s.sp.toNat - 32 = s.sp.toNat - 48 + 16 by omega] at this
  have hqD : S.mem.readLE (s.sp.toNat - 48 + 24) 8 = BitVec.toNat (S.regs 1) := by
    have := hSl4; rwa [show s.sp.toNat - 24 = s.sp.toNat - 48 + 24 by omega] at this
  have hsp192 : (s.sp - 192#64).toNat = s.sp.toNat - 192 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have key3 : ∀ S3 : State,
      MemFrame (S.mem.writeLE (BitVec.toNat (S.regs 1)) 8 (BitVec.toNat (S.regs 5))) S3.mem
        [(s.sp.toNat - 4288, s.sp.toNat + 24)] →
      S3.regs 28 = s.regs 28 → S3.sp.toNat + 192 = s.sp.toNat → (S3.regs 30).toNat % 4 = 0 →
      (S3.regs 30).toNat < 2 ^ 48 → (S3.regs 0).toNat = 1547840 → (S3.regs 1).toNat = 685248 →
      (S3.regs 2).toNat = BitVec.toNat (S.regs 1) →
      CallOK S3 4096 3 ∧ StackRoom S3 4096 3 ∧ (S3.regs 1).toNat = ptrType ∧
        SliceObj B S3.mem (S3.regs 2).toNat (rsOf (BitVec.toNat (S.regs 1)) (BitVec.toNat (S.regs 5)) (BitVec.toNat (S.regs 2))) ∧ (∀ r ∈ rsOf (BitVec.toNat (S.regs 1)) (BitVec.toNat (S.regs 5)) (BitVec.toNat (S.regs 2)), r ∈ L2) ∧
        LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Put") [(S3.regs 0).toNat] L2 b2 0
          (S3.regs 28).toNat S3.mem (calleeStack S3 4096 3) := by
    intro S3 hm hg3' hsp3 h30a h30b h0 h1 h2
    have hfr0 : MemFrame s.mem S3.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) :=
      MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)])
        (hF.writeLE_inRanges _ ((hdrt.sub (a := BitVec.toNat (S.regs 1)) (n := 8) (Nat.le_refl _) (by omega)).append_left _)) hm (by frame_sub)
    have h := call_pre R L2 b2 0 (Extracted.program.contractAddr "sync.(*Pool).Put") [(S3.regs 0).toNat]
      (s := s) (S := S3) (lo := s.sp.toNat - 4288) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 3)
      (fr := 192) hg1 hg2 (by omega) hgo hfr0 hg3' hsp3 (by omega) h30a h30b (by decide) (by omega)
      (by omega) (by omega) ha4
      (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hL2W
      (by rw [h0]; exact hokP) (by rw [hg3']; exact RtInv.inv_frame hm hwrt hdinv) (Nat.zero_le _)
    refine ⟨h.1, h.2.1, by rw [h1]; exact hT.symm, ?_, hrs, h.2.2⟩
    rw [h2]
    exact SliceObj.of_frame hSh hm (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine Reaches.call (Summary.withExit (hput L2 b2 (rsOf (BitVec.toNat (S.regs 1)) (BitVec.toNat (S.regs 5)) (BitVec.toNat (S.regs 2)))) hret) (by rfl) ?_ ?_
  · refine key3 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · janus_frame
    · simp [setReg, hg]
    · simp [hsp192]; omega
    · simp [setReg]
    · simp [setReg]
    · simp [setReg, hqP]
    · simp [setReg, hqT]
    · simp [setReg, hqD]
  intro s3 hpc3 ⟨r3, vr3, fl3, m4, ex3, ep3, hs3, hfr3, hlf3, hns3, hinv3⟩
  subst hs3
  simp only [calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, hsp192] at hfr3 hlf3 hns3 hinv3
  rw [hdrop, hg] at hinv3
  have hSlS3 := Slots.step (spc := s.sp.toNat - 192) (k := 3) (fn := 603664) (pool := 1547840) (T := 685248)
    (d := BitVec.toNat (S.regs 1)) (n := n.toNat) (ret := ret) (fp := (s.regs 29).toNat) hwrt hb4 (by omega)
    (Or.inr (by omega)) (by omega) (by
      exact ((((hSlAll.of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)).of_write _ _ _
        (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega))
    hfr3
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hSlS3
  have e56 : m4.readLE (s.sp.toNat - 88) 8 = BitVec.toNat (S.regs 2) := by
    rw [keep_read hwrt hfr3 (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (S.regs 2).isLt
  have eLR : m4.readLE (s.sp.toNat - 192) 8 = 603580 := by
    rw [keep_read hwrt hfr3 (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]
  have eFP : m4.readLE (s.sp.toNat - 200) 8 = BitVec.toNat (S.regs 29) := by
    rw [keep_read hwrt hfr3 (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (S.regs 29).isLt
  clear hpc3
  have hret4 := hret.aligned
  have hret48 := hret.user
  janus_run [e56, eLR, eFP, q7, q8, hsp144, hsp192]
  have hLsepD : LiveSep L [(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 8)] := fun r hr => by
    have := hLd r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hstq : MemFrame S.mem (S.mem.writeLE (BitVec.toNat (S.regs 1)) 8 (BitVec.toNat (S.regs 5)))
      [(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 8)] :=
    (MemFrame.refl S.mem [(BitVec.toNat (S.regs 1), BitVec.toNat (S.regs 1) + 8)]).writeLE
      (BitVec.toNat (S.regs 5)) (List.mem_singleton_self _) (Nat.le_refl _) (by simp)
  unfold Post
  refine ⟨cap0, hcap0, ?_, ex, b2, hfresh, hb2, ?_, ?_, ?_⟩
  · simp [setReg, hcapN]
  · exact MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)])
      (MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)])
        (hF.writeLE_inRanges _ ((hdrt.sub (a := BitVec.toNat (S.regs 1)) (n := 8) (Nat.le_refl _) (by omega)).append_left _))
        (rs' := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) (by janus_frame) (by frame_sub)) hfr3 (by frame_sub)
  · exact LiveFrame.trans hLF (LiveFrame.trans (LiveFrame.of_win hstq hLsepD)
      (LiveFrame.trans (LiveFrame.of_win (ws := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) (by janus_frame) hwL)
        hlf3 (fun a n h => h.of_subset hLsub)) (fun _ _ h => h)) (fun _ _ h => h)
  · exact hinv3

/-! ## The header store and the write barrier -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem tail1 {impl : List Segment} {R : RtInv} {B : Nat} {n : BitVec 64} {L : List (Nat × Nat)}
    {bud ret : Nat} {s : State} (W : World impl R B n L bud ret s)
    (S : State) (m1 : Memory) (d capN newp cap0 b2 : Nat) (L2 ex : List (Nat × Nat))
    (hpc : S.pc = 603528#64) (hmem : S.mem = m1) (hsp : S.sp = s.sp - 144#64) (hg : S.regs 28 = s.regs 28)
    (hx18 : S.regs 18 = s.regs 18) (hx1 : (S.regs 1).toNat = d) (hx2 : (S.regs 2).toNat = capN)
    (hx5 : (S.regs 5).toNat = newp)
    (hSl : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m1)
    (hF : MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]))
    (hLF : LiveFrame s.mem m1 L [])
    (hdrt : InRanges d 24 R.rt) (hLd : LiveSep L [(d, d + 24)])
    (hP : HdrPure B d newp capN) (hdacc24 : m1.accessible d 24 true = true)
    (harr : 0 < capN → m1.accessible newp (8 * capN) true = true)
    (hrs : ∀ r ∈ rsOf d newp capN, r ∈ L2) (hdL : (d, d + 24) ∈ L2) (hLsub : ∀ r ∈ L, r ∈ L2)
    (hrsrt : ∀ x ∈ rsOf d newp capN, InRanges x.1 (x.2 - x.1) R.rt)
    (hL2W : LiveSep L2 [(s.sp.toNat - 4288, s.sp.toNat + 24)])
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 m1))
    (hdrop : Pool.dropAll L2 (rsOf d newp capN) = L ++ ex) (hfresh : FreshFrom ex L)
    (hb2 : b2 ≤ bud) (hcap0 : cap0 ≤ B)
    (hcapN : capN = if n.toNat ≤ cap0 then cap0 else growCap8 n.toNat cap0) :
    Goal W S := by
  have W0 := W
  unfold Goal
  obtain ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hret, hlr, hg1, hg2, hg3, hal, hb4, ha4, hw4, hgo, hwrt,
    hwL, hrt0, hpin, hsin, hsL, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hu64v, hu64acc, hu64W, hfl, hinv0, hn40,
    hbud, hcapB, hB40⟩ := W
  janus_eval_nat hFl : wbFlag
  rw [hFl] at hfacc
  have hP0 := hP
  obtain ⟨hd0, hd8, hd48, hcB, hB, hnp8, hnp48, hdisj⟩ := hP
  have hdW := InRanges.disjoint hdrt (hwrt _ (List.mem_singleton_self _))
  simp only at hdW
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  subst hmem
  -- the memory after the header store `{len = 0, cap = capN}`
  obtain ⟨mA, hmA⟩ : ∃ mA, mA = (S.mem.writeLE (d + 8) 8 0).writeLE (d + 16) 8 capN := ⟨_, rfl⟩
  have hAacc : ∀ a n w, mA.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hmA]; simp only [Memory.accessible_writeLE]
  have hFA : MemFrame s.mem mA (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) := by
    rw [hmA]
    exact (hF.writeLE_inRanges 0 ((hdrt.sub (a := d + 8) (n := 8) (by omega) (by omega)).append_left _)).writeLE_inRanges
      capN ((hdrt.sub (a := d + 16) (n := 8) (by omega) (by omega)).append_left _)
  have hdLsep : LiveSep L [(d, d + 24)] := hLd
  have hLFA : LiveFrame s.mem mA L [] := by
    refine LiveFrame.trans hLF (LiveFrame.of_win (ws := [(d, d + 24)]) ?_ hLd) (fun _ _ h => h)
    rw [hmA]
    exact ((MemFrame.refl S.mem [(d, d + 24)]).writeLE 0 (List.mem_singleton_self _) (by omega) (by simp <;> omega)).writeLE
      capN (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
  have hSlA : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat mA := by
    rw [hmA]
    exact (hSl.of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)
  have hHA : HdrOK B d newp capN mA := by
    refine ⟨hP0, ?_, ?_, ?_, ?_⟩
    · rw [hAacc]; exact hdacc24
    · intro h; rw [hAacc]; exact harr h
    · rw [hmA, Memory.readLE_writeLE_of_disjoint (h := by omega), Memory.readLE_writeLE_self]
    · rw [hmA, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  have hinvA : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 mA) := by
    rw [hmA, view_writeLE_live ⟨(d, d + 24), hdL, by omega, by omega⟩,
      view_writeLE_live ⟨(d, d + 24), hdL, by omega, by omega⟩]
    exact hinv
  have hdacc8a : S.mem.accessible ((S.regs 1).toNat + 8) 8 true = true := by
    rw [hx1]; exact Memory.accessible_mono _ hdacc24 (by omega) (by omega)
  have hdacc8b : S.mem.accessible ((S.regs 1).toNat + 16) 8 true = true := by
    rw [hx1]; exact Memory.accessible_mono _ hdacc24 (by omega) (by omega)
  have hdaccf : S.mem.accessible (S.regs 1).toNat 8 false = true := by
    rw [hx1]; exact Memory.accessible_sub _ hdacc24 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hflag : S.mem.accessible 1705440 4 false = true := by rw [hF.accessible]; exact hfacc
  have hflo := hfl _ _ _ _ hinv
  rw [hFl] at hflo
  have hflD := MemFrame.outside_mem hflo hdL
  simp only at hflD
  have hflD' : 1705440 + 4 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 24 ≤ 1705440 := by rw [hx1]; exact hflD
  have hpack := Hid.mk (And.intro hF (And.intro hLF (And.intro hrs (And.intro hdL (And.intro hLsub (And.intro hrsrt (And.intro hL2W (And.intro hinv (And.intro hdrop (And.intro hfresh (And.intro hb2 (And.intro hcap0 (And.intro hcapN (And.intro hLd (And.intro hdrt (And.intro hSl (And.intro harr (And.intro hFA (And.intro hLFA (And.intro hSlA (And.intro hHA (And.intro hinvA (And.intro hmA hAacc)))))))))))))))))))))))
  have hpack2 := Hid.mk (And.intro hwb (And.intro hokWb (And.intro hput hRty)))
  clear hF hLF hrs hdL hLsub hrsrt hL2W hinv hdrop hfresh hb2 hcap0 hcapN hLd hdrt hSl harr hFA hLFA hSlA hHA hinvA
  clear hmA hAacc hwb hokWb hput hRty hget hnew hgrow hclr hokP hokG hokN hokGr hokClr hfl hinv0 hsin hsL hu64 hfacc hpin hdLsep
  janus_run [hdacc24, hdacc8a, hdacc8b, hdaccf, hflag, hsp, hg] until [Extracted.program.contractAddr "runtime.gcWriteBarrier2", 603556]
  · -- the barrier is off
    obtain ⟨hF, hLF, hrs, hdL, hLsub, hrsrt, hL2W, hinv, hdrop, hfresh, hb2, hcap0, hcapN, hLd, hdrt, hSl, harr,
      hFA, hLFA, hSlA, hHA, hinvA, hmA, hAacc⟩ := hpack.get
    obtain ⟨hwb, hokWb, hput, hRty⟩ := hpack2.get
    exact tail2 W0 _ mA d capN newp cap0 b2 L2 ex rfl (by rw [hmA, hx1, hx2]) rfl (by simp [setReg, hg])
      (by simp [setReg, hx18]) (by simp [setReg, hx1]) (by simp [setReg, hx2]) (by simp [setReg, hx5])
      hSlA hFA hLFA hdrt hLd hHA hrs hdL hLsub hrsrt hL2W hinvA hdrop hfresh hb2 hcap0 hcapN
  · -- the barrier is on
    obtain ⟨hF, hLF, hrs, hdL, hLsub, hrsrt, hL2W, hinv, hdrop, hfresh, hb2, hcap0, hcapN, hLd, hdrt, hSl, harr,
      hFA, hLFA, hSlA, hHA, hinvA, hmA, hAacc⟩ := hpack.get
    obtain ⟨hwb, hokWb, hput, hRty⟩ := hpack2.get
    have hmemlit : (S.mem.writeLE ((S.regs 1).toNat + 8) 8 0).writeLE ((S.regs 1).toNat + 16) 8
        (S.regs 2).toNat = mA := by rw [hmA, hx1, hx2]
    refine Reaches.call (Summary.withExit (hwb L2 b2) hret) (by rfl) ?_ ?_
    · dsimp only
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hokWb, ?_, ?_, ?_⟩
      · simp [setReg]
      · simp [setReg]
      · rw [hsp144]; omega
      · rw [hsp144]; omega
      · decide
      · rw [hsp144]; omega
      · rw [hmemlit, hAacc, hF.accessible, hsp144]
        exact Memory.accessible_mono _ hw4 (by omega) (by omega)
      · rw [hmemlit]; simpa [setReg, hg] using hinvA
      · rw [hsp144]; exact LiveSep.sub_win hL2W (by omega) (by omega)
      · rw [hsp144]; exact LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega)
    intro S2 hpc2 ⟨buf, junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
    subst hs2
    simp only [hsp144, hmemlit] at hfr2 hlf2
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hbufN : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hbw := InRanges.disjoint hbufN (hwrt _ (List.mem_singleton_self _))
    simp only at hbw
    have hap16 : ApartAll buf.toNat 16 L2 := by simpa using hapL
    have hout16 : Outside buf.toNat 16 L2 := hap16.outside
    have hdb := hap16 _ hdL
    simp only [Apart] at hdb
    have hacc16 : m'.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hacc8a : m'.accessible buf.toNat 8 true = true :=
      Memory.accessible_mono _ hacc16 (Nat.le_refl _) (by omega)
    have hacc8b : m'.accessible (buf.toNat + 8) 8 true = true :=
      Memory.accessible_mono _ hacc16 (by omega) (by omega)
    have hSlM : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m' :=
      Slots.step (spc := s.sp.toNat - 144) (k := 0) hwrt hb4 (by omega) (Or.inl rfl) (by omega) hSlA
        (hfr2.mono (fun a n h => by
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.1, h.2.1⟩))
    have hinvS' : InvSlots R b2 L2 (s.regs 28).toNat R.rt m' buf.toNat 2 := by
      simpa [InvSlots, setReg, hg] using hinvS
    have post : ∀ x1 x2 : Nat,
        Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat
          ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2) ∧
        MemFrame s.mem ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2)
          (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) ∧
        LiveFrame s.mem ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2) L [] ∧
        HdrOK B d newp capN ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2) ∧
        R.inv b2 L2 (s.regs 28).toNat
          (view R.rt L2 ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2)) := by
      intro x1 x2
      have hstore : MemFrame m' ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2)
          [(buf.toNat, buf.toNat + 16)] :=
        (((MemFrame.refl m' [(buf.toNat, buf.toNat + 16)]).writeLE (a := buf.toNat) (k := 8) x1
          (r := (buf.toNat, buf.toNat + 16)) (List.mem_singleton_self _) (Nat.le_refl _)
          (show buf.toNat + 8 ≤ buf.toNat + 16 by omega)).writeLE (a := buf.toNat + 8) (k := 8)
          x2 (r := (buf.toNat, buf.toNat + 16)) (List.mem_singleton_self _)
          (show buf.toNat ≤ buf.toNat + 8 by omega) (show buf.toNat + 8 + 8 ≤ buf.toNat + 16 by omega))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (hSlM.of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)
      · exact ((MemFrame.trans hFA hfr2 (by frame_sub)).writeLE_inRanges x1
          ((hbufN.sub (a := buf.toNat) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges x2
          ((hbufN.sub (a := buf.toNat + 8) (n := 8) (by omega) (by omega)).append_left _)
      · have hLs : LiveSep L [(buf.toNat, buf.toNat + 16)] := fun r hr => by
          have := hap16 r (hLsub r hr)
          simp only [Apart] at this
          simp only [outside_cons, outside_nil, and_true]
          omega
        exact LiveFrame.trans (LiveFrame.trans hLFA hlf2 (fun a n h => h.of_subset hLsub))
          (LiveFrame.of_win hstore hLs) (fun _ _ h => h)
      · obtain ⟨hP1, hda, har, h8, h16⟩ := hHA
        refine ⟨hP1, ?_, ?_, ?_, ?_⟩
        · simp only [Memory.accessible_writeLE, hfr2.accessible]; exact hda
        · intro hc; simp only [Memory.accessible_writeLE, hfr2.accessible]; exact har hc
        · rw [Memory.readLE_writeLE_of_disjoint (h := by omega), Memory.readLE_writeLE_of_disjoint (h := by omega),
            hlf2.readLE _ _ ⟨(d, d + 24), hdL, by omega, by omega⟩ trivial]
          exact h8
        · rw [Memory.readLE_writeLE_of_disjoint (h := by omega), Memory.readLE_writeLE_of_disjoint (h := by omega),
            hlf2.readLE _ _ ⟨(d, d + 24), hdL, by omega, by omega⟩ trivial]
          exact h16
      · have hv1 : view R.rt L2 ((m'.writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2) =
            ((view R.rt L2 m').writeLE buf.toNat 8 x1).writeLE (buf.toNat + 8) 8 x2 := by
          rw [view_writeLE_vis (hbufN.sub (a := buf.toNat + 8) (n := 8) (by omega) (by omega))
              (Outside.of_sub hout16 (by omega) (by omega)),
            view_writeLE_vis (hbufN.sub (a := buf.toNat) (n := 8) (Nat.le_refl _) (by omega))
              (Outside.of_sub hout16 (Nat.le_refl _) (by omega))]
        rw [hv1]
        refine hinvS' _ ?_
        exact (((MemFrame.refl (view R.rt L2 m') [(buf.toNat, buf.toNat + 8 * 2)]).writeLE (a := buf.toNat) (k := 8) x1
          (r := (buf.toNat, buf.toNat + 8 * 2)) (List.mem_singleton_self _) (Nat.le_refl _)
          (show buf.toNat + 8 ≤ buf.toNat + 8 * 2 by omega)).writeLE (a := buf.toNat + 8) (k := 8) x2
          (r := (buf.toNat, buf.toNat + 8 * 2)) (List.mem_singleton_self _)
          (show buf.toNat ≤ buf.toNat + 8 by omega) (show buf.toNat + 8 + 8 ≤ buf.toNat + 8 * 2 by omega))
    have hpost := Hid.mk post
    clear post hSlM hinvS' hinvS hapL hapW hsl3 hsl4 hsl2 hsl1 hlf2 hfr2 hFA hLFA hSlA hHA hinvA hF hLF hSl hAacc hmA
    janus_run [hacc8a, hacc8b, hbuf64] until [603556]
    obtain ⟨hSl2, hF2, hLF2, hH2, hinv2⟩ := hpost.get _ _
    exact tail2 W0 _ _ d capN newp cap0 b2 L2 ex rfl rfl rfl (by simp [wbRetX, wbRegs_apply, setReg, hg])
      (by simp [wbRetX, wbRegs_apply, setReg, hx18]) (by simp [wbRetX, wbRegs_apply, setReg, hx1])
      (by simp [wbRetX, wbRegs_apply, setReg, hx2]) (by simp [wbRetX, wbRegs_apply, setReg, hx5])
      hSl2 hF2 hLF2 hdrt hLd hH2 hrs hdL hLsub hrsrt hL2W hinv2 hdrop hfresh hb2 hcap0 hcapN

/-! ## After `memclrNoHeapPointers`: the reloads -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem afterClr {impl : List Segment} {R : RtInv} {B : Nat} {n : BitVec 64} {L : List (Nat × Nat)}
    {bud ret : Nat} {s : State} (W : World impl R B n L bud ret s)
    (S : State) (m1 : Memory) (d capN newp cap0 b2 : Nat) (L2 ex : List (Nat × Nat))
    (hpc : S.pc = 603516#64) (hmem : S.mem = m1) (hsp : S.sp = s.sp - 144#64) (hg : S.regs 28 = s.regs 28)
    (hx18 : S.regs 18 = s.regs 18)
    (e88 : m1.readLE (s.sp.toNat - 56) 8 = d) (e64 : m1.readLE (s.sp.toNat - 80) 8 = capN)
    (e80 : m1.readLE (s.sp.toNat - 64) 8 = newp)
    (hSl : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m1)
    (hF : MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]))
    (hLF : LiveFrame s.mem m1 L [])
    (hdrt : InRanges d 24 R.rt) (hLd : LiveSep L [(d, d + 24)])
    (hP : HdrPure B d newp capN) (hdacc24 : m1.accessible d 24 true = true)
    (harr : 0 < capN → m1.accessible newp (8 * capN) true = true)
    (hrs : ∀ r ∈ rsOf d newp capN, r ∈ L2) (hdL : (d, d + 24) ∈ L2) (hLsub : ∀ r ∈ L, r ∈ L2)
    (hrsrt : ∀ x ∈ rsOf d newp capN, InRanges x.1 (x.2 - x.1) R.rt)
    (hL2W : LiveSep L2 [(s.sp.toNat - 4288, s.sp.toNat + 24)])
    (hinv : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 m1))
    (hdrop : Pool.dropAll L2 (rsOf d newp capN) = L ++ ex) (hfresh : FreshFrom ex L)
    (hb2 : b2 ≤ bud) (hcap0 : cap0 ≤ B)
    (hcapN : capN = if n.toNat ≤ cap0 then cap0 else growCap8 n.toNat cap0) :
    Goal W S := by
  have W0 := W
  unfold Goal
  obtain ⟨regsS, spS, pcS, flS, memS, dczS, vrS, tpS, fcS, fsS⟩ := S
  simp only at hpc hmem hsp hg hx18
  subst hpc hsp
  have hw4 := W.w4
  have hret := W.hret
  have hb4 := W.b4
  have ha4 := W.a4
  have hal := W.al
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  subst hmem
  have hwS : memS.accessible (s.sp.toNat - 4288) (4288 + 24) true = true := by
    rw [hF.accessible]; exact hw4
  have hd64 : d < 2 ^ 64 := by have := hP.2.2.1; omega
  have hpack := Hid.mk (And.intro hF (And.intro hLF (And.intro hSl (And.intro hdrt (And.intro hLd
    (And.intro hP (And.intro hdacc24 (And.intro harr (And.intro hrs (And.intro hdL (And.intro hLsub
    (And.intro hrsrt (And.intro hL2W (And.intro hinv (And.intro hdrop (And.intro hfresh hcapN))))))))))))))))
  clear hF hLF hSl hdrt hLd hP hdacc24 harr hrs hdL hLsub hrsrt hL2W hinv hdrop hfresh hcapN W
  have hdd := hd64
  janus_run [e88, e64, e80, hg, hsp144] until [603528]
  obtain ⟨hF, hLF, hSl, hdrt, hLd, hP, hdacc24, harr, hrs, hdL, hLsub, hrsrt, hL2W, hinv, hdrop, hfresh, hcapN⟩ :=
    hpack.get
  have hcn64 : capN < 2 ^ 64 := by have := hP.2.2.2.1; have := hP.2.2.2.2.1; omega
  have hnp64 : newp < 2 ^ 64 := by have := hP.2.2.2.2.2.2.1; omega
  exact tail1 W0 _ _ d capN newp cap0 b2 L2 ex rfl rfl rfl (by simp [setReg, hg])
    (by simp [setReg, hx18]) (by simp [setReg, e88]; omega) (by simp [setReg, e64]; omega) (by simp [setReg, e80]; omega)
    hSl hF hLF hdrt hLd hP hdacc24 harr hrs hdL hLsub hrsrt hL2W hinv hdrop hfresh hb2 hcap0 hcapN

/-! ## After `growslice`: the clearing of the new elements -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem afterGrow {impl : List Segment} {R : RtInv} {B : Nat} {n : BitVec 64} {L : List (Nat × Nat)}
    {bud ret : Nat} {s : State} (W : World impl R B n L bud ret s)
    (S : State) (m : Memory) (d capN newp cap0 b3 : Nat) (L2 ex : List (Nat × Nat))
    (hpc : S.pc = 603468#64) (hmem : S.mem = m) (hsp : S.sp = s.sp - 144#64) (hg : S.regs 28 = s.regs 28)
    (hx18 : S.regs 18 = s.regs 18) (hx0 : (S.regs 0).toNat = newp) (hx1 : (S.regs 1).toNat = n.toNat)
    (hx2 : (S.regs 2).toNat = capN) (hcn : capN = growCap8 n.toNat cap0) (hcn' : cap0 < n.toNat)
    (hcap0 : cap0 ≤ B)
    (s72 : m.readLE (s.sp.toNat - 72) 8 = n.toNat - cap0) (s64 : m.readLE (s.sp.toNat - 80) 8 = cap0)
    (s56 : m.readLE (s.sp.toNat - 56) 8 = d)
    (hSl : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m)
    (hF : MemFrame s.mem m (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]))
    (hLF : LiveFrame s.mem m L [])
    (hdrt : InRanges d 24 R.rt) (hLd : LiveSep L [(d, d + 24)]) (hdacc24 : m.accessible d 24 true = true)
    (hd0 : 0 < d) (hd8 : d % 8 = 0) (hd48 : d + 24 ≤ 2 ^ 48)
    (hdL : (d, d + 24) ∈ L2) (hLsub : ∀ r ∈ L, r ∈ L2)
    (hL2W : LiveSep L2 [(s.sp.toNat - 4288, s.sp.toNat + 24)])
    (hdrop : Pool.dropAll (L2 ++ [(newp, newp + 8 * capN)]) (rsOf d newp capN) = L ++ ex)
    (hfresh : FreshFrom ex L) (hb3 : b3 ≤ bud)
    (hnrt : InRanges newp (8 * capN) R.rt) (hn48 : newp + 8 * capN ≤ 2 ^ 48)
    (hnacc : m.accessible newp (8 * capN) true = true) (hn8 : newp % 8 = 0) (hnap : ApartAll newp (8 * capN) L2)
    (hinv : R.inv b3 (L2 ++ [(newp, newp + 8 * capN)]) (s.regs 28).toNat
      (view R.rt (L2 ++ [(newp, newp + 8 * capN)]) m)) :
    Goal W S := by
  have W0 := W
  unfold Goal
  obtain ⟨regsS, spS, pcS, flS, memS, dczS, vrS, tpS, fcS, fsS⟩ := S
  simp only at hpc hmem hsp hg hx18 hx0 hx1 hx2
  subst hpc hsp hmem
  obtain ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hret, hlr, hg1, hg2, hg3, hal, hb4, ha4, hw4, hgo, hwrt,
    hwL, hrt0, hpin, hsin, hsL, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hu64v, hu64acc, hu64W, hfl, hinv0,
    hn40, hbud, hcapB, hB40⟩ := W
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hwS : memS.accessible (s.sp.toNat - 4288) (4288 + 24) true = true := by
    rw [hF.accessible]; exact hw4
  have hn64 : n.toNat < 2 ^ 64 := by omega
  have hcn64 : capN < 2 ^ 64 := by omega
  have hSlAll := hSl
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hSl
  have hx0' : regsS 0 = BitVec.ofNat 64 newp := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := (regsS 0).isLt; omega)
  have hx1' : regsS 1 = BitVec.ofNat 64 n.toNat := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := (regsS 1).isLt; omega)
  have hx2' : regsS 2 = BitVec.ofNat 64 capN := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := (regsS 2).isLt; omega)
  have hpack := Hid.mk (And.intro hF (And.intro hLF (And.intro hSlAll (And.intro hdrt (And.intro hLd (And.intro hdacc24 (And.intro hdL (And.intro hLsub (And.intro hL2W (And.intro hdrop (And.intro hfresh (And.intro hnrt (And.intro hnacc (And.intro hnap hinv))))))))))))))
  have hpack2 := Hid.mk (And.intro hclr hokClr)
  clear hF hLF hdrt hLd hdacc24 hdL hLsub hL2W hdrop hfresh hnrt hnacc hnap hinv hclr hokClr hSlAll
  clear hget hput hnew hgrow hwb hRty hokG hokP hokN hokGr hokWb hnew0 hfl hinv0 hsin hsL hu64 hfacc hpin
  janus_run [s72, s64, s56, q6, hg, hsp144, hx0', hx1', hx2'] until [Extracted.program.contractAddr "runtime.memclrNoHeapPointers"]
  obtain ⟨hF, hLF, hSlAll, hdrt, hLd, hdacc24, hdL, hLsub, hL2W, hdrop, hfresh, hnrt, hnacc, hnap, hinv⟩ := hpack.get
  obtain ⟨hclr, hokClr⟩ := hpack2.get
  have hcapn : n.toNat ≤ capN := hcn ▸ le_growCap8 _ _
  have hnw := InRanges.disjoint hnrt (hwrt _ (List.mem_singleton_self _))
  simp only at hnw
  have hnL : LiveSep [(newp, newp + 8 * capN)] [(s.sp.toNat - 4288, s.sp.toNat + 24)] := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [outside_cons, outside_nil, and_true]; omega
  have hL2'W : LiveSep (L2 ++ [(newp, newp + 8 * capN)]) [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
    rw [liveSep_append]; exact ⟨hL2W, hnL⟩
  have hinvW : ∀ S2 : State, MemFrame memS S2.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] →
      R.inv b3 (L2 ++ [(newp, newp + 8 * capN)]) (s.regs 28).toNat
        (view R.rt (L2 ++ [(newp, newp + 8 * capN)]) S2.mem) := fun S2 hm =>
    RtInv.inv_frame hm hwrt hinv
  have key : ∀ S2 : State, MemFrame memS S2.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] →
      S2.regs 28 = s.regs 28 → S2.sp.toNat + 144 = s.sp.toNat → (S2.regs 30).toNat % 4 = 0 →
      (S2.regs 30).toNat < 2 ^ 48 → (S2.regs 0).toNat = newp + 8 * cap0 →
      (S2.regs 1).toNat = 8 * (n.toNat - cap0) →
      Mem.EqPre 4096 2 S2 ∧
        LiveMemAt R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
          [(S2.regs 0).toNat, (S2.regs 1).toNat] (L2 ++ [(newp, newp + 8 * capN)]) b3 S2
          (calleeStack S2 4096 2) ∧
        LiveDest R (L2 ++ [(newp, newp + 8 * capN)]) S2 4096 2 (S2.regs 0).toNat (S2.regs 1).toNat := by
    intro S2 hm hg2' hsp2 h30a h30b h0 h1
    have hfr0 : MemFrame s.mem S2.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) :=
      MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hF
        (rs' := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hm (by frame_sub)
    have h := call_pre R (L2 ++ [(newp, newp + 8 * capN)]) b3 0
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
      [(S2.regs 0).toNat, (S2.regs 1).toNat] (s := s) (S := S2) (lo := s.sp.toNat - 4288)
      (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 2) (fr := 144) hg1 hg2 (by omega) hgo hfr0 hg2'
      hsp2 (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
      (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hL2'W
      (by rw [h0, h1]; exact hokClr newp cap0 hcap0 hcn') (by rw [hg2']; exact hinvW S2 hm) (Nat.zero_le _)
    refine ⟨(memPre_of h).1, (memPre_of h).2, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [h0, h1]; omega
    · rw [hm.accessible, h0, h1]
      exact Memory.accessible_mono _ hnacc (by omega) (by omega)
    · rw [h0, h1]
      simp only [calleeStack, outside_cons, outside_nil, and_true]
      omega
    · exact ⟨(newp, newp + 8 * capN), List.mem_append_right _ (List.mem_singleton_self _), by rw [h0]; omega,
        by rw [h0, h1]; omega⟩
  have hclrArgs : ∀ S2 : State, (S2.regs 0).toNat = newp + 8 * cap0 → (S2.regs 1).toNat = 8 * (n.toNat - cap0) →
      R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
        [(S2.regs 0).toNat, (S2.regs 1).toNat] := fun S2 h0 h1 => by
    rw [h0, h1]; exact hokClr newp cap0 hcap0 hcn'
  have hsh3 : ∀ x : Nat, x < 2 ^ 40 → (((BitVec.ofNat 64 x).rotateRight 61 &&& 18446744073709551608#64 &&&
      18446744073709551615#64)).toNat = 8 * x := fun x hx => by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_assoc]
    have : 18446744073709551608 &&& 18446744073709551615 = 18446744073709551608 := by decide
    rw [this, Janus.Contracts.Iface.lsl3_toNat]
    simp only [BitVec.toNat_ofNat]
    have h1 : x % 2 ^ 64 = x := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega
  refine Reaches.call (Summary.withExit (hclr (L2 ++ [(newp, newp + 8 * capN)]) b3) hret) (by rfl) ?_ ?_
  · refine key _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · janus_frame
    · simp [setReg, hg]
    · simp [hsp144]; omega
    · simp [setReg]
    · simp [setReg]
    · simp [setReg, hx0', hx1', Nat.shiftLeft_eq]
      omega
    · have := hsh3 (n.toNat - cap0) (by omega)
      simpa [setReg] using this
  have hcap0n : cap0 ≤ n.toNat := by omega
  have post : ∀ (S2 : State) (m' : Memory), (S2.regs 0).toNat = newp + 8 * cap0 →
      (S2.regs 1).toNat = 8 * (n.toNat - cap0) →
      S2.mem = (memS.writeLE (s.sp.toNat - 80) 8 capN).writeLE (s.sp.toNat - 64) 8 newp →
      S2.regs 28 = s.regs 28 →
      MemFrame S2.mem m' (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
        (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 8 * 2)] ++ [((S2.regs 0).toNat, (S2.regs 0).toNat + (S2.regs 1).toNat)]) →
      LiveFrame S2.mem m' (L2 ++ [(newp, newp + 8 * capN)]) [((S2.regs 0).toNat, (S2.regs 0).toNat + (S2.regs 1).toNat)] →
      R.inv b3 (L2 ++ [(newp, newp + 8 * capN)]) (S2.regs 28).toNat
        (view R.rt (L2 ++ [(newp, newp + 8 * capN)]) m') →
      Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat m' ∧
        MemFrame s.mem m' (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) ∧ LiveFrame s.mem m' L [] ∧
        m'.accessible d 24 true = true ∧ (0 < capN → m'.accessible newp (8 * capN) true = true) ∧
        m'.readLE (s.sp.toNat - 56) 8 = d ∧ m'.readLE (s.sp.toNat - 80) 8 = capN ∧
        m'.readLE (s.sp.toNat - 64) 8 = newp ∧
        R.inv b3 (L2 ++ [(newp, newp + 8 * capN)]) (s.regs 28).toNat
          (view R.rt (L2 ++ [(newp, newp + 8 * capN)]) m') := by
    intro S2 m' h0 h1 hmS2 hg2' hfr3 hlf3 hinv3
    have hex : ∀ x ∈ [((S2.regs 0).toNat, (S2.regs 0).toNat + (S2.regs 1).toNat)],
        InRanges x.1 (x.2 - x.1) R.rt := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hnrt.sub (by simp only; omega) (by simp only; omega)
    have hfr3' : MemFrame S2.mem m' (R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
        (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 8 * 2)]) :=
      hfr3.mono (fun a n h => by
        simp only [outside_append] at h ⊢
        exact ⟨h, outside_of_inRanges_rt h.1 hex⟩)
    have hm2 : MemFrame memS S2.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
      rw [hmS2]; janus_frame
    have hSlS2 : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat S2.mem := by
      rw [hmS2]
      exact (hSlAll.of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)
    refine ⟨Slots.step (spc := s.sp.toNat - 144) (k := 2) hwrt hb4 (by omega) (Or.inl rfl) (by omega) hSlS2 hfr3',
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)])
        (MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hF
          (rs' := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hm2 (by frame_sub)) hfr3' (by frame_sub)
    · have hLs : LiveSep L [((S2.regs 0).toNat, (S2.regs 0).toNat + (S2.regs 1).toNat)] := fun r hr => by
        have := hnap r (hLsub r hr)
        simp only [Apart] at this
        simp only [outside_cons, outside_nil, and_true]
        omega
      exact LiveFrame.trans hLF (LiveFrame.trans (LiveFrame.of_win hm2 hwL)
        (LiveFrame.of_sep hlf3 hLs (fun r hr => List.mem_append_left _ (hLsub r hr)))
        (fun _ _ h => h)) (fun _ _ h => h)
    · rw [hfr3.accessible, hm2.accessible]; exact hdacc24
    · intro hc; rw [hfr3.accessible, hm2.accessible]; exact hnacc
    · rw [keep_read (x := s.sp.toNat - 56) (k := 8) hwrt hfr3' (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega), hmS2]
      repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
      exact s56
    · rw [keep_read (x := s.sp.toNat - 80) (k := 8) hwrt hfr3' (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega), hmS2]
      repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [keep_read (x := s.sp.toNat - 64) (k := 8) hwrt hfr3' (by omega) (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega), hmS2]
      rw [Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [hg2'] at hinv3; exact hinv3
  intro s3 hpc3 ⟨junk3, fl3, vr3, m', ex3, ep3, hs3, hfr3, hlf3, hinv3, hz⟩
  subst hs3
  clear hpc3 hz
  simp only [calleeStack, hsp144] at hfr3
  obtain ⟨hSl', hF', hLF', hda, har, e88, e64, e80, hinv'⟩ := post _ m' (by simp [setReg, hx0', hx1', Nat.shiftLeft_eq]; omega)
    (by have := hsh3 (n.toNat - cap0) (by omega); simpa [setReg] using this) rfl
    (by simp [setReg, hg]) hfr3 hlf3 hinv3
  have hcrange : capN ≤ B := by rw [hcn]; exact hcapB cap0 hcap0 hcn'
  have hcpos : 0 < capN := by have := le_growCap8 n.toNat cap0; omega
  have hrs3 : ∀ r ∈ rsOf d newp capN, r ∈ L2 ++ [(newp, newp + 8 * capN)] := by
    intro r hr
    simp only [rsOf, if_neg (show capN ≠ 0 by omega), List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_append_left _ hdL
    · exact List.mem_append_right _ (List.mem_singleton_self _)
  have hrsrt3 : ∀ x ∈ rsOf d newp capN, InRanges x.1 (x.2 - x.1) R.rt := by
    intro x hx
    simp only [rsOf, if_neg (show capN ≠ 0 by omega), List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact hdrt.sub (by simp only; omega) (by simp only; omega)
    · exact hnrt.sub (by simp only; omega) (by simp only; omega)
  have hdisj : Disjoint d 24 newp (8 * capN) := by
    have := hnap _ hdL
    simp only [Apart] at this
    simp only [Janus.Spec.Disjoint]; omega
  have hn64 : n.toNat < 2 ^ 64 := by omega
  exact afterClr W0 _ m' d capN newp cap0 b3 (L2 ++ [(newp, newp + 8 * capN)]) ex (by simp [retStateX, setReg]) rfl rfl
    (by simp [retStateX, callRegs_apply, setReg, hg]) (by first | simp [retStateX, callRegs_apply, setReg, hx18] | simp [retStateX, callRegs_apply] | rfl) e88 e64 e80 hSl' hF' hLF'
    hdrt hLd ⟨hd0, hd8, hd48, hcrange, hB40, hn8, hn48, hdisj⟩ hda har hrs3
    (List.mem_append_left _ hdL) (fun r hr => List.mem_append_left _ (hLsub r hr)) hrsrt3
    hL2'W hinv' hdrop hfresh hb3 hcap0 (by rw [hcn]; simp [Nat.not_le.2 hcn'])

/-! ## The closure stores of the join -/

set_option maxRecDepth 40000 in
/-- Frames of calls from the function's frame (`sp - 144`) fit in its window `[sp - 4288, sp + 24)`. -/
theorem sub_call {rt : List (Nat × Nat)} {sp k : Nat} (hb : 4288 ≤ sp) (hk : k ≤ 5) :
    ∀ a n, Outside a n (rt ++ [(sp - 4288, sp + 24)]) →
      Outside a n [(sp - 4288, sp + 24)] ∧
      Outside a n (rt ++ [(sp - 144 - 4096, sp - 144 - 8), (sp - 144 + 8, sp - 144 + 8 + 8 * k)]) := by
  intro a n h
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h2, h1, ?_, ?_⟩ <;> omega

/-- The live set after the stack is grown: the old array stays (the collector frees it), the header
and the new array go back to the pool. -/
theorem dropAll_grow {L A : List (Nat × Nat)} {H N : Nat × Nat} (hL : ∀ r ∈ L, r ≠ H ∧ r ≠ N)
    (hA : ∀ r ∈ A, r ≠ H ∧ r ≠ N) :
    Pool.dropAll ((L ++ H :: A) ++ [N]) [H, N] = L ++ A := by
  have key : ∀ X : List (Nat × Nat), (∀ r ∈ X, r ≠ H ∧ r ≠ N) →
      X.filter (fun r => !([H, N].contains r)) = X := by
    intro X hX
    rw [List.filter_eq_self]; intro r hr
    have := hX r hr
    simp [this.1, this.2]
  unfold Pool.dropAll
  simp only [List.filter_append, List.filter_cons, key L hL, key A hA]
  simp


theorem sub_toInt (a c : Nat) (ha : a < 2 ^ 40) (hc : c < 2 ^ 40) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c).toInt = (a : Int) - (c : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]
  split <;> omega

theorem testbit63 (x : Nat) (h : x < 2 ^ 40) : ¬((BitVec.ofNat 64 x).getLsbD 63 == true) = true := by
  have : x.testBit 63 = false := Nat.testBit_lt_two_pow (by omega)
  simp only [BitVec.getLsbD_ofNat, this]
  simp

/-- The closure `{StackGrow.deferwrap1, &stackPool, *stack, s}` at `sp0 - 48`, the pointer to it at
`sp0 - 16` and the "defer armed" byte (`StackGrow+0x70 … 0x98`). -/
def stores1 (m : Memory) (sp d : Nat) : Memory :=
  (((((m.writeLE (sp - 48) 8 603664).writeLE (sp - 40) 8 1547840).writeLE (sp - 32) 8 685248).writeLE
    (sp - 24) 8 d).writeLE (sp - 16) 8 (sp - 48)).writeLE (sp - 89) 1 1

/-- ... and the spills before the `growslice` call: `s`, `oldCap`, `num` (`StackGrow+0xb8 … 0xcc`). -/
def stores2 (m : Memory) (sp d c n : Nat) : Memory :=
  (((stores1 m sp d).writeLE (sp - 56) 8 d).writeLE (sp - 80) 8 c).writeLE (sp - 72) 8
    (18446744073709551616 - c + n)

theorem stores1_frame (m : Memory) (sp d : Nat) (hb : 4288 ≤ sp) :
    MemFrame m (stores1 m sp d) [(sp - 4288, sp + 24)] := by
  unfold stores1; janus_frame

theorem stores2_frame (m : Memory) (sp d c n : Nat) (hb : 4288 ≤ sp) :
    MemFrame m (stores2 m sp d c n) [(sp - 4288, sp + 24)] := by
  unfold stores2 stores1; janus_frame

theorem stores1_slots {m : Memory} {sp d n ret fp : Nat} (hsp : 152 ≤ sp) (hsp48 : sp < 2 ^ 48) (hd : d < 2 ^ 48)
    (h0 : m.readLE (sp - 144) 8 = ret % 2 ^ 64) (h1 : m.readLE (sp - 152) 8 = fp)
    (h2 : m.readLE (sp + 8) 8 = n) :
    Slots sp 603664 1547840 685248 d n ret fp (stores1 m sp d) := by
  unfold stores1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    exact h2
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    exact h0
  · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
    exact h1

theorem stores2_slots {m : Memory} {sp d c n nn ret fp : Nat}
    (h : Slots sp 603664 1547840 685248 d nn ret fp (stores1 m sp d)) (hsp : 152 ≤ sp) :
    Slots sp 603664 1547840 685248 d nn ret fp (stores2 m sp d c n) := by
  unfold stores2
  exact ((h.of_write _ _ _ (fun x hx => by omega)).of_write _ _ _ (fun x hx => by omega)).of_write _ _ _
    (fun x hx => by omega)

/-! ## The join: the pooled (or new) stack in hand -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem tail0 {impl : List Segment} {R : RtInv} {B : Nat} {n : BitVec 64} {L : List (Nat × Nat)}
    {bud ret : Nat} {s : State} (W : World impl R B n L bud ret s)
    (S : State) (m : Memory) (d b2 : Nat) (rs : List (Nat × Nat))
    (hpc : S.pc = 603336#64) (hmem : S.mem = m) (hsp : S.sp = s.sp - 144#64) (hg : S.regs 28 = s.regs 28)
    (hx18 : S.regs 18 = s.regs 18) (hx1 : (S.regs 1).toNat = d) (hx2 : S.regs 2 = 685248#64)
    (hS0 : m.readLE (s.sp.toNat - 144) 8 = ret % 2 ^ 64 ∧ m.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat ∧
      m.readLE (s.sp.toNat + 8) 8 = n.toNat)
    (hF : MemFrame s.mem m (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]))
    (hLF : LiveFrame s.mem m L [])
    (hdrt : InRanges d 24 R.rt)
    (hSh : SliceObj B m d rs) (hfreshrs : FreshFrom rs L)
    (hrsrt : ∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt)
    (hL2W : LiveSep (L ++ rs) [(s.sp.toNat - 4288, s.sp.toNat + 24)])
    (hinv : R.inv b2 (L ++ rs) (s.regs 28).toNat (view R.rt (L ++ rs) m))
    (hb2 : b2 ≤ bud) (hb2' : bud ≤ b2 + 24) :
    Goal W S := by
  have W0 := W
  unfold Goal
  obtain ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hret, hlr, hg1, hg2, hg3, hal, hb4, ha4, hw4, hgo, hwrt,
    hwL, hrt0, hpin, hsin, hsL, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hu64v, hu64acc, hu64W, hfl, hinv0, hn40,
    hbud, hcapB, hB40⟩ := W
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  janus_eval_nat hW : wrapAddr
  janus_eval_nat hU : u64Type
  rw [hP] at hokP
  have hrsE := hSh
  obtain ⟨hd0, hd8, hd48, hdacc24, hlc, hcB, hB, hp8, hp48, harr, hdisj, hrsE⟩ := hSh
  obtain ⟨cap0, hcap0e⟩ : ∃ c, c = m.readLE (d + 16) 8 := ⟨_, rfl⟩
  obtain ⟨ptr0, hptr0e⟩ : ∃ c, c = m.readLE d 8 := ⟨_, rfl⟩
  obtain ⟨len0, hlen0e⟩ : ∃ c, c = m.readLE (d + 8) 8 := ⟨_, rfl⟩
  simp only [← hcap0e, ← hptr0e, ← hlen0e] at hrsE harr hdisj hp8 hp48 hcB hlc
  subst hrsE
  have hdW := InRanges.disjoint hdrt (hwrt _ (List.mem_singleton_self _))
  simp only at hdW
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  subst hmem
  have hdaccf : S.mem.accessible d 8 false = true :=
    Memory.accessible_sub _ hdacc24 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hdaccf2 : S.mem.accessible (d + 16) 8 false = true :=
    Memory.accessible_sub _ hdacc24 (Or.inl rfl) (by omega) (by omega)
  have hdaccx : S.mem.accessible d 1 false = true :=
    Memory.accessible_sub _ hdacc24 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hn64 : n.toNat < 2 ^ 64 := by omega
  have hx1' : S.regs 1 = BitVec.ofNat 64 d := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := (S.regs 1).isLt; omega)
  have hwS : S.mem.accessible (s.sp.toNat - 4288) (4288 + 24) true = true := by
    rw [hF.accessible]; exact hw4
  -- the freshness of the stack's ranges
  have hfr' : FreshFrom (rsOf d ptr0 cap0) L := hfreshrs
  have hdA : ApartAll d 24 L := by
    have := hfr' (d, d + 24) (List.mem_cons_self ..)
    simpa only [Nat.add_sub_cancel_left] using this
  have hLd : LiveSep L [(d, d + 24)] := fun r hr => by
    have := hdA r hr
    simp only [Apart] at this
    simp only [outside_cons, outside_nil, and_true]
    omega
  have hLnot : ∀ r ∈ L, r ∉ rsOf d ptr0 cap0 := by
    intro r hr hm
    simp only [rsOf, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact notMem_of_apartAll (by omega) hdA hr
    · by_cases hc : cap0 = 0
      · simp [hc] at hm
      · simp only [hc, if_false, List.mem_singleton] at hm
        subst hm
        have := hfr' (ptr0, ptr0 + 8 * cap0) (by simp [rsOf, hc])
        simp only [Nat.add_sub_cancel_left] at this
        exact notMem_of_apartAll (by omega) this hr
  have hpack := Hid.mk (And.intro hF (And.intro hLF (And.intro hrsrt (And.intro hL2W (And.intro hinv (And.intro hb2 (And.intro hb2' (And.intro hdrt (And.intro hdacc24 (And.intro hS0 (And.intro hdisj (And.intro harr (And.intro hfreshrs (And.intro hLd (And.intro hLnot hlen0e)))))))))))))))
  have hpack2 := Hid.mk (And.intro hget (And.intro hput (And.intro hnew (And.intro hgrow (And.intro hclr (And.intro hwb (And.intro hRty (And.intro hokG (And.intro hokP (And.intro hokN (And.intro hokGr (And.intro hokClr (And.intro hokWb (And.intro hu64v (And.intro hu64acc (And.intro hu64W (And.intro hfl (And.intro hfacc hu64))))))))))))))))))
  clear hF hLF hrsrt hL2W hinv hb2 hb2' hdrt hdacc24 hS0 hdisj harr hfreshrs hLd hLnot hlen0e hfr' hdA
  clear hget hput hnew hgrow hclr hwb hRty hokG hokP hokN hokGr hokClr hokWb hu64v hu64acc hu64W hfl hfacc hu64 hinv0 hsin hsL hpin hnew0
  janus_run [hwS, hdaccf, hdaccx, hdaccf2, hsp, hg, hx1', hx2] until [603528, Extracted.program.contractAddr "runtime.growslice", Extracted.program.contractAddr "runtime.memclrNoHeapPointers"]
  · -- `n < 0`: impossible
    obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, -, hn0⟩, -, -, -, -, -, -⟩ := hpack.get
    exfalso
    rw [hn0] at hbr
    exact testbit63 _ (by omega) hbr
  · -- `n ≤ cap`: no growth
    obtain ⟨hF, hLF, hrsrt, hL2W, hinv, hb2, hb2', hdrt, hdacc24, ⟨hS0a, hS0b, hn0⟩, hdisj, harr, hfreshrs, hLd, hLnot, -⟩ :=
      hpack.get
    rw [hn0, ← hcap0e, sub_toInt _ _ (by omega) (by omega)] at hbr
    have hnc : n.toNat ≤ cap0 := by omega
    simp only [← hcap0e, ← hptr0e, hn0]
    have hm1 := stores1_frame S.mem s.sp.toNat d (by omega)
    have hdL : (d, d + 24) ∈ L ++ rsOf d ptr0 cap0 := List.mem_append_right _ (List.mem_cons_self ..)
    exact tail1 W0 _ (stores1 S.mem s.sp.toNat d) d cap0 ptr0 cap0 b2 (L ++ rsOf d ptr0 cap0) [] rfl rfl rfl
      (by simp [setReg, hg])
      (by simp [setReg, hx18]) (by simp [setReg, hx1]) (by simp [setReg]; omega) (by simp [setReg]; omega)
      (stores1_slots (by omega) (by omega) (by omega) hS0a hS0b hn0)
      (MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hF
        (rs' := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hm1 (by frame_sub))
      (LiveFrame.trans hLF (LiveFrame.of_win hm1 hwL) (fun _ _ h => h)) hdrt hLd
      ⟨hd0, hd8, hd48, hcB, hB, hp8, hp48, hdisj⟩ (by rw [hm1.accessible]; exact hdacc24)
      (fun h => by rw [hm1.accessible]; exact harr h) (fun r hr => List.mem_append_right _ hr) hdL
      (fun r hr => List.mem_append_left _ hr) hrsrt hL2W
      (RtInv.inv_frame hm1 hwrt hinv) (by rw [dropAll_append_self hLnot, List.append_nil]) (by simp [FreshFrom]) hb2 hcB
      (by simp [hnc])
  · -- `cap < n`: `growslice`
    obtain ⟨hF, hLF, hrsrt, hL2W, hinv, hb2, hb2', hdrt, hdacc24, ⟨hS0a, hS0b, hn0⟩, hdisj, harr, hfreshrs, hLd, hLnot, -⟩ :=
      hpack.get
    obtain ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hokG, hokP, hokN, hokGr, hokClr, hokWb, hu64v, hu64acc, hu64W,
      hfl, hfacc, hu64⟩ := hpack2.get
    rw [hn0, ← hcap0e] at hbr
    simp only [← hcap0e, ← hptr0e, hn0]
    rw [hU] at hokGr hu64v hu64acc hu64W hu64
    have hm2 := stores2_frame S.mem s.sp.toNat d cap0 n.toNat (by omega)
    have hbc := hbud cap0 hcB hbr
    have hcapB' := hcapB cap0 hcB hbr
    have hdL : (d, d + 24) ∈ L ++ rsOf d ptr0 cap0 := List.mem_append_right _ (List.mem_cons_self ..)
    have hSl2 := stores2_slots (c := cap0) (n := n.toNat) (stores1_slots (m := S.mem) (sp := s.sp.toNat) (d := d)
      (n := n.toNat) (ret := ret) (fp := (s.regs 29).toNat) (by omega) (by omega) (by omega) hS0a hS0b hn0) (by omega)
    have hF2 : MemFrame s.mem (stores2 S.mem s.sp.toNat d cap0 n.toNat)
        (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) :=
      MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hF
        (rs' := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hm2 (by frame_sub)
    have hLF2 : LiveFrame s.mem (stores2 S.mem s.sp.toNat d cap0 n.toNat) L [] :=
      LiveFrame.trans hLF (LiveFrame.of_win hm2 hwL) (fun _ _ h => h)
    have hLW : LiveSep L [(s.sp.toNat - 4288, s.sp.toNat + 24)] := hwL
    have hnn : cap0 < 2 ^ 40 := by omega
    -- the facts about the call state `S3`
    have key : ∀ S3 : State, S3.mem = stores2 S.mem s.sp.toNat d cap0 n.toNat → S3.regs 28 = s.regs 28 →
        S3.sp.toNat + 144 = s.sp.toNat → (S3.regs 30).toNat % 4 = 0 → (S3.regs 30).toNat < 2 ^ 48 →
        (S3.regs 0).toNat = ptr0 → (S3.regs 1).toNat = n.toNat → (S3.regs 2).toNat = cap0 →
        (S3.regs 3).toNat = n.toNat - cap0 → (S3.regs 4).toNat = 701312 →
        GrowslicePre 4096 S3 ∧ StackRoom S3 4096 5 ∧
          LiveAt R (Extracted.program.contractAddr "runtime.growslice") (growsliceArgs S3) (L ++ rsOf d ptr0 cap0) b2
            (growsliceRound S3) (S3.regs 28).toNat S3.mem (calleeStack S3 4096 5) := by
      intro S3 hm3 hg3' hsp3 h30a h30b hr0 hr1 hr2 hr3 hr4
      have hmm : MemFrame S.mem S3.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by rw [hm3]; exact hm2
      have hF3 : MemFrame s.mem S3.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) := by rw [hm3]; exact hF2
      have hargs : growsliceArgs S3 = [ptr0, n.toNat, cap0, n.toNat - cap0, 701312] := by
        simp only [growsliceArgs, hr0, hr1, hr2, hr3, hr4]
      have hround : growsliceRound S3 = 8 * growCap8 n.toNat cap0 := by
        simp only [growsliceRound, hr1, hr2]
      have h := call_pre R (L ++ rsOf d ptr0 cap0) b2 (growsliceRound S3)
        (Extracted.program.contractAddr "runtime.growslice") (growsliceArgs S3)
        (s := s) (S := S3) (lo := s.sp.toNat - 4288) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 5) (fr := 144)
        hg1 hg2 (by omega) hgo hF3 hg3' hsp3 (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
        (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hL2W
        (by rw [hargs, ← hU]; exact hokGr ptr0 cap0 hcB hbr) (by rw [hg3']; exact RtInv.inv_frame hmm hwrt hinv)
        (by rw [hround]; omega)
      have hu64o : Outside 701312 16 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) := by
        simp only [outside_append]
        exact ⟨hu64, hu64W⟩
      refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, h.2.1, h.2.2⟩
      · rw [hr4, hF3.accessible]; exact hu64acc
      · simp only [typSize, hr4]
        rw [hF3.readLE _ _ (Outside.of_sub hu64o (Nat.le_refl _) (by omega))]; exact hu64v.1
      · simp only [typPtrBytes, hr4]
        rw [hF3.readLE _ _ (Outside.of_sub hu64o (by omega) (by omega))]; exact hu64v.2
      · omega
      · omega
      · omega
      · omega
      · intro hpos
        have hc0 : 0 < cap0 := by omega
        have e : n.toNat - (n.toNat - cap0) = cap0 := by omega
        refine ⟨?_, ?_⟩
        · rw [hr0, hr1, hr3, e]; omega
        · rw [hr0, hr1, hr3, e, hmm.accessible]
          exact Memory.accessible_sub _ (harr hc0) (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
    have post : ∀ (S3 : State) (ptr : W64) (junk : Nat → W64) (f3 : Flags) (v3 : Nat → BitVec 128) (m3 : Memory)
        (ex3 : Option (Nat × Nat)) (ep3 : Nat → Bool),
        S3.mem = stores2 S.mem s.sp.toNat d cap0 n.toNat → S3.sp = s.sp - 144#64 → S3.regs 28 = s.regs 28 →
        S3.regs 18 = s.regs 18 → S3.regs 30 = 603468#64 → (S3.regs 0).toNat = ptr0 → (S3.regs 1).toNat = n.toNat →
        (S3.regs 2).toNat = cap0 → (S3.regs 3).toNat = n.toNat - cap0 →
        MemFrame S3.mem m3 (R.rt ++ calleeStack S3 4096 5) → LiveFrame S3.mem m3 (L ++ rsOf d ptr0 cap0) [] →
        (growsliceObj R.rt S3 m3 ptr.toNat ∧ ApartAll ptr.toNat (growsliceRound S3) (L ++ rsOf d ptr0 cap0)) →
        ApartAll ptr.toNat (growsliceRound S3) (calleeStack S3 4096 5) →
        R.inv (b2 - growsliceRound S3) ((L ++ rsOf d ptr0 cap0) ++ [(ptr.toNat, ptr.toNat + growsliceRound S3)])
          (S3.regs 28).toNat
          (view R.rt ((L ++ rsOf d ptr0 cap0) ++ [(ptr.toNat, ptr.toNat + growsliceRound S3)]) m3) →
        Goal W0 (retStateX S3 junk
          [ptr, S3.regs 1, BitVec.ofNat 64 (growCap8 (S3.regs 1).toNat (S3.regs 2).toNat)] f3 v3 m3 ex3 ep3) := by
      intro S3 ptr junk f3 v3 m3 ex3 ep3 hm3 hsp3 hg3' h18 hr30 hr0 hr1 hr2 hr3 hfr3 hlf3 ⟨hobj, hapL⟩ hapS hinv3
      have hround : growsliceRound S3 = 8 * growCap8 n.toNat cap0 := by simp only [growsliceRound, hr1, hr2]
      have hsp3n : S3.sp.toNat = s.sp.toNat - 144 := by rw [hsp3]; exact hsp144
      rw [hround] at hapL hapS hinv3
      simp only [growsliceObj, Fresh, hr0, hr1, hr2, hr3] at hobj
      obtain ⟨⟨hnrt, hn48, hnacc, hal8, -, -, -⟩, -, -⟩ := hobj
      have hcpos : 0 < growCap8 n.toNat cap0 := by have := le_growCap8 n.toNat cap0; omega
      have hn8 : ptr.toNat % 8 = 0 := hal8 (Or.inr (by omega))
      have hmm : MemFrame S.mem S3.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by rw [hm3]; exact hm2
      have hSlS3 : Slots s.sp.toNat 603664 1547840 685248 d n.toNat ret (s.regs 29).toNat S3.mem := by
        rw [hm3]; exact hSl2
      have hF3 : MemFrame s.mem S3.mem (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) := by rw [hm3]; exact hF2
      have hLF3 : LiveFrame s.mem S3.mem L [] := by rw [hm3]; exact hLF2
      simp only [calleeStack, hsp3n] at hfr3 hapS
      have hfrc := hfr3
      have hcrange : growCap8 n.toNat cap0 ≤ B := hcapB'
      have hLH : ∀ r ∈ L, r ≠ (d, d + 24) ∧ r ≠ (ptr.toNat, ptr.toNat + 8 * growCap8 n.toNat cap0) := by
        intro r hr
        refine ⟨fun h => hLnot r hr (h ▸ List.mem_cons_self ..), fun h => ?_⟩
        subst h
        exact notMem_of_apartAll (by omega) ((apartAll_append _ _ _ _).mp hapL).1 hr
      have hAH : ∀ r ∈ (if cap0 = 0 then [] else [(ptr0, ptr0 + 8 * cap0)]),
          r ≠ (d, d + 24) ∧ r ≠ (ptr.toNat, ptr.toNat + 8 * growCap8 n.toNat cap0) := by
        intro r hr
        refine ⟨fun h => ?_, fun h => ?_⟩
        · by_cases hc : cap0 = 0
          · simp [hc] at hr
          · simp only [hc, if_false, List.mem_singleton] at hr
            subst hr
            simp only [Prod.mk.injEq] at h
            simp only [Janus.Spec.Disjoint] at hdisj
            omega
        · subst h
          exact notMem_of_apartAll (by omega) hapL (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      have hrs3 : rsOf d ptr.toNat (growCap8 n.toNat cap0) =
          [(d, d + 24), (ptr.toNat, ptr.toNat + 8 * growCap8 n.toNat cap0)] := by
        simp [rsOf] <;> omega
      have hdisj3 : Disjoint d 24 ptr.toNat (8 * growCap8 n.toNat cap0) := by
        have := hapL (d, d + 24) hdL
        simp only [Apart] at this
        simp only [Janus.Spec.Disjoint]; omega
      have hS72 : m3.readLE (s.sp.toNat - 72) 8 = n.toNat - cap0 := by
        rw [keep_read (x := s.sp.toNat - 72) (k := 8) hwrt hfrc (by omega) (by omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega), hm3]
        unfold stores2
        rw [Memory.readLE_writeLE_self]; omega
      have hS64 : m3.readLE (s.sp.toNat - 80) 8 = cap0 := by
        rw [keep_read (x := s.sp.toNat - 80) (k := 8) hwrt hfrc (by omega) (by omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega), hm3]
        unfold stores2
        rw [Memory.readLE_writeLE_of_disjoint (h := by omega), Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      have hS56 : m3.readLE (s.sp.toNat - 56) 8 = d := by
        rw [keep_read (x := s.sp.toNat - 56) (k := 8) hwrt hfrc (by omega) (by omega)
          (by simp only [outside_cons, outside_nil, and_true]; omega), hm3]
        unfold stores2
        repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
        rw [Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      exact afterGrow W0 _ m3 d (growCap8 n.toNat cap0) ptr.toNat cap0 (b2 - 8 * growCap8 n.toNat cap0)
        (L ++ rsOf d ptr0 cap0) (if cap0 = 0 then [] else [(ptr0, ptr0 + 8 * cap0)])
        (by simp [retStateX, hr30]) rfl (by simp [retStateX, hsp3])
        (by simp [retStateX, callRegs_apply, hg3']) (by simp [retStateX, callRegs_apply, h18])
        (by simp [retStateX, callRegs_apply] <;> omega) (by simp [retStateX, callRegs_apply, hr1])
        (by simp [retStateX, callRegs_apply, hr1, hr2] <;> omega) rfl hbr hcB hS72 hS64 hS56
        (Slots.step (spc := s.sp.toNat - 144) (k := 5) hwrt hb4 (by omega) (Or.inl rfl) (by omega) hSlS3 hfrc)
        (MemFrame.trans (rs := R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) hF3
          (rs' := R.rt ++ [(s.sp.toNat - 144 - 4096, s.sp.toNat - 144 - 8),
            (s.sp.toNat - 144 + 8, s.sp.toNat - 144 + 8 + 8 * 5)]) hfrc (by frame_sub))
        (LiveFrame.trans hLF3 (LiveFrame.of_sep hlf3 (fun r hr => trivial) (fun r hr => List.mem_append_left _ hr))
          (fun _ _ h => h))
        hdrt hLd (by rw [hfr3.accessible, hmm.accessible]; exact hdacc24) hd0 hd8 hd48 hdL
        (fun r hr => List.mem_append_left _ hr) hL2W
        (by rw [hrs3]; exact dropAll_grow hLH hAH) (fun r hr => hfreshrs r (List.mem_cons_of_mem _ hr))
        (by omega) hnrt hn48 hnacc hn8 hapL (by rw [hg3'] at hinv3; exact hinv3)
    refine Reaches.call (Summary.withExit (hgrow (L ++ rsOf d ptr0 cap0) b2) hret) (by rfl) ?_ ?_
    · exact key _ rfl (by simp [setReg, hg]) (by simp [hsp144] <;> omega) (by simp [setReg]) (by simp [setReg])
        (by simp [setReg] <;> omega) (by simp [setReg, hn0] <;> omega) (by simp [setReg] <;> omega)
        (by simp [setReg] <;> omega) (by simp [setReg])
    · intro s3 hpc3 ⟨ptr, junk, f3, v3, m3, ex3, ep3, hs3, hfr3, hlf3, hobj, hapS, hinv3⟩
      subst hs3
      exact post _ ptr junk f3 v3 m3 ex3 ep3 rfl rfl (by simp [setReg, hg]) (by simp [setReg, hx18]) (by simp [setReg])
        (by simp [setReg] <;> omega) (by simp [setReg] <;> omega) (by simp [setReg] <;> omega) (by simp [setReg] <;> omega)
        hfr3 hlf3 hobj hapS hinv3
  · -- `n ≤ cap` and `cap < n`: impossible
    obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, -, hn0⟩, -, -, -, -, -, -⟩ := hpack.get
    exfalso
    rename_i hbA hbB
    rw [hn0, ← hcap0e, sub_toInt _ _ (by omega) (by omega)] at hbB
    omega

/-! ## The theorem -/

theorem sub_call' {rt : List (Nat × Nat)} {sp : Nat} (hb : 4288 ≤ sp) :
    ∀ a n, Outside a n (rt ++ [(sp - 4288, sp + 24)]) →
      Outside a n (rt ++ [(sp - 4288, sp + 24)]) ∧
      Outside a n (rt ++ [(sp - 144 - 4096, sp - 144 - 8), (sp - 144 + 8, sp - 144 + 8 + 8 * 1)]) :=
  fun a n h => ⟨h, (sub_call (k := 1) hb (by omega) a n h).2⟩


theorem sliceObj_zero {B p : Nat} {m : Memory} (hB : B < 2 ^ 40) (h0 : 0 < p) (h8 : p % 8 = 0)
    (h48 : p + 24 ≤ 2 ^ 48) (hacc : m.accessible p 24 true = true) (hz : ZeroBytes m p 24) :
    SliceObj B m p [(p, p + 24)] := by
  have e0 : m.readLE p 8 = 0 := hz.readLE (k := 0) (j := 8) (by omega)
  have e1 : m.readLE (p + 8) 8 = 0 := hz.readLE (k := 8) (j := 8) (by omega)
  have e2 : m.readLE (p + 16) 8 = 0 := hz.readLE (k := 16) (j := 8) (by omega)
  unfold SliceObj
  rw [e0, e1, e2]
  refine ⟨h0, h8, h48, hacc, Nat.le_refl _, Nat.zero_le _, hB, by omega, by omega, fun h => absurd h (by omega), ?_, by simp⟩
  simp only [Janus.Spec.Disjoint]; omega


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
theorem correctness (impl : List Segment) (R : RtInv) (B : Nat) (hB40 : B < 2 ^ 40)
    (hget : PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get")
      4096 R ptrType (SliceObj B))
    (hput : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
      4096 R ptrType (SliceObj B))
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hgrow : GrowsliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hfl : ∀ b L g v, R.inv b L g v → Outside wbFlag 4 L)
    (n : BitVec 64) (L : List (Nat × Nat)) (bud : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => GuardOK s 4288 ∧ StackOK s 4288 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4288, s.sp.toNat + 24) :: R.rt) ∧
        LiveSep [(s.sp.toNat - 4288, s.sp.toNat + 24)] R.rt ∧
        LiveSep L [(s.sp.toNat - 4288, s.sp.toNat + 24)] ∧
        (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s.sp.toNat - 4288 ∨ s.sp.toNat + 24 ≤ poolAddr) ∧
        Outside stkType 16 R.rt ∧
        Outside u64Type 16 R.rt ∧ s.mem.accessible wbFlag 4 false = true ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [stkType] ∧
        (∀ p c, c ≤ B → c < n.toNat →
          R.ok (Extracted.program.contractAddr "runtime.growslice") [p, n.toNat, c, n.toNat - c, u64Type]) ∧
        (∀ q c, c ≤ B → c < n.toNat →
          R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [q + 8 * c, 8 * (n.toNat - c)]) ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
        R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ n.toNat < 2 ^ 40 ∧ 24 ≤ bud ∧
        (∀ c, c ≤ B → c < n.toNat → 24 + 8 * growCap8 n.toNat c ≤ bud) ∧
        (∀ c, c ≤ B → c < n.toNat → growCap8 n.toNat c ≤ B))
      (fun s s' => Post R B n L bud s s') := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64,
    hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hinv, hn40, hb24, hbud, hcapB⟩
  janus_intro hs
  janus_data hd [hw4]
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  janus_eval_nat hSt : stkType
  janus_eval_nat hU : u64Type
  have hRty : s.mem.readLE stkType 8 = 24 ∧ s.mem.readLE (stkType + 8) 8 = 8 := by
    rw [hSt]
    exact ⟨by rw [h_rodata 738112 8 (by decide +kernel)]; decide +kernel,
      by rw [h_rodata (738112 + 8) 8 (by decide +kernel)]; decide +kernel⟩
  have hsL : Outside stkType 16 [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
    rw [hSt]; simp only [outside_cons, outside_nil, and_true]; omega
  have hu64v : s.mem.readLE u64Type 8 = 8 ∧ s.mem.readLE (u64Type + 8) 8 = 0 := by
    rw [hU]
    exact ⟨by rw [h_rodata 701312 8 (by decide +kernel)]; decide +kernel,
      by rw [h_rodata (701312 + 8) 8 (by decide +kernel)]; decide +kernel⟩
  have hu64acc : s.mem.accessible u64Type 16 false = true := by
    rw [hU]; exact Memory.accessible_sub _ h_data2 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hu64W : Outside u64Type 16 [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
    rw [hU]; simp only [outside_cons, outside_nil, and_true]; omega
  have W : World impl R B n L bud ret s :=
    ⟨hget, hput, hnew, hgrow, hclr, hwb, hRty, hret, h_lr, hg1, hg2, hg3, hal, hb4, ha4, hw4, hgo, hwrt, hwL, hrt0,
      hpin, hsin, hsL, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb, hnew0, hu64v, hu64acc, hu64W, hfl,
      hinv, hn40, hbud, hcapB, hB40⟩
  have W0 := W
  have hsp144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  rw [hP] at hpin hokG hokP hnew0
  have hstkacc : s.mem.accessible stkType 16 false = true := by
    rw [hSt]; exact Memory.accessible_sub _ h_data3 (Or.inl rfl) (Nat.le_refl _) (by omega)
  clear h_rodata h_data0 h_data1 h_data2 h_data3 h_data4 h_ddisj0_0 h_ddisj0_1 h_ddisj0_2 h_ddisj0_3 h_ddisj0_4
  have hpw := hpin
  have hgo' := hgo
  simp only [outside_cons, outside_nil, and_true] at hgo'
  have key1 : ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4288, s.sp.toNat + 24)] →
      S.regs 28 = s.regs 28 → S.sp.toNat + 144 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 →
      (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = 1547840 →
      CallOK S 4096 1 ∧ StackRoom S 4096 1 ∧ S.mem.readLE (1547840 + newOffset) 8 = 0 ∧
      LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L bud 0
        (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
    intro S hf hg hsp h30a h30b h0
    have h := call_pre R L bud 0 (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat]
      (s := s) (S := S) (lo := s.sp.toNat - 4288) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 1) (fr := 144)
      hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega)
      (by omega) ha4
      (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
      (by rw [h0]; exact hokG) (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    rw [hf.readLE _ _ (by simp only [newOffset, outside_cons, outside_nil, and_true]; omega)]
    exact hnew0
  janus_run until [Extracted.program.contractAddr "sync.(*Pool).Get"]
  refine Reaches.call (Summary.withExit (hget L bud) hret) rfl
    (key1 _ (by janus_frame) (by simp [setReg]) (by simp [hsp144]; omega) (by simp [setReg])
      (by simp [setReg]) (by simp [setReg])) ?_
  intro s1 hpc1 ⟨r, vr, fl, m1, ex1, ep1, hs1, hfr1, hlf1, hns1, hcase⟩
  subst hs1
  simp only [calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, hsp144] at hfr1 hlf1 hns1 hcase
  have hF1 : MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) :=
    MemFrame.trans (rs := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) (by janus_frame) hfr1 (sub_call hb4 (by omega))
  have hLF1 : LiveFrame s.mem m1 L [] :=
    LiveFrame.trans (LiveFrame.of_win (ws := [(s.sp.toNat - 4288, s.sp.toNat + 24)]) (by janus_frame) hwL) hlf1
      (fun _ _ h => h)
  have hS01 : m1.readLE (s.sp.toNat - 144) 8 = ret % 2 ^ 64 ∧ m1.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat ∧
      m1.readLE (s.sp.toNat + 8) 8 = n.toNat := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · rw [hfr1.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack]
        exact ⟨outside_rt_of_win hwrt (by omega) (by omega), by omega, by omega⟩)]
      repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
      rw [Memory.readLE_writeLE_self]
      try first | exact Nat.mod_eq_of_lt (s.regs 29).isLt | exact Nat.mod_eq_of_lt (by omega)
  trace_state
  rcases hcase with ⟨hr0, hr1, hinvG⟩ | ⟨rs, hr0, hSh, hfresh, hinrt, hsep, hinvG⟩
  · -- nothing in the pool: a new stack
    have hr0' : r 0 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr0)
    have hr1' : r 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr1)
    have hdesc := hRty
    rw [hSt] at hdesc
    have hsin' : Outside 738112 16 R.rt := by rw [← hSt]; exact hsin
    have hsL' : Outside 738112 16 [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by rw [← hSt]; exact hsL
    have hoS : ∀ a k, 738112 ≤ a → a + k ≤ 738112 + 16 →
        Outside a k (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) := fun a k h1 h2 => by
      simp only [outside_append]
      exact ⟨Outside.of_sub hsin' h1 h2, Outside.of_sub hsL' h1 h2⟩
    have hsz : m1.readLE 738112 8 = 24 := by
      rw [hF1.readLE _ _ (hoS _ _ (Nat.le_refl _) (by omega))]; exact hdesc.1
    have hpb : m1.readLE (738112 + 8) 8 = 8 := by
      rw [hF1.readLE _ _ (hoS _ _ (by omega) (by omega))]; exact hdesc.2
    janus_run until [Extracted.program.contractAddr "runtime.newobject"]
    have key2 : ∀ S : State, S.mem = m1 → S.regs 28 = s.regs 28 → S.sp.toNat + 144 = s.sp.toNat →
        (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = 738112 →
        (NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
          LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L bud
            (newobjectRound S) (S.regs 28).toNat S.mem (calleeStack S 4096 1)) ∧
          0 < typSize S.mem (S.regs 0).toNat := by
      intro S hm hg' hsp' h30a h30b h0
      have hr : typSize S.mem (S.regs 0).toNat = 24 := by simp only [typSize, hm, h0]; exact hsz
      have hp : typPtrBytes S.mem (S.regs 0).toNat = 8 := by simp only [typPtrBytes, hm, h0]; exact hpb
      have hround : newobjectRound S = 24 := by
        simp only [newobjectRound, hr, typNoscan, hp]; decide
      have h := call_pre R L bud 24 (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat]
        (s := s) (S := S) (lo := s.sp.toNat - 4288) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 1)
        (fr := 144) hg1 hg2 (by omega) hgo (by rw [hm]; exact hF1) hg' hsp' (by omega) h30a h30b (by decide)
        (by omega) (by omega) (by omega) ha4
        (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
        (by rw [h0]; exact hokN) (by rw [hm, hg']; exact hinvG) hb24
      rw [hround]
      refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_⟩, h.2.1, h.2.2⟩, by omega⟩
      · rw [hm, h0, hF1.accessible]; exact hstkacc
      · rw [hr]; simp [maxAlloc]
    refine Reaches.call (Summary.withExit (hnew.pos L bud) hret) rfl
      (key2 _ rfl (by simp [setReg, Map.keepABI]) (by simp [hsp144]; omega) (by simp [setReg])
        (by simp [setReg]) (by simp [setReg])) ?_
    intro s2 hpc2 ⟨ptr, junk, f2, v2, m2, ex2, ep2, hs2, hfr2, hlf2, ⟨hobj, hapL⟩, hapS, hinv2⟩
    subst hs2
    simp only [retStateX, calleeStack, newobjectObj, Fresh, newobjectRound, setReg_apply, reduceIte,
      Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsp144, typSize, typNoscan,
      typPtrBytes, hsz, hpb, Map.keepABI_apply, or_true, true_or, ite_true, Nat.reduceBEq, true_implies,
      false_implies] at hfr2 hlf2 hobj hapL hapS hinv2
    have hbs : blockSize 24 false = 24 := by decide
    rw [hbs] at hobj hapL hapS hinv2
    obtain ⟨hin, hbd, hacc, hal8, -, hzero, -⟩ := hobj
    have hptr0 : 0 < BitVec.toNat ptr := by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hrt0 r hr
      omega
    have hS02 : m2.readLE (s.sp.toNat - 144) 8 = ret % 2 ^ 64 ∧
        m2.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat ∧ m2.readLE (s.sp.toNat + 8) 8 = n.toNat := by
      obtain ⟨a1, a2, a3⟩ := hS01
      refine ⟨?_, ?_, ?_⟩ <;>
      · rw [hfr2.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨outside_rt_of_win hwrt (by omega) (by omega), by omega, by omega⟩)]
        first | exact a1 | exact a2 | exact a3
    have hF2 : MemFrame s.mem m2 (R.rt ++ [(s.sp.toNat - 4288, s.sp.toNat + 24)]) :=
      MemFrame.trans hF1 hfr2 (sub_call' hb4)
    have hLF2 : LiveFrame s.mem m2 L [] := LiveFrame.trans hLF1 hlf2 (fun _ _ h => h)
    have hpd := InRanges.disjoint hin (hwrt _ (List.mem_singleton_self _))
    simp only at hpd
    have hSh2 : SliceObj B m2 ptr.toNat [(ptr.toNat, ptr.toNat + 24)] :=
      sliceObj_zero hB40 hptr0 hal8 (by omega) (Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega))
        hzero
    have hrsrt : ∀ x ∈ [(ptr.toNat, ptr.toNat + 24)], InRanges x.1 (x.2 - x.1) R.rt := by
      intro x hx
      simp only [List.mem_singleton] at hx; subst hx
      simpa only [Nat.add_sub_cancel_left] using hin
    have hL2W : LiveSep (L ++ [(ptr.toNat, ptr.toNat + 24)]) [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
      rw [liveSep_append]
      refine ⟨hwL, ?_⟩
      simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true]
      omega
    have hfreshrs : FreshFrom [(ptr.toNat, ptr.toNat + 24)] L := by
      simpa [FreshFrom] using hapL
    have hpack := Hid.mk (And.intro hS02 (And.intro hF2 (And.intro hLF2 (And.intro hSh2 (And.intro hrsrt
      (And.intro hL2W (And.intro hfreshrs hinv2)))))))
    clear hpc2 hS02 hF2 hLF2 hSh2 hrsrt hL2W hfreshrs hinv2 hfr2 hlf2 hapL hapS hin hzero hacc hpd hF1 hLF1 hfr1 hlf1 hS01
    clear key1 key2 hdesc hsz hpb hinvG hns1 hgo hgo'
    janus_run until [603336]
    obtain ⟨hS02, hF2, hLF2, hSh2, hrsrt, hL2W, hfreshrs, hinv2⟩ := hpack.get
    exact tail0 W0 _ m2 ptr.toNat (bud - 24) [(ptr.toNat, ptr.toNat + 24)] (by simp [setReg]) rfl rfl
      (by simp [setReg, retStateX, callRegs_apply, Map.keepABI_apply]) (by simp [setReg, retStateX, callRegs_apply, Map.keepABI_apply])
      (by simp [setReg, retStateX, callRegs_apply]) (by simp [setReg])
      hS02 hF2 hLF2 (by simpa only [Nat.add_sub_cancel_left] using hrsrt _ (List.mem_singleton_self _)) hSh2 hfreshrs hrsrt
      hL2W hinv2 (by omega) (by omega)
  · -- a pooled stack
    have hr0' : r 0 = 685248#64 := BitVec.eq_of_toNat_eq (by simpa [hT] using hr0)
    have hd0 := hSh.1
    have hr1' : r 1 ≠ 0#64 := fun h => by simp [h] at hd0
    have hrsE := hSh.2.2.2.2.2.2.2.2.2.2.2
    have hdrt : InRanges (BitVec.toNat (r 1)) 24 R.rt := by
      have := hinrt ((BitVec.toNat (r 1)), (BitVec.toNat (r 1)) + 24) (by rw [hrsE]; exact List.mem_cons_self ..)
      simpa only [Nat.add_sub_cancel_left] using this
    have hL2W : LiveSep (L ++ rs) [(s.sp.toNat - 4288, s.sp.toNat + 24)] := by
      rw [liveSep_append]
      refine ⟨hwL, fun r hr => ?_⟩
      have := InRanges.disjoint (hinrt r hr) (hwrt _ (List.mem_singleton_self _))
      simp only at this
      simp only [outside_cons, outside_nil, and_true]
      omega
    have hpack := Hid.mk (And.intro hS01 (And.intro hF1 (And.intro hLF1 (And.intro hdrt (And.intro hSh
      (And.intro hfresh (And.intro hinrt (And.intro hL2W hinvG))))))))
    clear hpc1 hS01 hF1 hLF1 hdrt hSh hfresh hinrt hL2W hinvG hsep hns1 hfr1 hlf1 key1 hrsE hgo hgo'
    janus_run until [603336]
    obtain ⟨hS01, hF1, hLF1, hdrt, hSh, hfresh, hinrt, hL2W, hinvG⟩ := hpack.get
    exact tail0 W0 _ m1 (BitVec.toNat (r 1)) bud rs (by simp [setReg]) rfl rfl
      (by simp [setReg, retStateX, callRegs_apply, Map.keepABI_apply])
      (by simp [setReg, retStateX, callRegs_apply, Map.keepABI_apply])
      (by simp [setReg, retStateX, callRegs_apply, Map.keepABI_apply]) (by simp [setReg])
      hS01 hF1 hLF1 hdrt hSh hfresh hinrt hL2W hinvG (Nat.le_refl _) (by omega)



/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The live runtime `R` is the toy bump allocator of `Janus.Contracts.LiveToy` (`toyR`), whose
runtime-owned ranges are the heap, the bump cell, the barrier buffer and the type descriptors
`tys`: nothing else: `stack`'s descriptor and the barrier's enable word are data of the binary. Its `Get` returns nil, its `Put` drops its argument, its `newobject` and
`growslice` hand out the next bytes of the heap, its `memclrNoHeapPointers` clears the 8 bytes of
the one request and its barrier returns the buffer (code at the six contract addresses). With them
`correctness` applies to a call state of `StackGrow(1)` with an empty live set (`nonvacuous`), and
the call returns `1` with the guarantee (`returns`). -/

namespace Witness

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.PoolSat

set_option maxRecDepth 100000

def P : Nat := janus_eval% poolAddr
def sT : Nat := janus_eval% stkType
def pT : Nat := janus_eval% ptrType
def uT : Nat := janus_eval% u64Type
def wF : Nat := janus_eval% wbFlag
def cG : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Get")
def cP : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Put")
def cN : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def cGr : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def cM : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
def cW : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

theorem hP : poolAddr = P := by unfold P; decide
theorem hTy : stkType = sT := by unfold sT; decide
theorem hPT : ptrType = pT := by unfold pT; decide
theorem aG : Extracted.program.contractAddr "sync.(*Pool).Get" = cG := by decide
theorem aP : Extracted.program.contractAddr "sync.(*Pool).Put" = cP := by decide
theorem aN : Extracted.program.contractAddr "runtime.newobject" = cN := by decide
theorem hU : u64Type = uT := by unfold uT; decide
theorem hWF : wbFlag = wF := by unfold wF; decide
theorem aGr : Extracted.program.contractAddr "runtime.growslice" = cGr := by decide
theorem aM : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = cM := by decide
theorem aW : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = cW := by decide

/-- The toy runtime has no type descriptors of its own. -/
def tys : Tys := []

theorem tysOK : TysOK tys := fun t ht => absurd ht (by simp [tys])

/-- The requests it serves. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = cG ∧ args = [P]) ∨ (a = cP ∧ args = [P]) ∨ (a = cN ∧ args = [sT]) ∨
  (a = cGr ∧ ∃ q et, args = [q, 1, 0, 1, et]) ∨ (a = cM ∧ ∃ q, args = [q, 8]) ∨ (a = cW ∧ args = [2])

def R : RtInv := toyR tys ok

/-- The model code at the three contract addresses. -/
def implAt : List Segment :=
  [{ name := "model.Get", base := cG, words := getCode },
   { name := "model.Put", base := cP, words := putCode },
   { name := "model.newobject", base := cN, words := newobjectCodeD },
   { name := "model.growslice", base := cGr, words := growCode8 },
   { name := "model.memclr", base := cM, words := memclrCode },
   { name := "model.wb", base := cW, words := wbCode }]

def linked : Program := Extracted.program.link implAt

set_option maxRecDepth 20000 in
theorem hget : PoolGetLive linked cG 4096 R pT (SliceObj 1) := by
  refine poolGetLive_of_run tys ok linked cG pT (SliceObj 1) ?_
  intro s hpc h30 h30'
  change ReachesRet linked _ s _
  janus_run
  exact getFinal_eq s

set_option maxRecDepth 20000 in
theorem hput : PoolPutLive linked cP 4096 R pT (SliceObj 1) := by
  refine poolPutLive_of_run tys tysOK ok linked cP pT (SliceObj 1) ?_
  intro s hpc h30 h30'
  change ReachesRet linked _ s _
  janus_run
  rfl

set_option maxRecDepth 20000 in
theorem hnew : NewobjectLiveContract linked cN 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet linked _ s _
  janus_run
  exact finish_newobjectD tysOK pre

set_option maxRecDepth 20000 in
theorem hgrow : GrowsliceLiveContract linked cGr 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩ := pre.1
  change ReachesRet linked _ s _
  janus_run
  refine finish_growslice8 tysOK ?_ pre
  intro args h
  simp only [R, toyR, ok] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact h
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

set_option maxRecDepth 20000 in
theorem hclr : MemclrNoHeapPointersLive linked cM 4096 R := by
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  have h8 : (s.regs 1).toNat = 8 := by
    have h := hLm.1
    simp only [R, toyR, ok] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, d, h⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · simp only [List.cons.injEq, and_true] at h; exact h.2
    · exact absurd h1 (by decide)
  rw [h8] at hd2 hd4
  change ReachesRet linked _ s _
  janus_run
  rw [h8]
  exact liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 (zeroed_store _ _)

set_option maxRecDepth 20000 in
theorem hwb : WbLiveContract linked cW 4096 R 2 := by
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  change ReachesRet linked _ s _
  janus_run
  have h := wb_post (tys := tys) (ok := ok) tysOK (n := 2) (b := b) (L := L) (s := s) (by omega) pre.2.2.1 pre.2.2.2.2
  simp only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true, show 8 * 2 = 16 from rfl] at h
  exact h

/-! ### The call state -/

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The data segments, and the bump cell `HEAP`; zero elsewhere. -/
def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4288, 4312, true⟩, ⟨g0, 0x100, false⟩, ⟨P, 40, true⟩, ⟨wF, 4, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 1 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [1] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
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

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := s0.mem) (b := 0x400) (g := (s0.regs 28).toNat) (by decide) (by decide)
    (fun i hi hi' => ?_) (by decide) (by decide) (by decide) (fun t ht => absurd ht (by simp [tys]))
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem s0_sp : s0.sp.toNat = sp0 := by simp [s0, sp0]
theorem s0_g : (s0.regs 28).toNat = g0 := by simp [s0, g0]

theorem hP' : P = 1547840 := by unfold P; decide
theorem hs' : sT = 738112 := by unfold sT; decide
theorem hu' : uT = 701312 := by unfold uT; decide
theorem hw' : wF = 1705440 := by unfold wF; decide

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 4288 ∧ StackOK s0 4288 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 28).toNat + 16) 8 ((s0.sp.toNat - 4288, s0.sp.toNat + 24) :: R.rt) ∧
    LiveSep [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] R.rt ∧
    LiveSep [] [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] ∧
    (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s0.sp.toNat - 4288 ∨ s0.sp.toNat + 24 ≤ poolAddr) ∧
    Outside stkType 16 R.rt ∧ Outside u64Type 16 R.rt ∧ s0.mem.accessible wbFlag 4 false = true ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [stkType] ∧
    (∀ p c, c ≤ 1 → c < (1#64).toNat →
      R.ok (Extracted.program.contractAddr "runtime.growslice")
        [p, (1#64).toNat, c, (1#64).toNat - c, u64Type]) ∧
    (∀ q c, c ≤ 1 → c < (1#64).toNat →
      R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
        [q + 8 * c, 8 * ((1#64).toNat - c)]) ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    s0.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧ (1#64).toNat < 2 ^ 40 ∧ 24 ≤ 0x400 ∧
    (∀ c, c ≤ 1 → c < (1#64).toNat → 24 + 8 * growCap8 (1#64).toNat c ≤ 0x400) ∧
    (∀ c, c ≤ 1 → c < (1#64).toNat → growCap8 (1#64).toNat c ≤ 1) := by
  rw [hP, hTy, hU, hWF, aG, aP, aN, aGr, aM, aW, s0_sp, s0_g]
  have hrt : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, dataLoaded, ?_, ?_, by simp, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv0, by decide, by decide, ?_, ?_⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, hs', hw', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [hrt]; simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, hs', hw', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · intro r hr
    rw [hrt] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [HEAP, BUMP, WBUF] <;> omega
  · simp only [sp0, hP']; decide
  · rw [hs', hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [hu', hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [hw']; decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro p c hc hc'
    have : c = 0 := by simp at hc'; omega
    subst this
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, p, uT, by simp⟩)))
  · intro q c hc hc'
    have : c = 0 := by simp at hc'; omega
    subst this
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, by simp⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  · rw [hP']; unfold newOffset; decide
  · intro c hc hc'
    have : c = 0 := by simp at hc'; omega
    subst this
    decide
  · intro c hc hc'
    have : c = 0 := by simp at hc'; omega
    subst this
    decide

theorem hfl' : ∀ b L g v, R.inv b L g v → Outside wbFlag 4 L := by
  intro b L g v h
  obtain ⟨p, -, -, -, -, hL, -⟩ := h
  rw [hWF]
  exact outside_live hL (by simp only [HEAP, hw']; omega)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (B : Nat) (ret : Nat) (s : State)
    (L : List (Nat × Nat)) (bud : Nat) (n : BitVec 64),
    B < 2 ^ 40 ∧
    (PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      ptrType (SliceObj B) ∧
    PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      ptrType (SliceObj B) ∧
    NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R ∧
    GrowsliceLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2) ∧
    (∀ b L g v, R.inv b L g v → Outside wbFlag 4 L) ∧
    (RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [n] s) ∧
    ((GuardOK s 4288 ∧ StackOK s 4288 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4288, s.sp.toNat + 24) :: R.rt) ∧
      LiveSep [(s.sp.toNat - 4288, s.sp.toNat + 24)] R.rt ∧
      LiveSep L [(s.sp.toNat - 4288, s.sp.toNat + 24)] ∧
      (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s.sp.toNat - 4288 ∨ s.sp.toNat + 24 ≤ poolAddr)) ∧
      (Outside stkType 16 R.rt ∧ Outside u64Type 16 R.rt ∧
      s.mem.accessible wbFlag 4 false = true ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [stkType] ∧
      (∀ p c, c ≤ B → c < n.toNat →
        R.ok (Extracted.program.contractAddr "runtime.growslice") [p, n.toNat, c, n.toNat - c, u64Type])) ∧
      ((∀ q c, c ≤ B → c < n.toNat →
        R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
          [q + 8 * c, 8 * (n.toNat - c)]) ∧
      R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
      s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
      R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ n.toNat < 2 ^ 40 ∧ 24 ≤ bud ∧
      (∀ c, c ≤ B → c < n.toNat → 24 + 8 * growCap8 n.toNat c ≤ bud) ∧
      (∀ c, c ≤ B → c < n.toNat → growCap8 n.toNat c ≤ B))) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23⟩ := pre
  refine ⟨implAt, R, 1, ret, s0, [], 0x400, 1, by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hfl', ⟨hret, setup⟩,
    ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨a9, a10, a11, a12, a13, a14, a15⟩,
      ⟨a16, a17, a18, a19, a20, a21, a22, a23⟩⟩⟩
  · rw [aG, hPT]; exact hget
  · rw [aP, hPT]; exact hput
  · rw [aN]; exact hnew
  · rw [aGr]; exact hgrow
  · rw [aM]; exact hclr
  · rw [aW]; exact hwb

/-- So the guarantee is reached: `StackGrow(1)` returns `1`, the capacity of the grown stack, with the
runtime's invariant again for the live set extended by `ex` (the abandoned array). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 1 ∧
      ∃ xs b', FreshFrom xs [] ∧ b' ≤ 0x400 ∧
        MemFrame s0.mem s'.mem (R.rt ++ [(s0.sp.toNat - 4288, s0.sp.toNat + 24)]) ∧
        LiveFrame s0.mem s'.mem [] [] ∧ R.inv b' ([] ++ xs) (s0.regs 28).toNat (view R.rt ([] ++ xs) s'.mem) := by
  have h := correctness implAt R 1 (by decide) (by rw [aG, hPT]; exact hget) (by rw [aP, hPT]; exact hput)
    (by rw [aN]; exact hnew) (by rw [aGr]; exact hgrow) (by rw [aM]; exact hclr) (by rw [aW]; exact hwb)
    hfl' 1 [] 0x400 ret hret s0 setup pre
  refine Returns.mono h fun s' ⟨hab, cap0, hc, hres, xs, b', hfr, hb, hF, hLF, hinv⟩ => ⟨hab, ?_, xs, b', hfr, hb, hF, hLF, hinv⟩
  have : cap0 = 0 ∨ cap0 = 1 := by omega
  rcases this with rfl | rfl
  · rw [hres]; simp; decide
  · rw [hres]; simp

end Witness

end Proof

import Extracted

/-!
# `BoxAfterNew(s string, v uint64) (*Node, any, any)` (arm64)

```go
type Node struct{ A, B uint64 }
func BoxAfterNew(s string, v uint64) (*Node, any, any) { return &Node{v, v + 1}, s, v }
```

Three runtime calls in a row, each a **live** contract over the same runtime `R` (`Janus.Contracts.Live`):
`runtime.newobject` allocates the node, then `runtime.convTstring` boxes the string and `runtime.convT64` boxes the
number (`IfaceLive`). The point of the example is that the boxing contracts follow a live allocation (and each other):
the single-call `ConvTstring`/`ConvT64` cannot, they need their own readiness predicate and an `IfaceModel`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

abbrev tNode : Nat := Extracted.dataAddr.«type:boxdemo.Node#dac8e17d»
abbrev tStr : Nat := Extracted.dataAddr.«type:string#f88732b8»
abbrev tU64 : Nat := Extracted.dataAddr.«type:uint64#703ad2db»

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (sp' sl v : BitVec 64)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hcs : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convTstring") 4096 R convTstringSpec convTstringLive)
    (h64 : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") 4096 R convT64Spec convT64Live) :
    Ensures (Extracted.program.link impl) Extracted.entry [sp', sl, v]
      (fun s => GuardOK s 4160 ∧ StackOK s 4168 32 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4168) 4200 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4168) 4200 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ Outside tNode 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [tNode] ∧
        R.ok (Extracted.program.contractAddr "runtime.convTstring") [sp'.toNat, sl.toNat] ∧
        R.ok (Extracted.program.contractAddr "runtime.convT64") [v.toNat] ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ 40 ≤ b ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4168, s.sp.toNat + 32)]))
      (fun s s' => InRanges (s'.regs 0).toNat 16 R.rt ∧
        s'.mem.readLE (s'.regs 0).toNat 8 = v.toNat ∧
        s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = (v + 1).toNat ∧
        (s'.regs 1).toNat = tStr ∧ (s'.regs 3).toNat = tU64 ∧
        (sl.toNat ≠ 0 → BoxWords' R.rt s'.mem (s'.regs 2).toNat [sp'.toNat, sl.toNat]) ∧
        BoxHolds' R.rt s'.mem (s'.regs 4).toNat 8 v.toNat ∧
        ∃ b' L', b - 40 ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          InRanges (s'.regs 0).toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 32)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hty, hok1, hok2, hok3, hinv, hbud, hLs⟩
  janus_intro hs
  janus_data hd [hw]
  have hc1 : (if sl.toNat = 0 then 0 else 16) ≤ b - 16 := by split <;> omega
  have hc2 : (if v.toNat < 256 then 0 else 8) ≤ b - 16 - (if sl.toNat = 0 then 0 else 16) := by split <;> split <;> omega
  janus_run until [Extracted.entry + 0x4c] calls [hnew.pos, hcs]
  rename_i nd r1n r2n jk1 fl1 vr1 M1 ex1 ep1 hfr1 hpost1 hlf1 hfresh1 hapart1 hinv1 bx r1c r2c jk2 fl2 vr2 M2 ex2 ep2 hfr2 hpost2 hlf2 hfresh2 hapart2 hinv2
  have hbox : ∀ r ∈ (if sl.toNat = 0 then [] else [(bx.toNat, bx.toNat + 16)]),
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 64 - 4096 ∨ s.sp.toNat - 64 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 64 + 8 ∨ s.sp.toNat - 64 + 8 + 8 ≤ r.1) := by
    intro r hr
    have h1 := hapart2 r hr (s.sp.toNat - 64 - 4096, s.sp.toNat - 64 - 8) (by simp)
    have h2 := hapart2 r hr (s.sp.toNat - 64 + 8, s.sp.toNat - 64 + 8 + 16) (by simp)
    simp only [Apart] at h1 h2
    constructor <;> omega
  janus_run calls [h64]
  rename_i b3 r1d r2d jk3 fl3 vr3 M3 ex3 ep3 hfr3 hpost3 hlf3 hfresh3 hapart3 hinv3
  refine ⟨jk1, rfl, rfl, fun hnz => ?_, ?bh, _, _, ?hb, hinv3, ?hin, ?hfr⟩
  · -- the string's box is live (non-empty string): convT64 and the spill store leave it as convTstring made it
    simp only [hnz, ↓reduceIte] at hpost2
    obtain ⟨h1, h2, h3, h4⟩ := hpost2
    refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, fun i hi => ?_⟩
    have hi' : i < 2 := by simpa using hi
    have hin8 : InRanges (bx.toNat + 8 * i) 8 R.rt := InRanges.sub (by simpa using h3) (by omega) (by omega)
    have hap := InRanges.apart hin8 hout
    unfold Apart at hap
    rw [hlf3.readLE (bx.toNat + 8 * i) 8 ⟨(bx.toNat, bx.toNat + 16), by simp [hnz], by omega, by omega⟩ trivial]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    simpa using h4 i hi
  · exact hpost3
  · split <;> split <;> omega
  · exact InRanges.append_left (InRanges.append_left (InRanges.append_right L
      ⟨(_, _), List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩) _) _
  · janus_frame

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def csA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.convTstring")
def c64A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.convT64")

/-- The stub runtime: generic code, placed at `BoxAfterNew`'s own contract addresses (a non-empty string and `v ≥ 256`). -/
def implAt : List Segment := [newobjectSeg newA, convTstringSeg csA 16, convT64Seg c64A 16]

def sPtr : Nat := 0x300000

/-- The requests the witness runtime serves: `BoxAfterNew("hello", 300)`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [tNode]) ∨ (a = csA ∧ args = [sPtr, 5]) ∨ (a = c64A ∧ args = [300])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_cs : Extracted.program.contractAddr "runtime.convTstring" = csA := by decide
theorem addr_64 : Extracted.program.contractAddr "runtime.convT64" = c64A := by decide

theorem hok_cs : ∀ args, ok csA args → ∃ p, args = [p, 5] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
  · exfalso; revert h; decide
  · exact ⟨sPtr, h⟩
  · exfalso; revert h; decide

theorem hok_64 : ∀ args, ok c64A args → args = [300] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exfalso; revert h; decide
  · exfalso; revert h; decide
  · exact h

/-- The three live contracts at `BoxAfterNew`'s own addresses: one tactic each. -/
theorem model_new : NewobjectLiveContract linked newA 4096 R := by janus_live_newobject
theorem model_cs : RtLiveContract linked csA 4096 R convTstringSpec convTstringLive := by
  janus_live_convtstring 5 16 hok_cs
theorem model_64 : RtLiveContract linked c64A 4096 R convT64Spec convT64Live := by
  janus_live_convt64 300 16 hok_64

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4168, 4200, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

/-- `BoxAfterNew("hello", 300)`: the string at `sPtr` (never read). -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 sPtr else if i = 1 then 5 else if i = 2 then 300
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 sPtr, 5, 300] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

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

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : GuardOK s0 4160 ∧ StackOK s0 4168 32 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4168) 4200 R.rt ∧ Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4168) 4200 ∧
    Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧ Outside tNode 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [tNode] ∧
    R.ok (Extracted.program.contractAddr "runtime.convTstring") [(BitVec.ofNat 64 sPtr).toNat, (5 : BitVec 64).toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.convT64") [(300 : BitVec 64).toNat] ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧ 40 ≤ 0x400 ∧
    (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [(s0.sp.toNat - 4168, s0.sp.toNat + 32)]) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, inv0, by decide, fun r hr => absurd hr (by simp)⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, rfl⟩
  · rw [addr_cs]; exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  · rw [addr_64]; exact Or.inr (Or.inr ⟨rfl, by decide⟩)

/-! ### The call-site states of the three runtime contracts -/

/-- A call state at the runtime entry `addr` (words `x, y` in `X0, X1`), in the witness's world: the heap and
the invariant are those of `s0`; the callee's frame lies just below the caller's. -/
def callS (addr x y : Nat) : State :=
  { s0 with
    pc := BitVec.ofNat 64 addr
    sp := BitVec.ofNat 64 (sp0 - 16)
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 1 then BitVec.ofNat 64 y else s0.regs i }

theorem cs_sp (a x y : Nat) : (callS a x y).sp.toNat = sp0 - 16 := by rfl
theorem cs_g (a x y : Nat) : ((callS a x y).regs 28).toNat = g0 := by rfl
theorem cs_x30 (a x y : Nat) : ((callS a x y).regs 30).toNat = ret := by rfl
theorem cs_mem (a x y : Nat) : (callS a x y).mem = mem0 := rfl

theorem cs_callOK (a x y n : Nat) (hn : n ≤ 3) : CallOK (callS a x y) 4096 n := by
  have hw : mem0.accessible (sp0 - 16 - 4096) (4096 + 8 + 8 * 3) true = true := by decide
  simp only [CallOK, cs_x30, cs_sp, cs_mem]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by first | decide | (unfold sp0; omega), ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_room (a x y n : Nat) (hn : n ≤ 3) : StackRoom (callS a x y) 4096 n := by
  simp only [StackRoom, GuardOK, cs_g, cs_sp, cs_mem, calleeStack]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, sp0, g0]
  omega

theorem cs_winR (a x y n : Nat) (hn : n ≤ 3) : LiveSep (calleeStack (callS a x y) 4096 n) R.rt := by
  intro x' hx
  simp only [calleeStack, cs_sp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega

def sNew : State := callS newA tNode 0
def sCs : State := callS csA sPtr 5
def s64 : State := callS c64A 300 0

@[reducible] def newSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1)

theorem site_new : newSite R newA [] 0x400 sNew := by
  refine ⟨⟨cs_callOK _ _ _ 1 (by omega), ⟨by decide, by decide⟩, (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩,
    cs_room _ _ _ 1 (by omega), ?_, inv0, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ 1 (by omega)⟩
  exact Or.inl ⟨rfl, rfl⟩

theorem site_cs : RtLivePre 4096 R convTstringSpec convTstringLive csA [] 0x400 sCs := by
  refine ⟨cs_callOK _ _ _ 2 (by omega), trivial, fun r hr => by simp [convTstringSpec] at hr, trivial,
    cs_room _ _ _ 2 (by omega), ⟨Or.inr (Or.inl ⟨rfl, by decide⟩), inv0, by decide,
    fun r hr => absurd hr (by simp), cs_winR _ _ _ 2 (by omega)⟩⟩

theorem site_64 : RtLivePre 4096 R convT64Spec convT64Live c64A [] 0x400 s64 := by
  refine ⟨cs_callOK _ _ _ 1 (by omega), trivial, fun r hr => by simp [convT64Spec] at hr, trivial,
    cs_room _ _ _ 1 (by omega), ⟨Or.inr (Or.inr ⟨rfl, by decide⟩), inv0, by decide,
    fun r hr => absurd hr (by simp), cs_winR _ _ _ 1 (by omega)⟩⟩

/-- The returning run, exactly as `correctness` states it at the witness. -/
theorem returnsF : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (InRanges (s'.regs 0).toNat 16 R.rt ∧
      s'.mem.readLE (s'.regs 0).toNat 8 = (300 : BitVec 64).toNat ∧
      s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = ((300 : BitVec 64) + 1).toNat ∧
      (s'.regs 1).toNat = tStr ∧ (s'.regs 3).toNat = tU64 ∧
      ((5 : BitVec 64).toNat ≠ 0 →
        BoxWords' R.rt s'.mem (s'.regs 2).toNat [(BitVec.ofNat 64 sPtr).toNat, (5 : BitVec 64).toNat]) ∧
      BoxHolds' R.rt s'.mem (s'.regs 4).toNat 8 (300 : BitVec 64).toNat ∧
      ∃ b' L', 0x400 - 40 ≤ b' ∧ R.inv b' L' (s0.regs 28).toNat (view R.rt L' s'.mem) ∧
        InRanges (s'.regs 0).toNat 16 L' ∧
        MemFrame s0.mem s'.mem (R.rt ++ [(s0.sp.toNat - 4168, s0.sp.toNat + 32)])) :=
  correctness implAt R 0x400 [] (BitVec.ofNat 64 sPtr) 5 300 (by rw [addr_new]; exact model_new)
    (by rw [addr_cs]; exact model_cs) (by rw [addr_64]; exact model_64) ret hret s0 setup pre

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`BoxAfterNew("hello", 300)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State),
    NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convTstring") 4096 R convTstringSpec convTstringLive ∧
    RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") 4096 R convT64Spec convT64Live ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 sPtr, 5, 300] s ∧
    (GuardOK s 4160 ∧ StackOK s 4168 32 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4168) 4200 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4168) 4200 ∧
      Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ Outside tNode 16 R.rt ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [tNode] ∧
      R.ok (Extracted.program.contractAddr "runtime.convTstring") [(BitVec.ofNat 64 sPtr).toNat, (5 : BitVec 64).toNat] ∧
      R.ok (Extracted.program.contractAddr "runtime.convT64") [(300 : BitVec 64).toNat] ∧
      R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ 40 ≤ b ∧
      (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4168, s.sp.toNat + 32)])) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      newSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.convTstring") ∧
      RtLivePre 4096 R convTstringSpec convTstringLive (Extracted.program.contractAddr "runtime.convTstring") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.convT64") ∧
      RtLivePre 4096 R convT64Spec convT64Live (Extracted.program.contractAddr "runtime.convT64") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (InRanges (s'.regs 0).toNat 16 R.rt ∧
        s'.mem.readLE (s'.regs 0).toNat 8 = (300 : BitVec 64).toNat ∧
        s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = ((300 : BitVec 64) + 1).toNat ∧
        (s'.regs 1).toNat = tStr ∧ (s'.regs 3).toNat = tU64 ∧
        ((5 : BitVec 64).toNat ≠ 0 →
          BoxWords' R.rt s'.mem (s'.regs 2).toNat [(BitVec.ofNat 64 sPtr).toNat, (5 : BitVec 64).toNat]) ∧
        BoxHolds' R.rt s'.mem (s'.regs 4).toNat 8 (300 : BitVec 64).toNat ∧
        ∃ b' L', b - 40 ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          InRanges (s'.regs 0).toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 32)])) :=
  ⟨implAt, R, 0x400, [], ret, s0, by rw [addr_new]; exact model_new, by rw [addr_cs]; exact model_cs,
    by rw [addr_64]; exact model_64, hret, setup, pre,
    ⟨[], 0x400, sNew, by rw [addr_new]; rfl, by rw [addr_new]; exact site_new⟩,
    ⟨[], 0x400, sCs, by rw [addr_cs]; rfl, by rw [addr_cs]; exact site_cs⟩,
    ⟨[], 0x400, s64, by rw [addr_64]; rfl, by rw [addr_64]; exact site_64⟩, returnsF⟩

/-- So the guarantee is reached: the call returns the string and `uint64` type descriptors. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 1).toNat = tStr ∧ (s'.regs 3).toNat = tU64 :=
  returnsF.mono
    fun _ h => ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Witness

end Proof

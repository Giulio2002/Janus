import Janus.Contracts.PanicSatDecode

/-!
# The model engine meets the `gopanic`, `Goexit` and `deferreturn` contracts (arm64)

The induction over the loop of the model engine (`docs/model/panic_model_arm64.s`, label `LH`): an
invariant `Inv` on the loop state, one lemma per kind of step (the open-coded step, the record
step, the silent steps `TOREC` and `POPREC`, the end of the loop), and `engine_loop`, which shows
that `Panic.Engine` holds for the model, for every list of deferred calls.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel Janus.Spec.Map

theorem _root_.Janus.Spec.Map.Agrees.mono' {m m' : Memory} {rs rs' : List (Nat × Nat)} (h : Agrees m m' rs')
    (hs : ∀ a n, InRanges a n rs → InRanges a n rs') : Agrees m m' rs :=
  ⟨h.1, fun a ha => h.2 a (by
    have := hs a 1 ha; exact this)⟩

/-- The ranges of memory the runtime reads again between deferred calls, other than the
`deferBits` byte: the pending slots and the funcvals' code words. -/
def keepCore (m : Memory) (F : Frame) (items : List Item) : List (Nat × Nat) :=
  (match F.openAt with
    | none => []
    | some (ba, sa) => (openBits (m.readLE ba 1)).map (fun i => (sa + 8 * i, sa + 8 * i + 8))) ++
  items.map (fun it => (it.fn, it.fn + 8))

theorem frameKeep_eq (m : Memory) (F : Frame) (items : List Item) :
    frameKeep m F items = bitsWin F ++ keepCore m F items := by
  unfold frameKeep keepCore bitsWin
  cases F.openAt with
  | none => rfl
  | some p => obtain ⟨ba, sa⟩ := p; simp

theorem inRanges_keepCore_fn {m : Memory} {F : Frame} {items : List Item} {it : Item} (h : it ∈ items) :
    InRanges it.fn 8 (keepCore m F items) :=
  ⟨(it.fn, it.fn + 8), List.mem_append_right _ (List.mem_map.2 ⟨it, h, rfl⟩), Nat.le_refl _, Nat.le_refl _⟩

theorem inRanges_keepCore_slot {m : Memory} {F : Frame} {items : List Item} {ba sa i : Nat}
    (hF : F.openAt = some (ba, sa)) (hi : i ∈ openBits (m.readLE ba 1)) :
    InRanges (sa + 8 * i) 8 (keepCore m F items) := by
  refine ⟨(sa + 8 * i, sa + 8 * i + 8), List.mem_append_left _ ?_, Nat.le_refl _, Nat.le_refl _⟩
  rw [hF]; exact List.mem_map.2 ⟨i, hi, rfl⟩

/-! ## The calls still to make -/

theorem curItems_zero (m : Memory) (F : Frame) : curItems m F 0 = recItems F.sp (defers0 m) := by
  simp [curItems, phF, frameItems]

theorem curItems_ne {m : Memory} {F : Frame} {ph : Nat} (h : ph ≠ 0) :
    curItems m F ph = frameItems m F (defers0 m) := by
  simp [curItems, phF, h]

theorem curItems_open {m : Memory} {F : Frame} {ph ba sa : Nat} (hph : ph ≠ 0)
    (hF : F.openAt = some (ba, sa)) (hb0 : 0 < m.readLE ba 1) :
    curItems m F ph =
      { fn := m.readLE (sa + 8 * topBit (m.readLE ba 1)) 8, bits := some (m.readLE ba 1 % 2 ^ topBit (m.readLE ba 1)),
        chain := defers0 m } ::
      (openItems m sa (m.readLE ba 1 % 2 ^ topBit (m.readLE ba 1)) (defers0 m) ++ recItems F.sp (defers0 m)) := by
  rw [curItems_ne hph]
  unfold frameItems; rw [hF]
  simp only
  rw [openItems_top (by have := Memory.readLE_lt m ba 1; simpa using this) hb0]
  rfl

theorem curItems_open_zero {m : Memory} {F : Frame} {ph ba sa : Nat} (hph : ph ≠ 0)
    (hF : F.openAt = some (ba, sa)) (hb0 : m.readLE ba 1 = 0) :
    curItems m F ph = recItems F.sp (defers0 m) := by
  rw [curItems_ne hph]
  unfold frameItems; rw [hF]
  simp only [hb0]
  have : openBits 0 = [] := by decide
  simp [openItems, this]

/-- The calls only depend on the chain, the `deferBits` byte and the slots of the pending
defers. -/
theorem curItems_congr {m m' : Memory} {F : Frame} {ph : Nat} (hd : defers0 m' = defers0 m)
    (hb : ∀ ba sa, F.openAt = some (ba, sa) → ph ≠ 0 → m'.readLE ba 1 = m.readLE ba 1 ∧
      ∀ i ∈ openBits (m.readLE ba 1), m'.readLE (sa + 8 * i) 8 = m.readLE (sa + 8 * i) 8) :
    curItems m' F ph = curItems m F ph := by
  by_cases hph : ph = 0
  · subst hph; rw [curItems_zero, curItems_zero, hd]
  · rw [curItems_ne hph, curItems_ne hph]
    unfold frameItems
    cases hF : F.openAt with
    | none => simp [hd]
    | some p =>
      obtain ⟨ba, sa⟩ := p
      obtain ⟨h1, h2⟩ := hb ba sa hF hph
      simp only [hd, h1]
      rw [openItems_congr h2]

/-! ## The invariant -/

theorem saved0_none_iff (m : Memory) : saved0 m = none ↔ rd m (B + 0x10) = 0 := by
  rw [saved0_eq]; split <;> simp_all

/-- The loop state of the model (anywhere in the loop or at a deferred call's return point). `m0`
is the memory at the runtime function's entry, `items0` the calls the loop was entered with, `ds0`
the defer chain then. -/
structure Inv0 (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item) (ds0 : List DeferRec)
    (mode : DeferMode) (x28 x18 : W64) (lr x29 : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat) : Prop where
  sp : c.sp.toNat + 96 = F.sp
  al : F.sp % 16 = 0
  hi : F.sp + 8 ≤ 2 ^ 48
  acc : c.mem.accessible c.sp.toNat 96 true = true
  r28 : c.regs 28 = x28
  r18 : c.regs 18 = x18
  spB : F.sp ≤ B ∨ B + 0x1000 + 96 ≤ F.sp
  fm : FrameMem c.mem F mode ph x18.toNat lr x29
  hlr : mode = .ret → lr % 4 = 0 ∧ lr < 2 ^ 48
  hbd : F.bound < 2 ^ 64
  hres : F.resume % 4 = 0 ∧ F.resume < 2 ^ 48
  env : Env0 T c.mem
  pan : panics0 c.mem = ch
  room : rm ≤ room0 c.mem
  sv : mode = .ret → rd c.mem (B + 0x10) = 0
  chn : frameRest F.sp (defers0 c.mem) = frameRest F.sp ds0
  pm : mode = .panic → ∃ r rs, ch = r :: rs ∧ r.recovered = false ∧ r.goexit = false
  agr : Agrees m0 c.mem (keepCore m0 F items0)
  fo : FrameOK (P0 T RPa) m0 F items0
  bsub : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (c.mem.readLE ba 1), i ∈ openBits (m0.readLE ba 1)
  its : ∀ it ∈ curItems c.mem F ph, it ∈ items0

theorem inRanges_bits {F : Frame} {ba sa : Nat} (hF : F.openAt = some (ba, sa)) (items : List (Nat × Nat)) :
    InRanges ba 1 (bitsWin F ++ items) :=
  ⟨(ba, ba + 1), List.mem_append_left _ (by simp [bitsWin, hF]), Nat.le_refl _, Nat.le_refl _⟩

theorem inRanges_tail {a n : Nat} {r : Nat × Nat} {rs : List (Nat × Nat)} (h : InRanges a n rs) :
    InRanges a n (r :: rs) := h.of_subset fun r' hr' => List.mem_cons_of_mem _ hr'

/-- The state after a deferred call returned (or after a nested panic left it): the invariant
carries over, with the panic chain and the room the caller supplies. -/
theorem Inv0.ret {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
    {mode : DeferMode} {x28 x18 : W64} {lr x29 : Nat} {e e' : State} {ch : List PanicRec} {rm ph : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph)
    (hdr : DeferReturned (P0 T RPa) x28 x18 F.sp (frameKeep m0 F items0) e e')
    (ch' : List PanicRec) (rm' : Nat) (hpan : panics0 e'.mem = ch') (hroom : rm' ≤ room0 e'.mem)
    (hpm : mode = .panic → ∃ r rs, ch' = r :: rs ∧ r.recovered = false ∧ r.goexit = false) :
    Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e' ch' rm' ph := by
  obtain ⟨hpc, hsp, h28, h18, hag, henv, hdef, hsav, hrm⟩ := hdr
  rw [frameKeep_eq] at hag
  have hagE : Agrees e.mem e'.mem (keepCore m0 F items0) := hag.mono' fun a n h =>
    inRanges_tail (h.append_right _)
  have hfr : ∀ k, k + 8 ≤ 96 → e'.mem.readLE (F.sp - 96 + k) 8 = e.mem.readLE (F.sp - 96 + k) 8 := fun k hk =>
    hag.readLE ⟨(e.sp.toNat, F.sp), List.mem_cons_self, by have := hI.sp; simp only; omega,
      by have := hI.sp; simp only; omega⟩
  have hdef' : defers0 e'.mem = defers0 e.mem := hdef
  have hbyte : ∀ ba sa, F.openAt = some (ba, sa) → e'.mem.readLE ba 1 = e.mem.readLE ba 1 := fun ba sa hF =>
    hag.readLE (inRanges_tail (inRanges_bits hF (keepCore m0 F items0)))
  have hsl : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (e.mem.readLE ba 1),
      e'.mem.readLE (sa + 8 * i) 8 = e.mem.readLE (sa + 8 * i) 8 := fun ba sa hF i hi =>
    hagE.readLE (inRanges_keepCore_slot hF (hI.bsub ba sa hF i hi))
  have hci : curItems e'.mem F ph = curItems e.mem F ph :=
    curItems_congr hdef' fun ba sa hF _ => ⟨hbyte ba sa hF, hsl ba sa hF⟩
  have hfm := hI.fm
  have hsv : saved0 e'.mem = saved0 e.mem := hsav
  have hB := hI.sp
  refine ⟨by rw [hsp]; exact hI.sp, hI.al, hI.hi, by rw [hsp, hag.accessible]; exact hI.acc, h28, h18, hI.spB,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hI.hlr, hI.hbd, hI.hres, henv, hpan, hroom,
    fun hm => (saved0_none_iff _).1 (by rw [hsv]; exact (saved0_none_iff _).2 (hI.sv hm)),
    by rw [hdef']; exact hI.chn, hpm, hI.agr.trans hagE, hI.fo,
    fun ba sa hF i hi => hI.bsub ba sa hF i (by rw [← hbyte ba sa hF]; exact hi),
    fun it hit => hI.its it (by rw [← hci]; exact hit)⟩
  · rw [show F.sp - 96 = F.sp - 96 + 0 from rfl, hfr 0 (by omega)]; exact hfm.w0
  · rw [hfr 8 (by omega)]; exact hfm.w8
  · rw [hfr 16 (by omega)]; exact hfm.w16
  · rw [hfr 24 (by omega)]; exact hfm.w24
  · rw [hfr 32 (by omega)]; exact hfm.w32
  · intro ba sa hF
    rw [hfr 40 (by omega), hfr 48 (by omega)]; exact hfm.w40 ba sa hF
  · rw [hfr 56 (by omega)]; exact hfm.w56
  · intro hm; rw [hfr 64 (by omega), hfr 72 (by omega)]; exact hfm.w64 hm
  · exact hfm.hph

/-! ## Facts the steps use -/

section facts
variable {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
  {mode : DeferMode} {x28 x18 : W64} {lr x29 : Nat} {c : State} {ch : List PanicRec} {rm ph : Nat}

theorem Inv0.sp_eq (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) : F.sp - 96 = c.sp.toNat := by
  have := hI.sp; omega

theorem Inv0.item_facts (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) {it : Item}
    (hit : it ∈ items0) :
    it.fn + 8 ≤ 2 ^ 48 ∧ c.mem.accessible it.fn 8 false = true ∧ c.mem.readLE it.fn 8 % 4 = 0 ∧
      c.mem.readLE it.fn 8 < 2 ^ 48 ∧ Outside it.fn 8 [(B, B + 0x1000)] ∧ (it.fn + 8 ≤ F.sp - 256 ∨ F.sp ≤ it.fn) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.fo.2 it hit
  have hr : c.mem.readLE it.fn 8 = m0.readLE it.fn 8 := hI.agr.readLE (inRanges_keepCore_fn hit)
  refine ⟨h1, ?_, by rw [hr]; exact h3, by rw [hr]; exact h4, h5, h6⟩
  rw [hI.agr.accessible]; exact h2

theorem Inv0.ba_facts (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) {ba sa : Nat}
    (hF : F.openAt = some (ba, sa)) :
    ba + 1 ≤ 2 ^ 48 ∧ c.mem.accessible ba 1 true = true ∧ Outside ba 1 [(B, B + 0x1000)] ∧ F.sp ≤ ba ∧
      ∀ it ∈ items0, it.fn + 8 ≤ ba ∨ ba + 1 ≤ it.fn := by
  have h := hI.fo.1
  rw [hF] at h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h
  exact ⟨h1, by rw [hI.agr.accessible]; exact h2, h3, h4, h6⟩

theorem Inv0.slot_facts (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) {ba sa i : Nat}
    (hF : F.openAt = some (ba, sa)) (hi : i ∈ openBits (c.mem.readLE ba 1)) :
    sa + 8 * i + 8 ≤ 2 ^ 48 ∧ c.mem.accessible (sa + 8 * i) 8 false = true ∧
      (sa + 8 * i + 8 ≤ ba ∨ ba + 1 ≤ sa + 8 * i) ∧ F.sp ≤ sa + 8 * i ∧ Outside (sa + 8 * i) 8 [(B, B + 0x1000)] := by
  have h := hI.fo.1
  rw [hF] at h
  obtain ⟨-, -, -, -, h5, -⟩ := h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h5 i (hI.bsub ba sa hF i hi)
  exact ⟨a1, by rw [hI.agr.accessible]; exact a2, a3, a4, a5⟩

theorem Inv0.slot_read (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) {ba sa i : Nat}
    (hF : F.openAt = some (ba, sa)) (hi : i ∈ openBits (c.mem.readLE ba 1)) :
    c.mem.readLE (sa + 8 * i) 8 = m0.readLE (sa + 8 * i) 8 :=
  hI.agr.readLE (inRanges_keepCore_slot hF (hI.bsub ba sa hF i hi))

end facts

/-! ## The step that makes a call -/

/-- The model engine is at the entry of the deferred call `it` (state `e`), reached from the loop
head `c`; the rest of the loop is `rest`. -/
structure CallSt (p : Program) (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item)
    (ds0 : List DeferRec) (mode : DeferMode) (x28 x18 : W64) (lr x29 : Nat) (c : State)
    (ch : List PanicRec) (rm ph : Nat) (it : Item) (rest : List Item) (e : State) : Prop where
  steps : ∃ k, Program.Steps p c k e
  call : DeferCall (P0 T RPa) x28 x18 F.sp it.fn e
  mf : MemFrame c.mem e.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F)
  bits : ∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b
  inv : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph
  chain : defers0 e.mem = it.chain
  cur : curItems e.mem F ph = rest
  sv : saved0 e.mem = saved0 c.mem
  rmono : room0 c.mem ≤ room0 e.mem
  recov : (it.bits = none ∧ ph = 0) ∨
    (∃ b ba sa, it.bits = some b ∧ F.openAt = some (ba, sa) ∧ ph ≠ 0 ∧ e.mem.readLE ba 1 = b)

section steps
variable {p : Program} {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
  {ds0 : List DeferRec} {mode : DeferMode} {x28 x18 : W64} {lr x29 : Nat} {c : State}
  {ch : List PanicRec} {rm ph : Nat}

/-- Memory changes outside `P.priv` keep the loop invariant's model facts. -/
theorem env0_of_outside {m : Memory} {a n v : Nat} {T : List FuncInfo} (h : Env0 T m)
    (ho : Outside a n [(B, B + 0x1000)]) : Env0 T (m.writeLE a n v) :=
  env0_agree h (agrees_writeLE m v ho)

theorem Inv0.spw (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) :
    c.sp.toNat % 16 = 0 ∧ c.sp.toNat + 104 ≤ 2 ^ 48 ∧ c.sp.toNat + 96 = F.sp := by
  have := hI.sp; have := hI.al; have := hI.hi; omega

theorem outside_of_forall {a n : Nat} : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n rs
  | [], _ => trivial
  | r :: rs, h => by
    obtain ⟨lo, hi⟩ := r
    exact ⟨h (lo, hi) (List.mem_cons_self), outside_of_forall fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- Every range the runtime reads again is apart from what the loop writes (the model's records,
its stack window below the frame, the `deferBits` byte). -/
theorem Inv0.keep_apart (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) :
    ∀ r ∈ keepCore m0 F items0, r.2 = r.1 + 8 ∧
      Outside r.1 8 ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
  intro r hr
  unfold keepCore at hr
  have hfo := hI.fo
  have hsp96 := hI.sp
  rcases List.mem_append.1 hr with hr | hr
  · -- a pending slot
    cases hF : F.openAt with
    | none => rw [hF] at hr; simp at hr
    | some q =>
      obtain ⟨ba, sa⟩ := q
      rw [hF] at hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
      have h := hfo.1
      rw [hF] at h
      obtain ⟨-, -, -, hba, hsl, -⟩ := h
      obtain ⟨a1, a2, a3, a4, a5⟩ := hsl i hi
      refine ⟨rfl, ?_⟩
      have o2 : Outside (sa + 8 * i) 8 (rtWin (P0 T RPa) F) := by
        simp only [rtWin, P0_depth, outside_cons, outside_nil, and_true]; omega
      have o3 : Outside (sa + 8 * i) 8 (bitsWin F) := by
        simp only [bitsWin, hF, outside_cons, outside_nil, and_true]; omega
      rw [outside_append, outside_append]; exact ⟨⟨a5, o2⟩, o3⟩
  · obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hr
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfo.2 it hit
    simp only [P0_depth] at f6
    refine ⟨rfl, ?_⟩
    have o2 : Outside it.fn 8 (rtWin (P0 T RPa) F) := by
      simp only [rtWin, P0_depth, outside_cons, outside_nil, and_true]; omega
    have o3 : Outside it.fn 8 (bitsWin F) := by
      cases hF : F.openAt with
      | none => simp [bitsWin, hF]
      | some q =>
        obtain ⟨ba, sa⟩ := q
        have h := hfo.1
        rw [hF] at h
        have := h.2.2.2.2.2 it hit
        simp only [bitsWin, hF, outside_cons, outside_nil, and_true]
        omega
    rw [outside_append, outside_append]; exact ⟨⟨f5, o2⟩, o3⟩

theorem FrameMem.congr {m m' : Memory} {F : Frame} {mode : DeferMode} {ph x18 lr x29 : Nat}
    (h : FrameMem m F mode ph x18 lr x29)
    (hk : ∀ k, k + 8 ≤ 96 → m'.readLE (F.sp - 96 + k) 8 = m.readLE (F.sp - 96 + k) 8) :
    FrameMem m' F mode ph x18 lr x29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hph⟩
  · have := hk 0 (by omega); simpa using this.trans h.w0
  · exact (hk 8 (by omega)).trans h.w8
  · exact (hk 16 (by omega)).trans h.w16
  · exact (hk 24 (by omega)).trans h.w24
  · exact (hk 32 (by omega)).trans h.w32
  · intro ba sa hF
    exact ⟨(hk 40 (by omega)).trans (h.w40 ba sa hF).1, (hk 48 (by omega)).trans (h.w40 ba sa hF).2⟩
  · exact (hk 56 (by omega)).trans h.w56
  · intro hm
    exact ⟨(hk 64 (by omega)).trans (h.w64 hm).1, (hk 72 (by omega)).trans (h.w64 hm).2⟩

/-- Moving from one loop state to another: what the loop writes is confined to the model's
records, its stack window and the `deferBits` byte; the caller supplies what changed in the model's
own bookkeeping. -/
theorem Inv0.step (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) {e : State} (ph' : Nat)
    (hsp : e.sp = c.sp) (h28 : e.regs 28 = c.regs 28) (h18 : e.regs 18 = c.regs 18)
    (hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F))
    (hfm : FrameMem e.mem F mode ph' x18.toNat lr x29)
    (henv : Env0 T e.mem) (hpan : panics0 e.mem = ch) (hroom : rm ≤ room0 e.mem)
    (hsv : mode = .ret → rd e.mem (B + 0x10) = 0)
    (hchn : frameRest F.sp (defers0 e.mem) = frameRest F.sp ds0)
    (hbs : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (e.mem.readLE ba 1), i ∈ openBits (m0.readLE ba 1))
    (hits : ∀ it ∈ curItems e.mem F ph', it ∈ items0) :
    Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph' := by
  refine ⟨by rw [hsp]; exact hI.sp, hI.al, hI.hi, by rw [hsp, hmf.accessible]; exact hI.acc,
    by rw [h28]; exact hI.r28, by rw [h18]; exact hI.r18, hI.spB, hfm, hI.hlr, hI.hbd, hI.hres, henv, hpan,
    hroom, hsv, hchn, ?_, ?_, hI.fo, hbs, hits⟩
  · intro hm; exact hI.pm hm
  · refine hI.agr.trans (Agrees.of_memFrame hmf fun a ha => ?_)
    obtain ⟨r, hr, h1, h2⟩ := ha
    obtain ⟨hr8, hro⟩ := hI.keep_apart r hr
    exact Outside.of_sub hro h1 (by omega)

end steps



end Janus.Contracts.PanicSat

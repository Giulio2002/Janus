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

theorem pan_mul (k : Nat) : (BitVec.ofNat 64 (k + 1) - 1#64) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega

theorem pan_shl (k : Nat) (hk : k < 8) : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.shiftLeft_eq]; omega

theorem pan_bit1 (m : Memory) (k : Nat) (hf : rd m (panAt k + 24) / 2 % 2 = 1) :
    (BitVec.ofNat 64 (m.readLE (65792 + (k * 32 + 24)) 8)).getLsbD 1 = true := by
  have : m.readLE (65792 + (k * 32 + 24)) 8 / 2 % 2 = 1 := by
    rw [show 65792 + (k * 32 + 24) = panAt k + 24 by simp only [panAt, B]; omega]; exact hf
  simp only [BitVec.getLsbD_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp; omega

set_option maxHeartbeats 0 in
/-- `RP` after a deferred call that recovered the panic: down to the start of `DROP`. -/
theorem seg_rp_rec (u : State) (x18 k : Nat) (hpc : u.pc = BitVec.ofNat 64 RPa)
    (hal : u.sp.toNat % 16 = 0) (hsp : u.sp.toNat + 104 ≤ 2 ^ 48)
    (hacc : u.mem.accessible u.sp.toNat 96 true = true) (hB : u.mem.accessible B 0x1000 true = true)
    (h18 : u.mem.readLE (u.sp.toNat + 56) 8 = x18) (hmode : u.mem.readLE (u.sp.toNat + 24) 8 = 0)
    (hk : npan u.mem = k + 1) (hk8 : k < 8) (hf : rd u.mem (panAt k + 24) / 2 % 2 = 1) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x394)) u (fun d => d.mem = u.mem ∧ d.sp = u.sp ∧
      d.regs 28 = u.regs 28 ∧ d.regs 18 = BitVec.ofNat 64 x18 ∧ d.regs 6 = BitVec.ofNat 64 B ∧
      d.regs 1 = BitVec.ofNat 64 (u.mem.readLE u.sp.toNat 8)) := by
  have hB' : u.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := u
  dsimp only at *
  simp only [RPa, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [h18, hmode, (show cm.readLE 65536 8 = k + 1 from hk), pan_mul k, pan_shl k hk8, pan_bit1 cm k hf, Bool.true_beq, Bool.false_eq_true]

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
theorem Inv0.ret' {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
    {mode : DeferMode} {x28 x18 : W64} {lr x29 : Nat} {e e' : State} {ch : List PanicRec} {rm ph : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph)
    (hsp : e'.sp = e.sp) (h28 : e'.regs 28 = x28)
    (hag : Agrees e.mem e'.mem ((e.sp.toNat, F.sp) :: frameKeep m0 F items0))
    (henv : Env0 T e'.mem) (hdef : defers0 e'.mem = defers0 e.mem) (hsav : saved0 e'.mem = saved0 e.mem)
    (ch' : List PanicRec) (rm' : Nat) (hpan : panics0 e'.mem = ch') (hroom : rm' ≤ room0 e'.mem) :
    Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e' ch' rm' ph ∧ curItems e'.mem F ph = curItems e.mem F ph := by
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
  refine ⟨?_, hci⟩
  refine ⟨by rw [hsp]; exact hI.sp, hI.al, hI.hi, by rw [hsp, hag.accessible]; exact hI.acc, h28, hI.spB,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hI.hlr, hI.hbd, hI.hres, henv, hpan, hroom,
    fun hm => (saved0_none_iff _).1 (by rw [hsv]; exact (saved0_none_iff _).2 (hI.sv hm)),
    by rw [hdef']; exact hI.chn, hI.agr.trans hagE, hI.fo,
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

theorem Inv0.ret {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
    {mode : DeferMode} {x28 x18 : W64} {lr x29 : Nat} {e e' : State} {ch : List PanicRec} {rm ph : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph)
    (hdr : DeferReturned (P0 T RPa) x28 x18 F.sp (frameKeep m0 F items0) e e')
    (ch' : List PanicRec) (rm' : Nat) (hpan : panics0 e'.mem = ch') (hroom : rm' ≤ room0 e'.mem) :
    Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e' ch' rm' ph ∧ curItems e'.mem F ph = curItems e.mem F ph := by
  obtain ⟨hpc, hsp, h28, h18, hag, henv, hdef, hsav, hrm⟩ := hdr
  exact hI.ret' hsp h28 hag henv hdef hsav ch' rm' hpan hroom

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
  r30 : e.regs 30 = BitVec.ofNat 64 RPa
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
theorem keep_apart_fo {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
    (hfo : FrameOK (P0 T RPa) m0 F items0) :
    ∀ r ∈ keepCore m0 F items0, r.2 = r.1 + 8 ∧
      Outside r.1 8 ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
  intro r hr
  unfold keepCore at hr
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

theorem Inv0.keep_apart (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) :
    ∀ r ∈ keepCore m0 F items0, r.2 = r.1 + 8 ∧
      Outside r.1 8 ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := keep_apart_fo hI.fo

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
    (hsp : e.sp = c.sp) (h28 : e.regs 28 = c.regs 28)
    (hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F))
    (hfm : FrameMem e.mem F mode ph' x18.toNat lr x29)
    (henv : Env0 T e.mem) (hpan : panics0 e.mem = ch) (hroom : rm ≤ room0 e.mem)
    (hsv : mode = .ret → rd e.mem (B + 0x10) = 0)
    (hchn : frameRest F.sp (defers0 e.mem) = frameRest F.sp ds0)
    (hbs : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (e.mem.readLE ba 1), i ∈ openBits (m0.readLE ba 1))
    (hits : ∀ it ∈ curItems e.mem F ph', it ∈ items0) :
    Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 e ch rm ph' := by
  refine ⟨by rw [hsp]; exact hI.sp, hI.al, hI.hi, by rw [hsp, hmf.accessible]; exact hI.acc,
    by rw [h28]; exact hI.r28, hI.spB, hfm, hI.hlr, hI.hbd, hI.hres, henv, hpan,
    hroom, hsv, hchn, ?_, hI.fo, hbs, hits⟩
  · refine hI.agr.trans (Agrees.of_memFrame hmf fun a ha => ?_)
    obtain ⟨r, hr, h1, h2⟩ := ha
    obtain ⟨hr8, hro⟩ := hI.keep_apart r hr
    exact Outside.of_sub hro h1 (by omega)

theorem topBit_mem {b : Nat} (hb : b < 256) (hb0 : 0 < b) : topBit b ∈ openBits b := by
  rw [openBits_top b hb hb0]; exact List.mem_cons_self

theorem step_open (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph)
    (hr18 : c.regs 18 = x18) (hpc : c.pc = BitVec.ofNat 64 eLH) (hph : ph ≠ 0) {ba sa : Nat} (hF : F.openAt = some (ba, sa))
    (hb0 : 0 < c.mem.readLE ba 1) {it : Item} {rest : List Item} (hcur : curItems c.mem F ph = it :: rest) :
    ∃ e, CallSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph it rest e := by
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hcur' := curItems_open hph hF hb0
  have hbl : c.mem.readLE ba 1 < 256 := by have := Memory.readLE_lt c.mem ba 1; simpa using this
  rw [hcur'] at hcur
  obtain ⟨hit, hrest⟩ := List.cons.inj hcur
  have hmem : it ∈ items0 := hI.its it (by rw [hcur', ← hit]; exact List.mem_cons_self)
  generalize hbb : c.mem.readLE ba 1 = b at *
  have hti := topBit_mem hbl hb0
  have hti' : topBit b ∈ openBits (c.mem.readLE ba 1) := by rw [hbb]; exact hti
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hI.item_facts hmem
  obtain ⟨b1, b2, b3, b4, b5⟩ := hI.ba_facts hF
  obtain ⟨s1, s2, s3, s4, s5⟩ := hI.slot_facts hF hti'
  have hfm := hI.fm
  have hs := hI.sp_eq
  obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
  have hw32 := hfm.w32
  rw [hs] at w40 w48 hw32
  have hfn : it.fn = c.mem.readLE (sa + 8 * topBit b) 8 := by rw [← hit]
  have hseg := seg_open c ba sa b it.fn hpc hal hsp hI.acc (by rw [hw32]; exact hph) w40 w48 hbb hb0 b1 b2 s1 s2
    hfn.symm f1 f2 (by omega) s3 (b5 it hmem) f4 f3
  obtain ⟨k, e, hk, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hesp, he26, he28, he18, he29, he30⟩ := hq
  have hflr : ba + 1 ≤ it.fn ∨ it.fn + 8 ≤ ba := (b5 it hmem).symm
  have hread : e.mem.readLE it.fn 8 = c.mem.readLE it.fn 8 := by
    rw [hemem]; exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hrdb : e.mem.readLE ba 1 = b % 2 ^ topBit b := by
    rw [hemem, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : b % 2 ^ topBit b ≤ b := Nat.mod_le _ _
                               simpa using (by omega : b % 2 ^ topBit b < 256))
  have hag : Agrees c.mem e.mem [(B, B + 0x1000)] := by rw [hemem]; exact agrees_writeLE c.mem _ b3
  have hl := P0_laws T RPa
  have hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
    rw [hemem]
    exact MemFrame.of_writeLE c.mem _ (r := (ba, ba + 1))
      (List.mem_append_right _ (by simp [bitsWin, hF])) (Nat.le_refl _) (Nat.le_refl _)
  have hdef : defers0 e.mem = defers0 c.mem := hl.defers_frame _ _ 0 hag
  have hpan : panics0 e.mem = ch := by rw [← hI.pan]; exact hl.panics_frame _ _ 0 hag
  have hsv : saved0 e.mem = saved0 c.mem := hl.saved_frame _ _ 0 hag
  have hrm : room0 e.mem = room0 c.mem := hl.room_frame _ _ 0 hag
  have hcurE : curItems e.mem F ph = rest := by
    rw [curItems_ne hph]
    unfold frameItems; rw [hF]; simp only
    rw [hrdb, hdef, ← hrest]
    rw [openItems_congr (m := c.mem) (m' := e.mem) (b := b % 2 ^ topBit b) fun i hi => ?_]
    have hi' : i ∈ openBits b := openBits_mod_sub b hbl hb0 i hi
    obtain ⟨q1, q2, q3, q4, q5⟩ := hI.slot_facts hF (by rw [hbb]; exact hi')
    rw [hemem]; exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hRPa : (BitVec.ofNat 64 RPa).toNat = RPa := by
    simp only [RPa, E, BitVec.toNat_ofNat]
  have henvE : Env0 T e.mem := by rw [hemem]; exact env0_of_outside hI.env b3
  have hesp' : e.sp.toNat = F.sp - 96 := by rw [hesp, hs]
  refine ⟨e, ⟨⟨k, hk⟩, ?_, he30, hmf, ?_, ?_, ?_, hcurE, hsv, ?_, ?_⟩⟩
  · -- the call
    refine ⟨?_, he26, by rw [he28]; exact hI.r28, by rw [he18]; exact hr18, ?_, ?_, ?_, ?_, ?_, ?_, henvE⟩
    · rw [hpe, hread]
    · rw [he29, hesp]
    · rw [hesp']; omega
    · simp only [P0_depth]; rw [hesp']; omega
    · rw [hesp']; omega
    · rw [he30, hRPa]; simp only [RPa, E]
    · rw [he30, hRPa]; simp only [RPa, E]; omega
  · -- the deferBits byte at the call
    intro b' ba' sa' hb' hF'
    rw [← hit] at hb'
    simp only [Option.some.injEq] at hb'
    rw [hF] at hF'
    simp only [Option.some.injEq, Prod.mk.injEq] at hF'
    obtain ⟨rfl, rfl⟩ := hF'
    rw [hrdb, ← hb']
  · -- the invariant
    refine hI.step ph hesp (by rw [he28]) hmf ?_ henvE hpan (by rw [hrm]; exact hI.room)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hemem]
      exact Memory.readLE_writeLE_of_disjoint _ _ (by rw [hs]; omega)
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [hdef]; exact hI.chn
    · rw [hF] at hF'
      simp only [Option.some.injEq, Prod.mk.injEq] at hF'
      obtain ⟨rfl, rfl⟩ := hF'
      rw [hrdb] at hi
      exact hI.bsub ba sa hF i (by rw [hbb]; exact openBits_mod_sub b hbl hb0 i hi)
    · rw [hcurE] at hit'
      exact hI.its it' (by rw [hcur', hrest]; exact List.mem_cons_of_mem _ hit')
  · rw [← hit]; exact hdef
  · exact Nat.le_of_eq hrm.symm
  · right; exact ⟨b % 2 ^ topBit b, ba, sa, by rw [← hit], hF, hph, hrdb⟩

theorem recTake_frame (m : Memory) {j : Nat} (hj : j < 8) (n : Nat) : MemFrame m (recTake m j n) [(B, B + 0x1000)] := by
  rw [recTake_eq]
  have h1 : MemFrame m (m.writeLE (recAt j + 16) 8 1) [(B, B + 0x1000)] :=
    MemFrame.of_writeLE m 1 (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
      (by simp only [recAt, B]; omega) (by simp only [recAt, B]; omega)
  have h2 := h1.writeLE (a := recAt j + 24) (k := 8) 0 (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
    (by simp only [recAt, B]; omega) (by simp only [recAt, B]; omega)
  split
  · exact h2.writeLE (a := B + 8) (k := 8) j (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
      (by simp only [B]; omega) (by simp only [B]; omega)
  · exact (h1.writeLE (a := recAt j + 24) (k := 8) n (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
      (by simp only [recAt, B]; omega) (by simp only [recAt, B]; omega))

theorem popMem_frame (m : Memory) {j : Nat} (hj : j < 8) : MemFrame m (popMem m j) [(B, B + 0x1000)] := by
  unfold popMem
  have h1 : MemFrame m (m.writeLE (recAt j + 16) 8 1) [(B, B + 0x1000)] :=
    MemFrame.of_writeLE m 1 (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
      (by simp only [recAt, B]; omega) (by simp only [recAt, B]; omega)
  exact h1.writeLE (a := B + 8) (k := 8) j (r := (B, B + 0x1000)) (List.mem_singleton.2 rfl)
    (by simp only [B]; omega) (by simp only [B]; omega)

theorem mf_of_priv {m m' : Memory} {F : Frame} (h : MemFrame m m' [(B, B + 0x1000)]) :
    MemFrame m m' ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) :=
  h.mono fun a n ho => by
    simp only [outside_append, P0_priv] at ho; exact ho.1.1

theorem step_rec (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph)
    (hr18 : c.regs 18 = x18) (hpc : c.pc = BitVec.ofNat 64 eLH) (hph : ph = 0) {j n : Nat} (hnd : ndef c.mem = j + 1)
    (hrs : recSp c.mem j = F.sp) (hn : recN c.mem j = n + 1) :
    ∃ e, CallSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph
      { fn := recFn c.mem j n, bits := none, chain := defers0 (recTake c.mem j n) }
      (recItems F.sp (defers0 (recTake c.mem j n))) e := by
  subst hph
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hj : j < 8 := by have := hI.env.ndef_le; omega
  have hn8 : n < 8 := by have := (hI.env.rec j (by omega)).1; omega
  have hcur := rec_call_items hI.env hnd hrs hn
  have hcur0 := (curItems_zero c.mem F).trans hcur
  have hmem : ({ fn := recFn c.mem j n, bits := none, chain := defers0 (recTake c.mem j n) } : Item) ∈ items0 :=
    hI.its _ (by rw [hcur0]; exact List.mem_cons_self)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hI.item_facts hmem
  simp only at f1 f2 f3 f4 f5 f6
  have hs := hI.sp_eq
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  rw [hs] at hw0 hw32
  have hfr := recTake_frame c.mem hj n
  have hfnr : (recTake c.mem j n).readLE (recFn c.mem j n) 8 = c.mem.readLE (recFn c.mem j n) 8 :=
    hfr.readLE _ _ (by simpa using f5)
  have hseg := seg_rec_call c j n (recFn c.mem j n) hpc hal hsp hI.acc hI.env.acc hw32 hnd hj
    (by rw [hrs, hw0]) hn hn8 rfl f1 f2 (by rw [hfnr]; exact f4) (by rw [hfnr]; exact f3)
  obtain ⟨k, e, hk, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hesp, he26, he28, he18, he29, he30⟩ := hq
  have hl := P0_laws T RPa
  have hRPa : (BitVec.ofNat 64 RPa).toNat = RPa := by
    simp only [RPa, E, BitVec.toNat_ofNat]
  have hesp' : e.sp.toNat = F.sp - 96 := by rw [hesp, hs]
  have henvE : Env0 T e.mem := by rw [hemem]; exact env0_recTake hI.env hnd hn
  have hmf := mf_of_priv (T := T) (F := F) (hemem ▸ hfr)
  have hpan : panics0 e.mem = ch := by rw [hemem, panics0_recTake hj]; exact hI.pan
  have hsv : saved0 e.mem = saved0 c.mem := by rw [hemem]; exact saved0_recTake hj
  have hrm : room0 c.mem ≤ room0 e.mem := by rw [hemem]; exact room0_recTake hI.env hnd hn
  have hdef : defers0 e.mem = defers0 (recTake c.mem j n) := by rw [hemem]
  have hcurE : curItems e.mem F 0 = recItems F.sp (defers0 (recTake c.mem j n)) := by
    rw [curItems_zero, hdef]
  refine ⟨e, ⟨⟨k, hk⟩, ?_, he30, hmf, ?_, ?_, hdef, hcurE, hsv, hrm, Or.inl ⟨rfl, rfl⟩⟩⟩
  · refine ⟨?_, he26, by rw [he28]; exact hI.r28, by rw [he18]; exact hr18, ?_, ?_, ?_, ?_, ?_, ?_, henvE⟩
    · rw [hpe, hemem]
    · rw [he29, hesp]
    · rw [hesp']; omega
    · simp only [P0_depth]; rw [hesp']; omega
    · rw [hesp']; omega
    · rw [he30, hRPa]; simp only [RPa, E]
    · rw [he30, hRPa]; simp only [RPa, E]; omega
  · intro b' ba' sa' hb'; simp at hb'
  · refine hI.step 0 hesp (by rw [he28]) hmf ?_ henvE hpan (Nat.le_trans hI.room hrm)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hemem]
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; rw [hs]; have := hI.spB; omega)
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [hdef, ← rec_call_rest hI.env hnd hrs hn]; exact hI.chn
    · have hbr : e.mem.readLE ba' 1 = c.mem.readLE ba' 1 := by
        rw [hemem]; exact hfr.readLE _ _ (by
          have := (hI.ba_facts hF').2.2.1
          simpa using this)
      exact hI.bsub ba' sa' hF' i (by rw [← hbr]; exact hi)
    · rw [hcurE] at hit'
      have := hI.its it' (by rw [hcur0]; exact List.mem_cons_of_mem _ hit')
      exact this

/-- A silent step of the loop (`TOREC`, `POPREC`): control returns to the loop head, nothing is called. -/
structure SilentSt (p : Program) (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item)
    (ds0 : List DeferRec) (mode : DeferMode) (x28 x18 : W64) (lr x29 : Nat) (c : State)
    (ch : List PanicRec) (rm ph ph2 : Nat) (c2 : State) : Prop where
  steps : ∃ k, Program.Steps p c k c2
  pc : c2.pc = BitVec.ofNat 64 eLH
  r18 : c2.regs 18 = x18
  inv : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c2 ch rm ph2
  cur : curItems c2.mem F ph2 = curItems c.mem F ph
  mf : MemFrame c.mem c2.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F)
  sv : saved0 c2.mem = saved0 c.mem
  meas : (if ph2 = 0 then 0 else 1) * 9 + ndef c2.mem < (if ph = 0 then 0 else 1) * 9 + ndef c.mem

theorem step_torec (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph)
    (hr18 : c.regs 18 = x18) (hpc : c.pc = BitVec.ofNat 64 eLH) (hph : ph ≠ 0) {ba sa : Nat} (hF : F.openAt = some (ba, sa))
    (hb : c.mem.readLE ba 1 = 0) :
    ∃ c2, SilentSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph 0 c2 := by
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  obtain ⟨b1, b2, b3, b4, b5⟩ := hI.ba_facts hF
  have hs := hI.sp_eq
  have hfm := hI.fm
  obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
  have hw32 := hfm.w32
  rw [hs] at w40 w48 hw32
  have hseg := seg_torec c ba hpc hal hsp hI.acc (by rw [hw32]; exact hph) w40 hb b1 b2
  have hseg2 := reachesRet_mono hseg fun e he => he
  obtain ⟨k1, e, hk1, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hesp, he28, he18⟩ := hq
  have hback := seg_back e (Or.inl hpe)
  obtain ⟨k2, c2, hk2, hpc2, hq2⟩ := reachesRet_transfer hp hback
  obtain ⟨hmem2, hsp2, hregs2⟩ := hq2
  have hl := P0_laws T RPa
  have hnb : Outside (c.sp.toNat + 32) 8 [(B, B + 0x1000)] := by
    simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega
  have hm2 : c2.mem = c.mem.writeLE (c.sp.toNat + 32) 8 0 := by rw [hmem2, hemem]
  have hag : Agrees c.mem c2.mem [(B, B + 0x1000)] := by rw [hm2]; exact agrees_writeLE c.mem _ hnb
  have hmf : MemFrame c.mem c2.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
    rw [hm2]
    exact MemFrame.of_writeLE c.mem _ (r := (F.sp - 256, F.sp - 8))
      (List.mem_append_left _ (List.mem_append_right _ (by simp [rtWin, P0_depth]))) (by omega) (by omega)
  have hdef : defers0 c2.mem = defers0 c.mem := hl.defers_frame _ _ 0 hag
  have hpan : panics0 c2.mem = ch := by rw [← hI.pan]; exact hl.panics_frame _ _ 0 hag
  have hsv : saved0 c2.mem = saved0 c.mem := hl.saved_frame _ _ 0 hag
  have hrm : room0 c2.mem = room0 c.mem := hl.room_frame _ _ 0 hag
  have hcur : curItems c2.mem F 0 = curItems c.mem F ph := by
    rw [curItems_zero, curItems_open_zero hph hF hb, hdef]
  have hndef : ndef c2.mem = ndef c.mem := by
    simp only [ndef]; rw [hm2]
    exact rd_w (by have := hI.spB; simp only [B] at *; omega)
  have hrdk : ∀ k, (k + 8 ≤ 32 ∨ 40 ≤ k) → c2.mem.readLE (F.sp - 96 + k) 8 = c.mem.readLE (F.sp - 96 + k) 8 := by
    intro k hk; rw [hm2]; exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨c2, ⟨⟨k1 + k2, hk1.trans hk2⟩, hpc2, by rw [hregs2, he18]; exact hr18, ?_, hcur, hmf, hsv, ?_⟩⟩
  · refine hI.step 0 (by rw [hsp2, hesp]) (by rw [hregs2, he28]) hmf ?_
      (by rw [hm2]; exact env0_of_outside hI.env hnb) hpan (by rw [hrm]; exact hI.room)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · have := hrdk 0 (Or.inl (by omega)); simpa using this.trans hfm.w0
      · exact (hrdk 8 (Or.inl (by omega))).trans hfm.w8
      · exact (hrdk 16 (Or.inl (by omega))).trans hfm.w16
      · exact (hrdk 24 (Or.inl (by omega))).trans hfm.w24
      · show c2.mem.readLE (F.sp - 96 + 32) 8 = 0
        rw [hm2, hs]; rw [Memory.readLE_writeLE_self]
      · intro ba' sa' hF'
        exact ⟨(hrdk 40 (Or.inr (by omega))).trans (hfm.w40 ba' sa' hF').1,
          (hrdk 48 (Or.inr (by omega))).trans (hfm.w40 ba' sa' hF').2⟩
      · exact (hrdk 56 (Or.inr (by omega))).trans hfm.w56
      · intro hm
        exact ⟨(hrdk 64 (Or.inr (by omega))).trans (hfm.w64 hm).1,
          (hrdk 72 (Or.inr (by omega))).trans (hfm.w64 hm).2⟩
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [hdef]; exact hI.chn
    · have hbr : c2.mem.readLE ba' 1 = c.mem.readLE ba' 1 := by
        rw [hm2]; exact Memory.readLE_writeLE_of_disjoint _ _ (by have := (hI.ba_facts hF').2.2.2.1; omega)
      exact hI.bsub ba' sa' hF' i (by rw [← hbr]; exact hi)
    · rw [hcur] at hit'; exact hI.its it' hit'
  · rw [hndef]; by_cases h0 : ph = 0
    · exact absurd h0 hph
    · simp [h0]

theorem step_pop (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph)
    (hr18 : c.regs 18 = x18) (hpc : c.pc = BitVec.ofNat 64 eLH) (hph : ph = 0) {j : Nat} (hnd : ndef c.mem = j + 1)
    (hrs : recSp c.mem j = F.sp) (hn : recN c.mem j = 0) :
    ∃ c2, SilentSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph ph c2 := by
  subst hph
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hj : j < 8 := by have := hI.env.ndef_le; omega
  have hs := hI.sp_eq
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  rw [hs] at hw0 hw32
  have hseg := seg_rec_pop c j hpc hal hsp hI.acc hI.env.acc hw32 hnd hj (by rw [hrs, hw0]) hn
  obtain ⟨k1, e, hk1, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hesp, he28, he18⟩ := hq
  have hback := seg_back e (Or.inr hpe)
  obtain ⟨k2, c2, hk2, hpc2, hq2⟩ := reachesRet_transfer hp hback
  obtain ⟨hmem2, hsp2, hregs2⟩ := hq2
  have hm2 : c2.mem = popMem c.mem j := by rw [hmem2, hemem, popMem_eq]
  have hfr := popMem_frame c.mem hj
  have hfr2 : MemFrame c.mem c2.mem [(B, B + 0x1000)] := by rw [hm2]; exact hfr
  have hmf := mf_of_priv (T := T) (F := F) hfr2
  have hpan : panics0 c2.mem = ch := by rw [hm2, panics0_popMem hj]; exact hI.pan
  have hsv : saved0 c2.mem = saved0 c.mem := by rw [hm2]; exact saved0_popMem hj
  have hrm : room0 c.mem ≤ room0 c2.mem := by rw [hm2]; exact room0_popMem hI.env hnd
  have hit := pop_items hI.env hnd hrs hn
  have hcur : curItems c2.mem F 0 = curItems c.mem F 0 := by
    rw [curItems_zero, curItems_zero, hm2, hit.1]
  have hndef : ndef c2.mem = j := by
    rw [hm2]; simp only [popMem, ndef, rd]; rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                               omega)
  refine ⟨c2, ⟨⟨k1 + k2, hk1.trans hk2⟩, hpc2, by rw [hregs2, he18]; exact hr18, ?_, hcur, hmf, hsv, ?_⟩⟩
  · refine hI.step 0 (by rw [hsp2, hesp]) (by rw [hregs2, he28]) hmf ?_
      (by rw [hm2]; exact env0_popMem hI.env hnd) hpan (Nat.le_trans hI.room hrm)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hm2]
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; rw [hs]; have := hI.spB; omega)
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [← hI.chn, hm2, ← hit.2]
    · have hbr : c2.mem.readLE ba' 1 = c.mem.readLE ba' 1 := by
        rw [hm2]; exact hfr.readLE _ _ (by
          have := (hI.ba_facts hF').2.2.1
          simpa using this)
      exact hI.bsub ba' sa' hF' i (by rw [← hbr]; exact hi)
    · rw [hcur] at hit'; exact hI.its it' hit'
  · rw [hndef, hnd]; simp

theorem step_fin (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph)
    (hr18 : c.regs 18 = x18) (hpc : c.pc = BitVec.ofNat 64 eLH) (hph : ph = 0)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) :
    ∃ k d, Program.Steps p c k d ∧ d.mem = c.mem ∧ d.regs 28 = x28 ∧ d.regs 18 = x18 ∧
      (mode = .ret → d.pc = BitVec.ofNat 64 lr ∧ d.sp = BitVec.ofNat 64 F.sp ∧ d.regs 29 = BitVec.ofNat 64 x29) ∧
      (mode ≠ .ret → d.pc = BitVec.ofNat 64 RPa ∧ d.sp = BitVec.ofNat 64 F.bound) := by
  subst hph
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hs := hI.sp_eq
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  have hw8 := hfm.w8
  have hw24 := hfm.w24
  rw [hs] at hw0 hw32 hw8 hw24
  have hend' : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ j < 8 ∧ recSp c.mem j ≠ c.mem.readLE c.sp.toNat 8 := by
    rcases hend with h | ⟨j, hj, hne⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by have := hI.env.ndef_le; omega, by rw [hw0]; exact hne⟩
  have hlrb : mode = .ret → c.mem.readLE (c.sp.toNat + 64) 8 % 4 = 0 ∧ c.mem.readLE (c.sp.toNat + 64) 8 < 2 ^ 48 := by
    intro hm
    have h := (hfm.w64 hm).1
    rw [hs] at h
    rw [h]; exact hI.hlr hm
  have hfsp : c.mem.readLE c.sp.toNat 8 < 2 ^ 64 := by
    have := Memory.readLE_lt c.mem c.sp.toNat 8
    have h : (256:Nat)^8 = 2^64 := by decide
    omega
  have hseg := seg_fin c mode F.bound (c.mem.readLE (c.sp.toNat + 64) 8) (c.mem.readLE (c.sp.toNat + 72) 8) hpc hal hsp
    hI.acc hI.env.acc hw32 hend' hw24 hw8 hI.hbd rfl rfl hfsp hlrb
  obtain ⟨k, d, hk, hpd, hd1, hd2, hd3, hd4⟩ := reachesRet_transfer hp hseg
  refine ⟨k, d, hk, hd1, by rw [hd2]; exact hI.r28, by rw [hd3]; exact hr18, fun hm => ?_, fun hm => ?_⟩
  · subst hm
    have h64 := (hfm.w64 rfl).1; have h72 := (hfm.w64 rfl).2
    rw [hs] at h64 h72
    simp only [reduceIte] at hpd hd4
    rw [h64] at hpd; rw [h72] at hd4; rw [hw0] at hd4
    exact ⟨hpd, hd4.1, hd4.2⟩
  · have hne : ¬ mode = .ret := hm
    simp only [hne, reduceIte] at hpd hd4
    exact ⟨hpd, hd4⟩

theorem step_recover (hp : EngineAt p) {u : State}
    (hI : Inv0 T m0 F items0 ds0 .panic x28 x18 lr x29 u ch rm ph)
    (hpc : u.pc = BitVec.ofNat 64 RPa) {k : Nat} (hk : npan u.mem = k + 1) (hk8 : k < 8)
    (hf : rd u.mem (panAt k + 24) / 2 % 2 = 1) :
    ∃ k' d, Program.Steps p u k' d ∧ d.pc = BitVec.ofNat 64 F.resume ∧ d.sp = BitVec.ofNat 64 F.sp ∧
      d.regs 29 = d.sp - 8 ∧ d.regs 28 = x28 ∧ d.regs 18 = x18 ∧
      MemFrame u.mem d.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F) ∧ Env0 T d.mem ∧
      panics0 d.mem = (panics0 u.mem).dropWhile (·.start ≤ F.sp) ∧ defers0 d.mem = defers0 u.mem ∧
      room0 u.mem ≤ room0 d.mem ∧
      ((ph ≠ 0 ∧ ∃ ba sa, F.openAt = some (ba, sa) ∧ u.mem.readLE ba 1 ≠ 0) ∧ saved0 d.mem = F.openAt ∨
        ¬ (ph ≠ 0 ∧ ∃ ba sa, F.openAt = some (ba, sa) ∧ u.mem.readLE ba 1 ≠ 0) ∧ saved0 d.mem = none) := by
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hs := hI.sp_eq
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw16 := hfm.w16
  have hw24 := hfm.w24
  have hw32 := hfm.w32
  have hw56 := hfm.w56
  rw [hs] at hw0 hw16 hw24 hw32 hw56
  have hmode : u.mem.readLE (u.sp.toNat + 24) 8 = 0 := by rw [hw24]; rfl
  have hfsp64 : F.sp < 2 ^ 64 := by have := hI.hi; omega
  -- RP to DROP
  have h1 := seg_rp_rec u x18.toNat k hpc hal hsp hI.acc hI.env.acc hw56 hmode hk hk8 hf
  obtain ⟨k1, d1, hk1, hpd1, hq1⟩ := reachesRet_transfer hp h1
  obtain ⟨hm1, hsp1, h281, h181, h61, h11⟩ := hq1
  rw [hw0] at h11
  -- DROP
  have h2 := seg_drop F.sp hfsp64 (k + 1) d1 hpd1 h61 h11 (by rw [hm1]; exact hk) (by omega)
    (by rw [hm1]; exact hI.env.acc)
  obtain ⟨k2, d2, hk2, hpd2, hq2⟩ := reachesRet_transfer hp h2
  obtain ⟨hsp2, h282, h182, h62, h12, hmf2, hnp2⟩ := hq2
  rw [hm1] at hmf2 hnp2
  have hspB := hI.spB
  have hfrOut : ∀ kk, kk + 8 ≤ 96 → Outside (u.sp.toNat + kk) 8 [(B, B + 8)] := by
    intro kk hk; simp only [outside_cons, outside_nil, and_true]; simp only [B] at *; omega
  have hsp21 : d2.sp = u.sp := by rw [hsp2, hsp1]
  have hrdf : ∀ kk, kk + 8 ≤ 96 → d2.mem.readLE (u.sp.toNat + kk) 8 = u.mem.readLE (u.sp.toNat + kk) 8 :=
    fun kk hk => hmf2.readLE _ _ (hfrOut kk hk)
  have hres : d2.mem.readLE (d2.sp.toNat + 16) 8 = F.resume := by
    rw [hsp21, hrdf 16 (by omega)]; exact hw16
  have hph' : d2.mem.readLE (d2.sp.toNat + 32) 8 = ph := by
    rw [hsp21, hrdf 32 (by omega)]; exact hw32
  have hb256' : d2.mem.readLE (d2.mem.readLE (d2.sp.toNat + 40) 8) 1 < 256 := by
    have := Memory.readLE_lt d2.mem (d2.mem.readLE (d2.sp.toNat + 40) 8) 1; simpa using this
  have hsa64 : d2.mem.readLE (d2.sp.toNat + 48) 8 < 2 ^ 64 := by
    have := Memory.readLE_lt d2.mem (d2.sp.toNat + 48) 8
    have h : (256:Nat)^8 = 2^64 := by decide
    omega
  have hph64 : ph < 2 ^ 64 := by
    rw [← hw32]
    have := Memory.readLE_lt u.mem (u.sp.toNat + 32) 8
    have h : (256:Nat)^8 = 2^64 := by decide
    omega
  have h3 := seg_dropped d2 F.sp F.resume ph (d2.mem.readLE (d2.sp.toNat + 40) 8)
    (d2.mem.readLE (d2.sp.toNat + 48) 8) hpd2 h62 h12 (by rw [hsp21]; exact hal) (by rw [hsp21]; omega)
    (by rw [hmf2.accessible, hsp21]; exact hI.acc) (by rw [hmf2.accessible]; exact hI.env.acc) hres
    hI.hres.1 hI.hres.2 hph' rfl rfl (fun hne => by
      have hsome := hfm.hph hne
      obtain ⟨⟨ba, sa⟩, hF⟩ : ∃ q, F.openAt = some q := by
        cases hq : F.openAt with
        | none => rw [hq] at hsome; simp at hsome
        | some q => exact ⟨q, rfl⟩
      obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
      rw [hs] at w40 w48
      have hba : d2.mem.readLE (d2.sp.toNat + 40) 8 = ba := by rw [hsp21, hrdf 40 (by omega)]; exact w40
      obtain ⟨b1, b2, b3, b4, -⟩ := hI.ba_facts hF
      rw [hba]
      refine ⟨b1, by rw [hmf2.accessible]; exact Memory.accessible_weaken _ b2, ?_⟩
      have := b3; simp only [outside_cons, outside_nil, and_true] at this; omega)
    hfsp64 hph64 hsa64 hb256' (by rw [hsp21]; simp only [B] at *; omega)
  obtain ⟨k3, d3, hk3, hpd3, hq3⟩ := reachesRet_transfer hp h3
  obtain ⟨hsp3, h293, h283, h183, hmf3, hsv3⟩ := hq3
  have hsub3 : ∀ a n, Outside a n RecWords → Outside a n [(B, B + 8)] ∧ Outside a n [(B + 0x10, B + 0x28)] := by
    intro a n h; simp only [RecWords, outside_cons, outside_nil, and_true] at h ⊢; exact h
  have hfRec : MemFrame u.mem d3.mem RecWords := hmf2.trans hmf3 hsub3
  have hnpd3 : npan d3.mem = npan d2.mem := by
    simp only [npan]
    exact hmf3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; simp only [B]; omega)
  have hnpd2 : npan d2.mem = dropCount u.mem F.sp (k + 1) := hnp2
  have hD := dropCount_le u.mem F.sp (k + 1)
  have hrec := recov_frame hI.env hfRec (by rw [hnpd3, hnpd2, hk]; exact hD)
  have hx18 : BitVec.ofNat 64 x18.toNat = x18 := by simp
  have hmfr : MemFrame u.mem d3.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F) := hfRec.mono fun a n h => by
    simp only [outside_append, P0_priv, outside_cons, outside_nil, and_true, RecWords] at h ⊢
    have := h.1; simp only [B] at *; omega
  have hmfr' : MemFrame u.mem d3.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F) := hmfr
  refine ⟨k1 + (k2 + k3), d3, hk1.trans (hk2.trans hk3), hpd3, hsp3, h293, ?_, ?_, hmfr', hrec.1, ?_, hrec.2.1,
    hrec.2.2.1, ?_⟩
  · rw [h283, h282, h281]; exact hI.r28
  · rw [h183, h182, h181]; exact hx18.trans rfl
  · rw [panics0_eq, panics0_eq, hnpd3, hnpd2, hk]
    have hmin1 : min (k + 1) 8 = k + 1 := Nat.min_eq_left (by omega)
    have hmin2 : min (dropCount u.mem F.sp (k + 1)) 8 = dropCount u.mem F.sp (k + 1) := Nat.min_eq_left (by omega)
    rw [hmin1, hmin2, hrec.2.2.2 _ (by omega)]
    exact panList_dropCount u.mem F.sp (k + 1)
  · -- the saved state
    by_cases hph0 : ph = 0
    · right
      refine ⟨fun h => h.1 hph0, ?_⟩
      rw [saved0_eq]
      have := hsv3; simp only [hph0, ne_eq, not_true_eq_false, false_and, if_false] at this
      rw [this]; simp
    · obtain ⟨⟨ba, sa⟩, hF⟩ : ∃ q, F.openAt = some q := by
        have hsome := hfm.hph hph0
        cases hq : F.openAt with
        | none => rw [hq] at hsome; simp at hsome
        | some q => exact ⟨q, rfl⟩
      obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
      rw [hs] at w40 w48
      have hba : d2.mem.readLE (d2.sp.toNat + 40) 8 = ba := by rw [hsp21, hrdf 40 (by omega)]; exact w40
      have hsa : d2.mem.readLE (d2.sp.toNat + 48) 8 = sa := by rw [hsp21, hrdf 48 (by omega)]; exact w48
      obtain ⟨b1, b2, b3, b4, -⟩ := hI.ba_facts hF
      have hbyte : d2.mem.readLE ba 1 = u.mem.readLE ba 1 := by
        refine hmf2.readLE _ _ ?_
        have := b3; simp only [outside_cons, outside_nil, and_true] at this ⊢; simp only [B] at *; omega
      rw [hba, hsa, hbyte] at hsv3
      by_cases hb0 : u.mem.readLE ba 1 = 0
      · right
        refine ⟨fun h => ?_, ?_⟩
        · obtain ⟨-, ba', sa', hF', hne⟩ := h
          rw [hF] at hF'; simp only [Option.some.injEq, Prod.mk.injEq] at hF'
          obtain ⟨rfl, rfl⟩ := hF'; exact hne hb0
        · rw [saved0_eq]
          have := hsv3; simp only [hph0, hb0, ne_eq, not_false_eq_true, true_and, not_true_eq_false, if_false] at this
          rw [this]; simp
      · left
        refine ⟨⟨hph0, ba, sa, hF, hb0⟩, ?_⟩
        rw [saved0_eq]
        have := hsv3; simp only [hph0, hb0, ne_eq, not_false_eq_true, and_self, if_true] at this
        obtain ⟨t1, t2, t3⟩ := this
        rw [if_neg (by rw [t1]; simp), t2, t3, hF]

theorem panics0_cons {m : Memory} (h : Env0 T m) {r : PanicRec} {rs : List PanicRec}
    (hp : panics0 m = r :: rs) : ∃ k, npan m = k + 1 ∧ k < 8 ∧ r = decPan m k ∧ rs = panList m k := by
  rw [panics0_eq] at hp
  have h8 := h.npan_le
  cases hnp : npan m with
  | zero => rw [hnp] at hp; simp [panList] at hp
  | succ k =>
    rw [hnp, Nat.min_eq_left (by rw [hnp] at h8; omega)] at hp
    have := List.cons.inj hp
    exact ⟨k, rfl, by rw [hnp] at h8; omega, this.1.symm, this.2.symm⟩

theorem decPan_recovered (m : Memory) (k : Nat) :
    (decPan m k).recovered = (rd m (panAt k + 24) / 2 % 2 == 1) := rfl

/-- From `RP` back to the loop head (a call that left the panic chain alone). -/
theorem step_rp (hp : EngineAt p) {u : State} (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 u ch rm ph)
    (hpc : u.pc = BitVec.ofNat 64 RPa)
    (hcase : mode ≠ .panic ∨ ∃ r rs, ch = r :: rs ∧ r.recovered = false) :
    ∃ k c', Program.Steps p u k c' ∧ c'.pc = BitVec.ofNat 64 eLH ∧ c'.mem = u.mem ∧ c'.regs 18 = x18 ∧
      Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c' ch rm ph := by
  obtain ⟨hal, hsp, hsp96⟩ := hI.spw
  have hs := hI.sp_eq
  have hfm := hI.fm
  have hw24 := hfm.w24
  have hw56 := hfm.w56
  rw [hs] at hw24 hw56
  have hcase' : u.mem.readLE (u.sp.toNat + 24) 8 ≠ 0 ∨ (u.mem.readLE (u.sp.toNat + 24) 8 = 0 ∧
      ∃ k, npan u.mem = k + 1 ∧ k < 8 ∧ rd u.mem (panAt k + 24) / 2 % 2 = 0) := by
    cases mode with
    | panic =>
      right
      refine ⟨by rw [hw24]; rfl, ?_⟩
      rcases hcase with hc | ⟨r, rs, hch, hr⟩
      · exact absurd rfl hc
      · have := hI.pan; rw [hch] at this
        obtain ⟨k, hk, hk8, hr', -⟩ := panics0_cons hI.env this
        refine ⟨k, hk, hk8, ?_⟩
        rw [hr', decPan_recovered] at hr
        simp only [beq_eq_false_iff_ne, ne_eq] at hr
        omega
    | goexit => left; rw [hw24]; simp [modeCode]
    | ret => left; rw [hw24]; simp [modeCode]
  have hseg := seg_rp_lh u x18.toNat hpc hal hsp hI.acc hI.env.acc hw56 hcase'
  obtain ⟨k, c', hk, hpc', hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hm, hsp', h28, h18⟩ := hq
  refine ⟨k, c', hk, hpc', hm, by rw [h18]; simp, ?_⟩
  have := hI.step (c := u) (e := c') ph (by rw [hsp']) (by rw [h28]) (by rw [hm]; exact MemFrame.refl _ _)
    (by rw [hm]; exact hfm) (by rw [hm]; exact hI.env) (by rw [hm]; exact hI.pan) (by rw [hm]; exact hI.room)
    (fun h => by rw [hm]; exact hI.sv h) (by rw [hm]; exact hI.chn) (fun ba sa hF => by rw [hm]; exact hI.bsub ba sa hF)
    (fun it hit => by rw [hm] at hit; exact hI.its it hit)
  exact this

/-- The panic chain's top entry is not recovered or a goexit (what the loop needs of `ch` in panic mode). -/
def PanOK (mode : DeferMode) (ch : List PanicRec) : Prop :=
  mode = .panic → ∃ r rs, ch = r :: rs ∧ r.recovered = false ∧ r.goexit = false

theorem ofNat_toNat_self (x : W64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- A deferred call, and everything after it: the model engine's loop reaches the call, and for every
way the call may end the loop goes on (or recovers). -/
theorem engine_call (hp : EngineAt p)
    {Fin : List PanicRec → Nat → State → State → Prop}
    (hFin : ∀ (ch : List PanicRec) (rm : Nat) (c c' d : State),
      MemFrame c.mem c'.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) → Fin ch rm c' d → Fin ch rm c d)
    (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph) (hpm : PanOK mode ch)
    {it : Item} {rest : List Item} {e : State}
    (cs : CallSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph it rest e)
    (IH : ∀ (c' : State) (ch' : List PanicRec) (rm' ph' : Nat), c'.pc = BitVec.ofNat 64 eLH → c'.regs 18 = x18 →
      Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c' ch' rm' ph' → PanOK mode ch' → curItems c'.mem F ph' = rest →
      Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch' rm' rest c') :
    Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch rm (it :: rest) c := by
  rw [Engine_cons]
  obtain ⟨k, hk⟩ := cs.steps
  have hRP : ∀ e' : State, e'.pc = e.regs 30 → e'.pc = BitVec.ofNat 64 RPa := fun e' h => by rw [h, cs.r30]
  refine ⟨k, e, hk, cs.call, cs.mf, cs.bits, cs.chain, cs.inv.pan, cs.inv.room, ?_, ?_, ?_⟩
  · -- the return point and the saved state
    split
    · rename_i hret
      refine ⟨rfl, (saved0_none_iff _).2 (cs.inv.sv hret)⟩
    · refine ⟨?_, cs.sv⟩
      show RPa = (e.regs 30).toNat
      rw [cs.r30]; simp only [RPa, E, BitVec.toNat_ofNat]
  · -- the call returned
    intro e' hdr
    have hroomE : room0 e.mem ≤ room0 e'.mem := hdr.2.2.2.2.2.2.2.2
    refine ⟨fun hpan' => ?_, fun hmode r rs hch hq _ => ?_⟩
    · obtain ⟨hI', hci⟩ := cs.inv.ret hdr ch rm hpan' (Nat.le_trans cs.inv.room hroomE)
      obtain ⟨k', c', hk', hpc', hmem', hr18', hI''⟩ := step_rp hp hI' (hRP e' hdr.1)
        (by cases hmode : mode with
            | panic => right; obtain ⟨r, rs, h1, h2, -⟩ := hpm hmode; exact ⟨r, rs, h1, h2⟩
            | goexit => left; simp
            | ret => left; simp)
      have hnx := IH c' ch rm ph hpc' hr18' hI'' hpm (by rw [hmem', hci]; exact cs.cur)
      refine Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' e' c' d (by rw [hmem']; exact MemFrame.refl _ _) hf)
        hk' (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) rfl hnx
    · subst hmode
      have hq' : panics0 e'.mem = { r with recovered := true } :: rs := hq
      obtain ⟨hI', hci⟩ := cs.inv.ret hdr _ rm hq' (Nat.le_trans cs.inv.room hroomE)
      obtain ⟨kk, hk1, hk8, hrr, -⟩ := panics0_cons hI'.env hq'
      have hflag : rd e'.mem (panAt kk + 24) / 2 % 2 = 1 := by
        have h := congrArg PanicRec.recovered hrr
        rw [decPan_recovered] at h
        simpa using h.symm
      obtain ⟨k', d, hk', hpcd, hsp', hr29, hr28, hr18d, hmf, henvd, hpand, hdefd, hroomd, hsvd⟩ :=
        step_recover hp hI' (hRP e' hdr.1) hk1 hk8 hflag
      refine ⟨k', d, hk', hpcd, hsp', hr29, hr28, hr18d, hmf, henvd, hpand, hdefd, ?_, hroomd⟩
      show saved0 d.mem = _
      rcases cs.recov with ⟨hb, hph0⟩ | ⟨b, ba, sa, hb, hF, hphne, hrdb⟩
      · have : it.bits.getD 0 = 0 := by rw [hb]; rfl
        rw [if_pos this]
        rcases hsvd with ⟨⟨hph, -⟩, -⟩ | ⟨-, h⟩
        · exact absurd hph0 hph
        · exact h
      · have hbyte : e'.mem.readLE ba 1 = b := by
          have := hdr.2.2.2.2.1.readLE (inRanges_tail (by rw [frameKeep_eq]; exact inRanges_bits hF (keepCore m0 F items0)))
          rw [this]; exact hrdb
        by_cases hb0 : b = 0
        · have hg : it.bits.getD 0 = 0 := by rw [hb]; simpa using hb0
          rw [if_pos hg]
          rcases hsvd with ⟨⟨-, ba', sa', hF', hne⟩, -⟩ | ⟨-, h⟩
          · rw [hF] at hF'; simp only [Option.some.injEq, Prod.mk.injEq] at hF'
            obtain ⟨rfl, rfl⟩ := hF'; exact absurd (hbyte.trans hb0) hne
          · exact h
        · have hg : ¬ it.bits.getD 0 = 0 := by rw [hb]; simpa using hb0
          rw [if_neg hg]
          rcases hsvd with ⟨-, h⟩ | ⟨hn, -⟩
          · exact h
          · exact absurd ⟨hphne, ba, sa, hF, by rw [hbyte]; exact hb0⟩ hn
  · -- a nested panic
    intro hmode u r2 hU hag henv hdef hsav hpan2 hgx hrc hstart hroom
    subst hmode
    obtain ⟨hUpc, hUsp, hU28⟩ := hU
    have hesp : e.sp.toNat < 2 ^ 64 := e.sp.isLt
    have hroom' : rm ≤ room0 u.mem + 1 := hroom
    obtain ⟨hI', hci⟩ := cs.inv.ret' (e' := u) (by rw [hUsp]; simp) (by rw [hU28]; simp) hag henv hdef hsav
      (r2 :: ch) (rm - 1) hpan2 (by omega)
    have hpm2 : PanOK .panic (r2 :: ch) := fun _ => ⟨r2, ch, rfl, hrc, hgx⟩
    obtain ⟨k', c', hk', hpc', hmem', hr18', hI''⟩ := step_rp hp hI' hUpc (Or.inr ⟨r2, ch, rfl, hrc⟩)
    have hnx := IH c' (r2 :: ch) (rm - 1) ph hpc' hr18' hI'' hpm2 (by rw [hmem', hci]; exact cs.cur)
    exact Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' u c' d (by rw [hmem']; exact MemFrame.refl _ _) hf)
      hk' (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) rfl hnx

/-- The model engine's loop meets `Panic.Engine`, for every list of deferred calls. -/
theorem engine_loop (hp : EngineAt p)
    {Fin : List PanicRec → Nat → State → State → Prop}
    (hFin : ∀ (ch : List PanicRec) (rm : Nat) (c c' d : State),
      MemFrame c.mem c'.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) → Fin ch rm c' d → Fin ch rm c d)
    (hfin : ∀ (c : State) (ch : List PanicRec) (rm : Nat), c.pc = BitVec.ofNat 64 eLH → c.regs 18 = x18 →
      Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm 0 → PanOK mode ch →
      (ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) → ∃ k d, Program.Steps p c k d ∧ Fin ch rm c d) :
    ∀ (n : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat), (curItems c.mem F ph).length = n →
      c.pc = BitVec.ofNat 64 eLH → c.regs 18 = x18 → Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph →
      PanOK mode ch →
      Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  have inner : ∀ (m : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat),
      (if ph = 0 then 0 else 1) * 9 + ndef c.mem ≤ m → (curItems c.mem F ph).length = n →
      c.pc = BitVec.ofNat 64 eLH → c.regs 18 = x18 → Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph →
      PanOK mode ch →
      Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ihm =>
    intro c ch rm ph hm hn hpc h18 hI hpm
    have silent : ∀ (ph2 : Nat) (c2 : State),
        SilentSt p T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm ph ph2 c2 →
        Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
      intro ph2 c2 ss
      obtain ⟨⟨j, hj⟩, hpc2, hr182, hinv2, hcur2, hmf2, hsv2, hmeas⟩ := ss
      have := ihm _ (by omega) c2 ch rm ph2 (Nat.le_refl _) (by rw [hcur2]; exact hn) hpc2 hr182 hinv2 hpm
      rw [hcur2] at this
      exact Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' c c2 d hmf2 hf) hj hmf2 hsv2 rfl this
    have finc : (ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) → ph = 0 →
        Engine p (P0 T RPa) U0 x28 x18 F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
      intro hend hph0
      subst hph0
      rw [curItems_zero, (fin_items hI.env hend).1, Engine_nil]
      exact hfin c ch rm hpc h18 hI hpm hend
    by_cases hph0 : ph = 0
    · subst hph0
      by_cases hnd : ndef c.mem = 0
      · exact finc (Or.inl hnd) rfl
      · obtain ⟨j, hj⟩ : ∃ j, ndef c.mem = j + 1 := ⟨ndef c.mem - 1, by omega⟩
        by_cases hrs : recSp c.mem j = F.sp
        · cases hnn : recN c.mem j with
          | zero =>
            obtain ⟨c2, ss⟩ := step_pop hp hI h18 hpc rfl hj hrs hnn
            exact silent 0 c2 ss
          | succ n0 =>
            obtain ⟨e, cs⟩ := step_rec hp hI h18 hpc rfl hj hrs hnn
            have hcur := (curItems_zero c.mem F).trans (rec_call_items hI.env hj hrs hnn)
            rw [hcur]
            refine engine_call hp hFin hI hpm cs ?_
            intro c' ch' rm' ph' hpc' h18' hI' hpm' hc'
            have hlt : (curItems c'.mem F ph').length < n := by
              rw [hc', ← hn, hcur]; simp
            exact (ihn _ hlt) c' ch' rm' ph' rfl hpc' h18' hI' hpm' |> fun h => by rw [hc'] at h; exact h
        · exact finc (Or.inr ⟨j, hj, hrs⟩) rfl
    · obtain ⟨⟨ba, sa⟩, hF⟩ : ∃ q, F.openAt = some q := by
        have hsome := hI.fm.hph hph0
        cases hq : F.openAt with
        | none => rw [hq] at hsome; simp at hsome
        | some q => exact ⟨q, rfl⟩
      by_cases hb : c.mem.readLE ba 1 = 0
      · obtain ⟨c2, ss⟩ := step_torec hp hI h18 hpc hph0 hF hb
        exact silent 0 c2 ss
      · have hb0 : 0 < c.mem.readLE ba 1 := Nat.pos_of_ne_zero hb
        have hcur := curItems_open hph0 hF hb0
        obtain ⟨e, cs⟩ := step_open hp hI h18 hpc hph0 hF hb0 hcur
        rw [hcur]
        refine engine_call hp hFin hI hpm cs ?_
        intro c' ch' rm' ph' hpc' h18' hI' hpm' hc'
        have hlt : (curItems c'.mem F ph').length < n := by
          rw [hc', ← hn, hcur]; simp
        exact (ihn _ hlt) c' ch' rm' ph' rfl hpc' h18' hI' hpm' |> fun h => by rw [hc'] at h; exact h
  exact fun c ch rm ph hn hpc h18 hI hpm => inner _ c ch rm ph (Nat.le_refl _) hn hpc h18 hI hpm

/-- `Engine.of_prefix` for `deferreturn`, whose prefix clears the saved state. -/
theorem Engine.of_prefix_ret {p : Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {x28 x18 : W64}
    {F : Frame} {keep : List (Nat × Nat)}
    {Fin : List PanicRec → Nat → State → State → Prop} {c c' : State} {j : Nat}
    (hFin : ∀ ch rm d, Fin ch rm c' d → Fin ch rm c d) (hst : Program.Steps p c j c')
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hrp : P.rp c'.mem x28.toNat = P.rp c.mem x28.toNat) :
    ∀ {ch : List PanicRec} {rm : Nat} {L : List Item},
      Engine p P U x28 x18 F keep .ret Fin ch rm L c' → Engine p P U x28 x18 F keep .ret Fin ch rm L c
  | _, _, [], h => by
    rw [Engine_nil] at h ⊢
    obtain ⟨k, d, hs, hf⟩ := h
    exact ⟨j + k, d, hst.trans hs, hFin _ _ _ hf⟩
  | _, _, it :: rest, h => by
    rw [Engine_cons] at h ⊢
    obtain ⟨k, e, hs, hcall, hmf, hb, hd, hpn, hrm, hrs, hcont, hnest⟩ := h
    refine ⟨j + k, e, hst.trans hs, hcall, hm.trans hmf fun a n h => ⟨h, h⟩, hb, hd, hpn, hrm, ?_,
      hcont, hnest⟩
    rw [if_pos rfl] at hrs ⊢; exact ⟨hrs.1.trans hrp, hrs.2⟩

end steps




end Janus.Contracts.PanicSat

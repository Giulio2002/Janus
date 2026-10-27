import Janus.Contracts.PanicSatAmd64Loop
import Janus.Contracts.PanicSatEngine

/-!
# The amd64 model engine meets the `gopanic`, `Goexit` and `deferreturn` contracts

The induction over the loop of the amd64 model engine (`docs/model/panic_model_amd64.s`, label `LH`)
that `Janus.Contracts.PanicSatEngine` does for the arm64 one: an invariant `Inv0` on the loop state, one
lemma per kind of step, and `engine_loop`, which shows that `PanicAmd64.Engine` holds for the model,
for every list of deferred calls.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Contracts.Panic (DeferMode Frame Item fnItems recItems openItems frameItems frameKeep bitsWin
  frameRecs_above recItems_above)
open Janus.Contracts.PanicSat (modeCode phF curItems clzTop topBit bicTop openBits_top openBits_mod_sub
  recTake dropCount dropCount_le panList_dropCount dropCount_w keepCore frameKeep_eq inRanges_keepCore_fn
  inRanges_keepCore_slot curItems_zero curItems_ne curItems_open curItems_open_zero curItems_congr
  saved0_none_iff inRanges_bits inRanges_tail env0_of_outside outside_of_forall keep_apart_fo
  topBit_mem recTake_frame popMem_frame panics0_cons decPan_recovered)
open Janus.Spec.Map

/-- The model's frame in memory `m` (at `msp = F.sp - 104`): `F.sp`, `F.bound`, `F.resume`, the mode,
the phase and the `deferBits` and slot addresses; in `deferreturn` mode also the caller's return
address, at `msp + 96`. -/
structure FrameMem (m : Memory) (F : Frame) (mode : DeferMode) (ph lr : Nat) : Prop where
  w0 : m.readLE (F.sp - 104) 8 = F.sp
  w8 : m.readLE (F.sp - 104 + 8) 8 = F.bound
  w16 : m.readLE (F.sp - 104 + 16) 8 = F.resume
  w24 : m.readLE (F.sp - 104 + 24) 8 = modeCode mode
  w32 : m.readLE (F.sp - 104 + 32) 8 = ph
  w40 : ∀ ba sa, F.openAt = some (ba, sa) → m.readLE (F.sp - 104 + 40) 8 = ba ∧ m.readLE (F.sp - 104 + 48) 8 = sa
  w96 : mode = .ret → m.readLE (F.sp - 104 + 96) 8 = lr
  hph : ph ≠ 0 → F.openAt.isSome

/-- The loop state of the model (anywhere in the loop or at a deferred call's return point). `m0`
is the memory at the runtime function's entry, `items0` the calls the loop was entered with, `ds0`
the defer chain then. -/
structure Inv0 (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item) (ds0 : List DeferRec)
    (mode : DeferMode) (g bp : W64) (lr : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat) : Prop where
  al : F.sp % 8 = 0
  hi : F.sp + 8 ≤ 2 ^ 48
  h112 : 112 ≤ F.sp
  acc : c.mem.accessible (F.sp - 112) 104 true = true
  r14 : c.regs 14 = g
  r5 : c.regs 5 = bp
  x15 : c.xmm 15 = 0
  dfc : c.df = false
  spB : F.sp ≤ B ∨ B + 0x1000 + 112 ≤ F.sp
  fm : FrameMem c.mem F mode ph lr
  hlr : mode = .ret → lr < 2 ^ 47 ∧ c.mem.accessible (F.sp - 8) 8 false = true
  hbd : F.bound + 8 < 2 ^ 64
  hres : F.resume < 2 ^ 47
  env : Env0 T c.mem
  pan : panics0 c.mem = ch
  room : rm ≤ room0 c.mem
  sv : mode = .ret → rd c.mem (B + 0x10) = 0
  chn : frameRest F.sp (defers0 c.mem) = frameRest F.sp ds0
  agr : Agrees m0 c.mem (keepCore m0 F items0)
  fo : FrameOK (P0 T RPa) m0 F items0
  bsub : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (c.mem.readLE ba 1), i ∈ openBits (m0.readLE ba 1)
  its : ∀ it ∈ curItems c.mem F ph, it ∈ items0

/-- `c` is at the loop head (or a deferred call's return point) of frame `F`: `RSP` is the engine's
frame, 104 bytes below `F.sp`. -/
def LoopAt (F : Frame) (c : State) : Prop := (c.regs 4).toNat + 104 = F.sp

/-- The state after a deferred call returned (or after a nested panic left it): the invariant
carries over, with the panic chain and the room the caller supplies. -/
theorem Inv0.ret' {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
    {mode : DeferMode} {g bp : W64} {lr : Nat} {e e' : State} {ch : List PanicRec} {rm ph : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode g bp lr e ch rm ph) (he : (e.regs 4).toNat + 112 = F.sp)
    (h14 : e'.regs 14 = g) (h5 : e'.regs 5 = bp) (hx : e'.xmm 15 = 0) (hdf : e'.df = false)
    (hag : Agrees e.mem e'.mem (((e.regs 4).toNat + 8, F.sp) :: frameKeep m0 F items0))
    (henv : Env0 T e'.mem) (hdef : defers0 e'.mem = defers0 e.mem) (hsav : saved0 e'.mem = saved0 e.mem)
    (ch' : List PanicRec) (rm' : Nat) (hpan : panics0 e'.mem = ch') (hroom : rm' ≤ room0 e'.mem) :
    Inv0 T m0 F items0 ds0 mode g bp lr e' ch' rm' ph ∧ curItems e'.mem F ph = curItems e.mem F ph := by
  rw [frameKeep_eq] at hag
  have hagE : Agrees e.mem e'.mem (keepCore m0 F items0) := hag.mono' fun a n h =>
    inRanges_tail (h.append_right _)
  have hfr : ∀ k, k + 8 ≤ 104 → e'.mem.readLE (F.sp - 104 + k) 8 = e.mem.readLE (F.sp - 104 + k) 8 := fun k hk =>
    hag.readLE ⟨((e.regs 4).toNat + 8, F.sp), List.mem_cons_self, by omega, by omega⟩
  have hbyte : ∀ ba sa, F.openAt = some (ba, sa) → e'.mem.readLE ba 1 = e.mem.readLE ba 1 := fun ba sa hF =>
    hag.readLE (inRanges_tail (inRanges_bits hF (keepCore m0 F items0)))
  have hsl : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (e.mem.readLE ba 1),
      e'.mem.readLE (sa + 8 * i) 8 = e.mem.readLE (sa + 8 * i) 8 := fun ba sa hF i hi =>
    hagE.readLE (inRanges_keepCore_slot hF (hI.bsub ba sa hF i hi))
  have hci : curItems e'.mem F ph = curItems e.mem F ph :=
    curItems_congr hdef fun ba sa hF _ => ⟨hbyte ba sa hF, hsl ba sa hF⟩
  have hfm := hI.fm
  refine ⟨⟨hI.al, hI.hi, hI.h112, by rw [hag.accessible]; exact hI.acc, h14, h5, hx, hdf, hI.spB,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hI.hbd, hI.hres, henv, hpan, hroom,
    fun hm => (saved0_none_iff _).1 (by rw [hsav]; exact (saved0_none_iff _).2 (hI.sv hm)),
    by rw [hdef]; exact hI.chn, hI.agr.trans hagE, hI.fo,
    fun ba sa hF i hi => hI.bsub ba sa hF i (by rw [← hbyte ba sa hF]; exact hi),
    fun it hit => hI.its it (by rw [← hci]; exact hit)⟩, hci⟩
  · rw [show F.sp - 104 = F.sp - 104 + 0 from rfl, hfr 0 (by omega)]; exact hfm.w0
  · rw [hfr 8 (by omega)]; exact hfm.w8
  · rw [hfr 16 (by omega)]; exact hfm.w16
  · rw [hfr 24 (by omega)]; exact hfm.w24
  · rw [hfr 32 (by omega)]; exact hfm.w32
  · intro ba sa hF
    rw [hfr 40 (by omega), hfr 48 (by omega)]; exact hfm.w40 ba sa hF
  · intro hm; rw [hfr 96 (by omega)]; exact hfm.w96 hm
  · exact hfm.hph
  · intro hm
    obtain ⟨h1, h2⟩ := hI.hlr hm
    exact ⟨h1, by rw [hag.accessible]; exact h2⟩

theorem Inv0.ret {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
    {mode : DeferMode} {g bp : W64} {lr : Nat} {e e' : State} {ch : List PanicRec} {rm ph : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode g bp lr e ch rm ph) (he : (e.regs 4).toNat + 112 = F.sp)
    (hdr : DeferReturned (P0 T RPa) g F.sp (frameKeep m0 F items0) e e') (h5 : e'.regs 5 = bp)
    (ch' : List PanicRec) (rm' : Nat) (hpan : panics0 e'.mem = ch') (hroom : rm' ≤ room0 e'.mem) :
    Inv0 T m0 F items0 ds0 mode g bp lr e' ch' rm' ph ∧ curItems e'.mem F ph = curItems e.mem F ph := by
  obtain ⟨hpc, hsp, h14, hbp, hx, hdf, hag, henv, hdef, hsav, hrm⟩ := hdr
  exact hI.ret' he h14 h5 hx hdf hag henv hdef hsav ch' rm' hpan hroom


section facts
variable {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item} {ds0 : List DeferRec}
  {mode : DeferMode} {g bp : W64} {lr : Nat} {c : State} {ch : List PanicRec} {rm ph : Nat}

theorem sub8_toNat (x : W64) (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by
  have := x.isLt
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [BitVec.toNat_sub, h8]; omega

theorem RPa_lt : RPa < 2 ^ 47 := by simp only [RPa, E]; omega

theorem rd_RPa (m : Memory) (a : Nat) : (m.writeLE a 8 RPa).readLE a 8 = RPa := by
  rw [Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by have := RPa_lt; omega)

theorem Inv0.item_facts (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) {it : Item}
    (hit : it ∈ items0) :
    it.fn + 8 ≤ 2 ^ 48 ∧ c.mem.accessible it.fn 8 false = true ∧ c.mem.readLE it.fn 8 < 2 ^ 47 ∧
      Outside it.fn 8 [(B, B + 0x1000)] ∧ (it.fn + 8 ≤ F.sp - 256 ∨ F.sp ≤ it.fn) := by
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hI.fo.1.2 it hit
  have h47 := hI.fo.2 it hit
  have hr : c.mem.readLE it.fn 8 = m0.readLE it.fn 8 := hI.agr.readLE (inRanges_keepCore_fn hit)
  refine ⟨h1, ?_, by rw [hr]; exact h47, h5, h6⟩
  rw [hI.agr.accessible]; exact h2

theorem Inv0.ba_facts (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) {ba sa : Nat}
    (hF : F.openAt = some (ba, sa)) :
    ba + 1 ≤ 2 ^ 48 ∧ c.mem.accessible ba 1 true = true ∧ Outside ba 1 [(B, B + 0x1000)] ∧ F.sp ≤ ba ∧
      ∀ it ∈ items0, it.fn + 8 ≤ ba ∨ ba + 1 ≤ it.fn := by
  have h := hI.fo.1.1
  rw [hF] at h
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h
  exact ⟨h1, by rw [hI.agr.accessible]; exact h2, h3, h4, h6⟩

theorem Inv0.slot_facts (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) {ba sa i : Nat}
    (hF : F.openAt = some (ba, sa)) (hi : i ∈ openBits (c.mem.readLE ba 1)) :
    sa + 8 * i + 8 ≤ 2 ^ 48 ∧ c.mem.accessible (sa + 8 * i) 8 false = true ∧
      (sa + 8 * i + 8 ≤ ba ∨ ba + 1 ≤ sa + 8 * i) ∧ F.sp ≤ sa + 8 * i ∧ Outside (sa + 8 * i) 8 [(B, B + 0x1000)] := by
  have h := hI.fo.1.1
  rw [hF] at h
  obtain ⟨-, -, -, -, h5, -⟩ := h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h5 i (hI.bsub ba sa hF i hi)
  exact ⟨a1, by rw [hI.agr.accessible]; exact a2, a3, a4, a5⟩

theorem Inv0.slot_read (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) {ba sa i : Nat}
    (hF : F.openAt = some (ba, sa)) (hi : i ∈ openBits (c.mem.readLE ba 1)) :
    c.mem.readLE (sa + 8 * i) 8 = m0.readLE (sa + 8 * i) 8 :=
  hI.agr.readLE (inRanges_keepCore_slot hF (hI.bsub ba sa hF i hi))

theorem Inv0.spw (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) (hL : (c.regs 4).toNat + 104 = F.sp) :
    (c.regs 4).toNat % 8 = 0 ∧ (c.regs 4).toNat + 104 ≤ 2 ^ 48 ∧ 8 ≤ (c.regs 4).toNat := by
  have := hI.al; have := hI.hi; have := hI.h112; omega

theorem Inv0.acc' (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) (hL : (c.regs 4).toNat + 104 = F.sp) :
    c.mem.accessible ((c.regs 4).toNat - 8) 104 true = true := by
  have : (c.regs 4).toNat - 8 = F.sp - 112 := by omega
  rw [this]; exact hI.acc

end facts

/-- Every range the runtime reads again is apart from what the loop writes (the model's records,
its stack window below the frame, the `deferBits` byte). -/
theorem keep_apart_fo {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
    (hfo : Janus.Contracts.Panic.FrameOK (P0 T RPa) m0 F items0) :
    ∀ r ∈ keepCore m0 F items0, r.2 = r.1 + 8 ∧
      Outside r.1 8 ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
  intro r hr
  unfold keepCore at hr
  rcases List.mem_append.1 hr with hr | hr
  · cases hF : F.openAt with
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

section steps
variable {p : Program} {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
  {ds0 : List DeferRec} {mode : DeferMode} {g bp : W64} {lr : Nat} {c : State}
  {ch : List PanicRec} {rm ph : Nat}

theorem Inv0.keep_apart (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) :
    ∀ r ∈ keepCore m0 F items0, r.2 = r.1 + 8 ∧
      Outside r.1 8 ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := keep_apart_fo hI.fo.1

theorem FrameMem.congr {m m' : Memory} {F : Frame} {mode : DeferMode} {ph lr : Nat}
    (h : FrameMem m F mode ph lr)
    (hk : ∀ k, k + 8 ≤ 104 → m'.readLE (F.sp - 104 + k) 8 = m.readLE (F.sp - 104 + k) 8) :
    FrameMem m' F mode ph lr := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hph⟩
  · have := hk 0 (by omega); simpa using this.trans h.w0
  · exact (hk 8 (by omega)).trans h.w8
  · exact (hk 16 (by omega)).trans h.w16
  · exact (hk 24 (by omega)).trans h.w24
  · exact (hk 32 (by omega)).trans h.w32
  · intro ba sa hF
    exact ⟨(hk 40 (by omega)).trans (h.w40 ba sa hF).1, (hk 48 (by omega)).trans (h.w40 ba sa hF).2⟩
  · intro hm
    exact (hk 96 (by omega)).trans (h.w96 hm)

/-- Moving from one loop state to another: what the loop writes is confined to the model's
records, its stack window and the `deferBits` byte; the caller supplies what changed in the model's
own bookkeeping. -/
theorem Inv0.step (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) {e : State} (ph' : Nat)
    (h14 : e.regs 14 = g) (h5 : e.regs 5 = bp) (hx : e.xmm 15 = 0) (hdf : e.df = false)
    (hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F))
    (hfm : FrameMem e.mem F mode ph' lr)
    (henv : Env0 T e.mem) (hpan : panics0 e.mem = ch) (hroom : rm ≤ room0 e.mem)
    (hsv : mode = .ret → rd e.mem (B + 0x10) = 0)
    (hchn : frameRest F.sp (defers0 e.mem) = frameRest F.sp ds0)
    (hbs : ∀ ba sa, F.openAt = some (ba, sa) → ∀ i ∈ openBits (e.mem.readLE ba 1), i ∈ openBits (m0.readLE ba 1))
    (hits : ∀ it ∈ curItems e.mem F ph', it ∈ items0) :
    Inv0 T m0 F items0 ds0 mode g bp lr e ch rm ph' := by
  refine ⟨hI.al, hI.hi, hI.h112, by rw [hmf.accessible]; exact hI.acc, h14, h5, hx, hdf, hI.spB, hfm,
    fun hm => ⟨(hI.hlr hm).1, by rw [hmf.accessible]; exact (hI.hlr hm).2⟩, hI.hbd, hI.hres, henv, hpan,
    hroom, hsv, hchn, ?_, hI.fo, hbs, hits⟩
  · refine hI.agr.trans (Agrees.of_memFrame hmf fun a ha => ?_)
    obtain ⟨r, hr, h1, h2⟩ := ha
    obtain ⟨hr8, hro⟩ := hI.keep_apart r hr
    exact Outside.of_sub hro h1 (by omega)

/-- The model engine is at the entry of the deferred call `it` (state `e`), reached from the loop
head `c`; the rest of the loop is `rest`. -/
structure CallSt (p : Program) (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item)
    (ds0 : List DeferRec) (mode : DeferMode) (g bp : W64) (lr : Nat) (c : State)
    (ch : List PanicRec) (rm ph : Nat) (it : Item) (rest : List Item) (e : State) : Prop where
  steps : ∃ k, Janus.Amd64.Program.Steps p c k e
  call : DeferCall (P0 T RPa) g F.sp it.fn e
  rsp : (e.regs 4).toNat + 112 = F.sp
  rp : e.mem.readLE (e.regs 4).toNat 8 = RPa
  mf : MemFrame c.mem e.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F)
  bits : ∀ b ba sa, it.bits = some b → F.openAt = some (ba, sa) → e.mem.readLE ba 1 = b
  inv : Inv0 T m0 F items0 ds0 mode g bp lr e ch rm ph
  chain : defers0 e.mem = it.chain
  cur : curItems e.mem F ph = rest
  sv : saved0 e.mem = saved0 c.mem
  rmono : room0 c.mem ≤ room0 e.mem
  recov : (it.bits = none ∧ ph = 0) ∨
    (∃ b ba sa, it.bits = some b ∧ F.openAt = some (ba, sa) ∧ ph ≠ 0 ∧ e.mem.readLE ba 1 = b)

end steps

end Janus.Contracts.PanicSatAmd64

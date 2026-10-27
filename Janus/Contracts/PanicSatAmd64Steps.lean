import Janus.Contracts.PanicSatAmd64Engine


/-!
# The amd64 model engine's loop: one lemma per step

The step lemmas of the induction `engine_loop` (`Janus.Contracts.PanicSatAmd64EngineLoop`) makes over
the amd64 model engine: the open-coded step, the record step, the silent steps (`TOREC`, `POPREC`),
the end of the loop, and the return from a deferred call (`RP`), each from the invariant `Inv0` of
`Janus.Contracts.PanicSatAmd64Engine`. The x86-64 twin of the first half of
`Janus.Contracts.PanicSatEngine`.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Contracts.Panic (DeferMode Frame Item fnItems recItems openItems frameItems frameKeep bitsWin
  frameRecs_above recItems_above)
open Janus.Contracts.PanicSat (modeCode phF curItems clzTop topBit bicTop openBits_top openBits_mod_sub
  recTake dropCount dropCount_le panList_dropCount dropCount_w keepCore frameKeep_eq inRanges_keepCore_fn
  inRanges_keepCore_slot curItems_zero curItems_ne curItems_open curItems_open_zero curItems_congr
  saved0_none_iff inRanges_bits inRanges_tail env0_of_outside outside_of_forall
  topBit_mem recTake_frame popMem_frame panics0_cons decPan_recovered openItems_congr
  rec_call_items rec_call_rest env0_recTake panics0_recTake saved0_recTake room0_recTake env0_popMem
  panics0_popMem saved0_popMem room0_popMem pop_items fin_items recov_frame popMem_eq recTake_eq RecWords popMem)
open Janus.Spec.Map

section steps
variable {p : Program} {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
  {ds0 : List DeferRec} {mode : DeferMode} {g bp : W64} {lr : Nat} {c : State}
  {ch : List PanicRec} {rm ph : Nat}

theorem step_open (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph)
    (hL : (c.regs 4).toNat + 104 = F.sp) (hpc : c.rip = BitVec.ofNat 64 eLH) (hph : ph ≠ 0)
    {ba sa : Nat} (hF : F.openAt = some (ba, sa))
    (hb0 : 0 < c.mem.readLE ba 1) {it : Item} {rest : List Item} (hcur : curItems c.mem F ph = it :: rest) :
    ∃ e, CallSt p T m0 F items0 ds0 mode g bp lr c ch rm ph it rest e := by
  obtain ⟨hal, hsp, h8⟩ := hI.spw hL
  have hacc := hI.acc' hL
  have hcur' := curItems_open hph hF hb0
  have hbl : c.mem.readLE ba 1 < 256 := by have := Janus.Arm64.Memory.readLE_lt c.mem ba 1; simpa using this
  rw [hcur'] at hcur
  obtain ⟨hit, hrest⟩ := List.cons.inj hcur
  have hmem : it ∈ items0 := hI.its it (by rw [hcur', ← hit]; exact List.mem_cons_self)
  generalize hbb : c.mem.readLE ba 1 = b at *
  have hti := topBit_mem hbl hb0
  have hti' : topBit b ∈ openBits (c.mem.readLE ba 1) := by rw [hbb]; exact hti
  obtain ⟨f1, f2, f3, f4, f5⟩ := hI.item_facts hmem
  obtain ⟨b1, b2, b3, b4, b5⟩ := hI.ba_facts hF
  obtain ⟨s1, s2, s3, s4, s5⟩ := hI.slot_facts hF hti'
  have hfm := hI.fm
  have hs : F.sp - 104 = (c.regs 4).toNat := by omega
  obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
  have hw32 := hfm.w32
  rw [hs] at w40 w48 hw32
  have hfn : it.fn = c.mem.readLE (sa + 8 * topBit b) 8 := by rw [← hit]
  have hseg := seg_open c ba sa b it.fn hpc hal hsp h8 hacc (by rw [hw32]; exact hph) w40 w48 hbb hb0 b1 b2 s1 s2
    hfn.symm f1 f2 (by show (c.regs 4).toNat + 96 ≤ ba; omega) s3 (b5 it hmem) f3
  obtain ⟨k, e, hk, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, he4, he2, he14, he5, hex, hedf⟩ := hq
  simp only [rsp] at hemem
  have hesp : (e.regs 4).toNat = F.sp - 112 := by rw [he4, sub8_toNat _ h8]; omega
  have hflr : ba + 1 ≤ it.fn ∨ it.fn + 8 ≤ ba := (b5 it hmem).symm
  have hread : e.mem.readLE it.fn 8 = c.mem.readLE it.fn 8 := by
    rw [hemem]
    refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans
      (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_) <;> omega
  have hrdb : e.mem.readLE ba 1 = b % 2 ^ topBit b := by
    rw [hemem]
    refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans ?_
    · omega
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have : b % 2 ^ topBit b ≤ b := Nat.mod_le _ _
                                 simpa using (by omega : b % 2 ^ topBit b < 256))
  have hnb2 : Outside ((c.regs 4).toNat - 8) 8 [(B, B + 0x1000)] := by
    simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega
  have hag : Agrees c.mem e.mem [(B, B + 0x1000)] := by
    rw [hemem]; exact (agrees_writeLE c.mem _ b3).writeLE _ hnb2
  have hl := P0_laws T RPa
  have hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
    rw [hemem]
    exact (MemFrame.of_writeLE c.mem _ (r := (ba, ba + 1))
      (List.mem_append_right _ (by simp [bitsWin, hF])) (Nat.le_refl _) (Nat.le_refl _)).writeLE (a := (c.regs 4).toNat - 8)
      (k := 8) RPa (r := (F.sp - 256, F.sp - 8))
      (List.mem_append_left _ (List.mem_append_right _ (by simp [rtWin, P0_depth]))) (by omega) (by omega)
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
    rw [hemem]
    refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans
      (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_) <;> omega
  have henvE : Env0 T e.mem := by
    rw [hemem]; exact env0_of_outside (env0_of_outside hI.env b3) hnb2
  have hrp : e.mem.readLE (e.regs 4).toNat 8 = RPa := by
    rw [hemem, show (e.regs 4).toNat = (c.regs 4).toNat - 8 by omega]; exact rd_RPa _ _
  refine ⟨e, ⟨⟨k, hk⟩, ?_, by omega, hrp, hmf, ?_, ?_, ?_, hcurE, hsv, ?_, ?_⟩⟩
  · -- the call
    refine ⟨?_, he2, by rw [he14]; exact hI.r14, by rw [hex]; exact hI.x15, by rw [hedf]; exact hI.dfc,
      by omega, ?_, by omega, by rw [hrp]; exact RPa_lt, henvE⟩
    · rw [hpe, hread]
    · simp only [P0_depth]; omega
  · -- the deferBits byte at the call
    intro b' ba' sa' hb' hF'
    rw [← hit] at hb'
    simp only [Option.some.injEq] at hb'
    rw [hF] at hF'
    simp only [Option.some.injEq, Prod.mk.injEq] at hF'
    obtain ⟨rfl, rfl⟩ := hF'
    rw [hrdb, ← hb']
  · -- the invariant
    refine hI.step ph (by rw [he14]; exact hI.r14) (by rw [he5]; exact hI.r5) (by rw [hex]; exact hI.x15)
      (by rw [hedf]; exact hI.dfc) hmf ?_ henvE hpan (by rw [hrm]; exact hI.room)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hemem]
      refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans
        (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_) <;> omega
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


theorem mf_of_priv {m m' : Memory} {F : Frame} (h : MemFrame m m' [(B, B + 0x1000)]) :
    MemFrame m m' ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) :=
  h.mono fun a n ho => by
    simp only [outside_append, P0_priv] at ho; exact ho.1.1

theorem step_rec (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph)
    (hL : (c.regs 4).toNat + 104 = F.sp) (hpc : c.rip = BitVec.ofNat 64 eLH) (hph : ph = 0)
    {j n : Nat} (hnd : ndef c.mem = j + 1)
    (hrs : recSp c.mem j = F.sp) (hn : recN c.mem j = n + 1) :
    ∃ e, CallSt p T m0 F items0 ds0 mode g bp lr c ch rm ph
      { fn := recFn c.mem j n, bits := none, chain := defers0 (recTake c.mem j n) }
      (recItems F.sp (defers0 (recTake c.mem j n))) e := by
  subst hph
  obtain ⟨hal, hsp, h8⟩ := hI.spw hL
  have hacc := hI.acc' hL
  have hj : j < 8 := by have := hI.env.ndef_le; omega
  have hn8 : n < 8 := by have := (hI.env.rec j (by omega)).1; omega
  have hcur := rec_call_items hI.env hnd hrs hn
  have hcur0 := (curItems_zero c.mem F).trans hcur
  have hmem : ({ fn := recFn c.mem j n, bits := none, chain := defers0 (recTake c.mem j n) } : Item) ∈ items0 :=
    hI.its _ (by rw [hcur0]; exact List.mem_cons_self)
  obtain ⟨f1, f2, f3, f4, f5⟩ := hI.item_facts hmem
  simp only at f1 f2 f3 f4 f5
  have hs : F.sp - 104 = (c.regs 4).toNat := by omega
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  rw [hs] at hw0 hw32
  have hfr := recTake_frame c.mem hj n
  have hfnr : (recTake c.mem j n).readLE (recFn c.mem j n) 8 = c.mem.readLE (recFn c.mem j n) 8 :=
    hfr.readLE _ _ (by simpa using f4)
  have hseg := seg_rec_call c j n (recFn c.mem j n) hpc hal hsp h8 hacc hI.env.acc hw32 hnd hj
    (by rw [hrs, hw0]) hn hn8 rfl f1 f2 (by rw [hfnr]; exact f3)
  obtain ⟨k, e, hk, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, he4, he2, he14, he5, hex, hedf⟩ := hq
  simp only [rsp] at hemem
  have hl := P0_laws T RPa
  have hesp : (e.regs 4).toNat = F.sp - 112 := by rw [he4, sub8_toNat _ h8]; omega
  have hnb2 : Outside ((c.regs 4).toNat - 8) 8 [(B, B + 0x1000)] := by
    simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega
  have henvE : Env0 T e.mem := by
    rw [hemem]; exact env0_of_outside (env0_recTake hI.env hnd hn) hnb2
  have hmf : MemFrame c.mem e.mem ([(B, B + 0x1000)] ++ rtWin (P0 T RPa) F ++ bitsWin F) := by
    rw [hemem]
    exact (mf_of_priv (T := T) (F := F) hfr).writeLE (a := (c.regs 4).toNat - 8)
      (k := 8) RPa (r := (F.sp - 256, F.sp - 8))
      (List.mem_append_left _ (List.mem_append_right _ (by simp [rtWin, P0_depth]))) (by omega) (by omega)
  have hag : Agrees (recTake c.mem j n) e.mem [(B, B + 0x1000)] := by
    rw [hemem]; exact agrees_writeLE _ _ hnb2
  have hpan : panics0 e.mem = ch := by
    have h := hl.panics_frame _ _ 0 hag
    simp only [P0_panics] at h
    first | rw [← h, panics0_recTake hj]; exact hI.pan | rw [h, panics0_recTake hj]; exact hI.pan
  have hsv : saved0 e.mem = saved0 c.mem := by
    have h := hl.saved_frame _ _ 0 hag
    simp only [P0_saved] at h
    first | rw [← h]; exact saved0_recTake hj | rw [h]; exact saved0_recTake hj
  have hrm : room0 c.mem ≤ room0 e.mem := by
    have h := hl.room_frame _ _ 0 hag
    simp only [P0_room] at h
    first | (rw [← h]; exact room0_recTake hI.env hnd hn) | (rw [h]; exact room0_recTake hI.env hnd hn)
  have hdef : defers0 e.mem = defers0 (recTake c.mem j n) := hl.defers_frame _ _ 0 hag
  have hcurE : curItems e.mem F 0 = recItems F.sp (defers0 (recTake c.mem j n)) := by
    rw [curItems_zero, hdef]
  have hread : e.mem.readLE (recFn c.mem j n) 8 = c.mem.readLE (recFn c.mem j n) 8 := by
    rw [hemem]
    refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans hfnr
    omega
  have hrp : e.mem.readLE (e.regs 4).toNat 8 = RPa := by
    rw [hemem, show (e.regs 4).toNat = (c.regs 4).toNat - 8 by omega]; exact rd_RPa _ _
  refine ⟨e, ⟨⟨k, hk⟩, ?_, by omega, hrp, hmf, ?_, ?_, hdef, hcurE, hsv, hrm, Or.inl ⟨rfl, rfl⟩⟩⟩
  · refine ⟨?_, he2, by rw [he14]; exact hI.r14, by rw [hex]; exact hI.x15, by rw [hedf]; exact hI.dfc,
      by omega, ?_, by omega, by rw [hrp]; exact RPa_lt, henvE⟩
    · rw [hpe, hread, hfnr]
    · simp only [P0_depth]; omega
  · intro b' ba' sa' hb'; simp at hb'
  · refine hI.step 0 (by rw [he14]; exact hI.r14) (by rw [he5]; exact hI.r5) (by rw [hex]; exact hI.x15)
      (by rw [hedf]; exact hI.dfc) hmf ?_ henvE hpan (Nat.le_trans hI.room hrm)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hemem]
      refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans (hfr.readLE _ _ ?_)
      · omega
      · simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [hdef, ← rec_call_rest hI.env hnd hrs hn]; exact hI.chn
    · have hbr : e.mem.readLE ba' 1 = c.mem.readLE ba' 1 := by
        rw [hemem]
        refine (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_).trans (hfr.readLE _ _ ?_)
        · have := (hI.ba_facts hF').2.2.2.1; omega
        · have := (hI.ba_facts hF').2.2.1
          simpa using this
      exact hI.bsub ba' sa' hF' i (by rw [← hbr]; exact hi)
    · rw [hcurE] at hit'
      have := hI.its it' (by rw [hcur0]; exact List.mem_cons_of_mem _ hit')
      exact this


/-- A silent step of the loop (`TOREC`, `POPREC`): control returns to the loop head, nothing is called. -/
structure SilentSt (p : Program) (T : List FuncInfo) (m0 : Memory) (F : Frame) (items0 : List Item)
    (ds0 : List DeferRec) (mode : DeferMode) (g bp : W64) (lr : Nat) (c : State)
    (ch : List PanicRec) (rm ph ph2 : Nat) (c2 : State) : Prop where
  steps : ∃ k, Janus.Amd64.Program.Steps p c k c2
  pc : c2.rip = BitVec.ofNat 64 eLH
  loop : (c2.regs 4).toNat + 104 = F.sp
  inv : Inv0 T m0 F items0 ds0 mode g bp lr c2 ch rm ph2
  cur : curItems c2.mem F ph2 = curItems c.mem F ph
  mf : MemFrame c.mem c2.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F)
  sv : saved0 c2.mem = saved0 c.mem
  meas : (if ph2 = 0 then 0 else 1) * 9 + ndef c2.mem < (if ph = 0 then 0 else 1) * 9 + ndef c.mem

theorem step_torec (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph)
    (hL : (c.regs 4).toNat + 104 = F.sp) (hpc : c.rip = BitVec.ofNat 64 eLH) (hph : ph ≠ 0)
    {ba sa : Nat} (hF : F.openAt = some (ba, sa)) (hb : c.mem.readLE ba 1 = 0) :
    ∃ c2, SilentSt p T m0 F items0 ds0 mode g bp lr c ch rm ph 0 c2 := by
  obtain ⟨hal, hsp, h8⟩ := hI.spw hL
  have hacc := hI.acc' hL
  obtain ⟨b1, b2, b3, b4, b5⟩ := hI.ba_facts hF
  have hs : F.sp - 104 = (c.regs 4).toNat := by omega
  have hfm := hI.fm
  obtain ⟨w40, w48⟩ := hfm.w40 ba sa hF
  have hw32 := hfm.w32
  rw [hs] at w40 w48 hw32
  have hseg := seg_torec c ba hpc hal hsp h8 hacc (by rw [hw32]; exact hph) w40 hb b1 b2
  obtain ⟨k1, e, hk1, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hes4, hes5, hes14, hesx, hesdf⟩ := hq
  have hback := seg_back e (Or.inl hpe)
  obtain ⟨k2, c2, hk2, hpc2, hq2⟩ := reachesRet_transfer hp hback
  obtain ⟨hmem2, hregs2, hxmm2, hdf2⟩ := hq2
  have hl := P0_laws T RPa
  have hnb : Outside ((c.regs 4).toNat + 32) 8 [(B, B + 0x1000)] := by
    simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega
  have hm2 : c2.mem = c.mem.writeLE ((c.regs 4).toNat + 32) 8 0 := by rw [hmem2, hemem]
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
  have hrdk : ∀ k, (k + 8 ≤ 32 ∨ 40 ≤ k) → c2.mem.readLE (F.sp - 104 + k) 8 = c.mem.readLE (F.sp - 104 + k) 8 := by
    intro k hk; rw [hm2]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hc4 : c2.regs 4 = c.regs 4 := by rw [hregs2, hes4]
  have hc5 : c2.regs 5 = c.regs 5 := by rw [hregs2, hes5]
  have hc14 : c2.regs 14 = c.regs 14 := by rw [hregs2, hes14]
  have hcx : c2.xmm 15 = c.xmm 15 := by rw [hxmm2, hesx]
  have hcdf : c2.df = c.df := by rw [hdf2, hesdf]
  refine ⟨c2, ⟨⟨k1 + k2, hk1.trans hk2⟩, hpc2, by rw [hc4]; exact hL, ?_, hcur, hmf, hsv, ?_⟩⟩
  · refine hI.step 0 (by rw [hc14]; exact hI.r14) (by rw [hc5]; exact hI.r5) (by rw [hcx]; exact hI.x15)
      (by rw [hcdf]; exact hI.dfc) hmf ?_
      (by rw [hm2]; exact env0_of_outside hI.env hnb) hpan (by rw [hrm]; exact hI.room)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
      · have := hrdk 0 (Or.inl (by omega)); simpa using this.trans hfm.w0
      · exact (hrdk 8 (Or.inl (by omega))).trans hfm.w8
      · exact (hrdk 16 (Or.inl (by omega))).trans hfm.w16
      · exact (hrdk 24 (Or.inl (by omega))).trans hfm.w24
      · show c2.mem.readLE (F.sp - 104 + 32) 8 = 0
        rw [hm2, hs]; rw [Janus.Arm64.Memory.readLE_writeLE_self]
      · intro ba' sa' hF'
        exact ⟨(hrdk 40 (Or.inr (by omega))).trans (hfm.w40 ba' sa' hF').1,
          (hrdk 48 (Or.inr (by omega))).trans (hfm.w40 ba' sa' hF').2⟩
      · intro hm
        exact (hrdk 96 (Or.inr (by omega))).trans (hfm.w96 hm)
    · have := hI.sv hm
      have h2 := (saved0_none_iff _).2 this
      rw [← hsv] at h2
      exact (saved0_none_iff _).1 h2
    · rw [hdef]; exact hI.chn
    · have hbr : c2.mem.readLE ba' 1 = c.mem.readLE ba' 1 := by
        rw [hm2]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by have := (hI.ba_facts hF').2.2.2.1; omega)
      exact hI.bsub ba' sa' hF' i (by rw [← hbr]; exact hi)
    · rw [hcur] at hit'; exact hI.its it' hit'
  · rw [hndef]; by_cases h0 : ph = 0
    · exact absurd h0 hph
    · simp [h0]

theorem step_pop (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph)
    (hL : (c.regs 4).toNat + 104 = F.sp) (hpc : c.rip = BitVec.ofNat 64 eLH) (hph : ph = 0)
    {j : Nat} (hnd : ndef c.mem = j + 1) (hrs : recSp c.mem j = F.sp) (hn : recN c.mem j = 0) :
    ∃ c2, SilentSt p T m0 F items0 ds0 mode g bp lr c ch rm ph ph c2 := by
  subst hph
  obtain ⟨hal, hsp, h8⟩ := hI.spw hL
  have hacc := hI.acc' hL
  have hj : j < 8 := by have := hI.env.ndef_le; omega
  have hs : F.sp - 104 = (c.regs 4).toNat := by omega
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  rw [hs] at hw0 hw32
  have hseg := seg_rec_pop c j hpc hal hsp h8 hacc hI.env.acc hw32 hnd hj (by rw [hrs, hw0]) hn
  obtain ⟨k1, e, hk1, hpe, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hemem, hes4, hes5, hes14, hesx, hesdf⟩ := hq
  have hback := seg_back e (Or.inr hpe)
  obtain ⟨k2, c2, hk2, hpc2, hq2⟩ := reachesRet_transfer hp hback
  obtain ⟨hmem2, hregs2, hxmm2, hdf2⟩ := hq2
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
    rw [hm2]; simp only [popMem, ndef, rd]; rw [Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have : (256:Nat)^8 = 2^64 := by decide
                               omega)
  have hc4 : c2.regs 4 = c.regs 4 := by rw [hregs2, hes4]
  have hc5 : c2.regs 5 = c.regs 5 := by rw [hregs2, hes5]
  have hc14 : c2.regs 14 = c.regs 14 := by rw [hregs2, hes14]
  have hcx : c2.xmm 15 = c.xmm 15 := by rw [hxmm2, hesx]
  have hcdf : c2.df = c.df := by rw [hdf2, hesdf]
  refine ⟨c2, ⟨⟨k1 + k2, hk1.trans hk2⟩, hpc2, by rw [hc4]; exact hL, ?_, hcur, hmf, hsv, ?_⟩⟩
  · refine hI.step 0 (by rw [hc14]; exact hI.r14) (by rw [hc5]; exact hI.r5) (by rw [hcx]; exact hI.x15)
      (by rw [hcdf]; exact hI.dfc) hmf ?_
      (by rw [hm2]; exact env0_popMem hI.env hnd) hpan (Nat.le_trans hI.room hrm)
      (fun hm => ?_) ?_ (fun ba' sa' hF' i hi => ?_) (fun it' hit' => ?_)
    · refine hfm.congr fun k hk => ?_
      rw [hm2]
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hI.spB; omega)
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

theorem add104_ofNat (x : W64) (n : Nat) (hx : x.toNat + 104 = n) (hn : n < 2 ^ 64) :
    x + 104#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h104 : (104#64).toNat = 104 := rfl
  rw [BitVec.toNat_add, h104, BitVec.toNat_ofNat]; omega

theorem step_fin (hp : EngineAt p) (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph)
    (hL : (c.regs 4).toNat + 104 = F.sp) (hpc : c.rip = BitVec.ofNat 64 eLH) (hph : ph = 0)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) :
    ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ d.mem = c.mem ∧ d.regs 5 = bp ∧ d.regs 14 = g ∧
      d.xmm 15 = 0 ∧ d.df = false ∧
      (mode = .ret → d.rip = BitVec.ofNat 64 lr ∧ d.regs 4 = BitVec.ofNat 64 F.sp) ∧
      (mode ≠ .ret → d.rip = BitVec.ofNat 64 RPa ∧ d.regs 4 = BitVec.ofNat 64 (F.bound + 8)) := by
  subst hph
  obtain ⟨hal, hsp, h8⟩ := hI.spw hL
  have hacc := hI.acc' hL
  have hs : F.sp - 104 = (c.regs 4).toNat := by omega
  have hfm := hI.fm
  have hw0 := hfm.w0
  have hw32 := hfm.w32
  have hw8 := hfm.w8
  have hw24 := hfm.w24
  rw [hs] at hw0 hw32 hw8 hw24
  have hend' : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ j < 8 ∧ recSp c.mem j ≠ c.mem.readLE (c.regs 4).toNat 8 := by
    rcases hend with h | ⟨j, hj, hne⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by have := hI.env.ndef_le; omega, by rw [hw0]; exact hne⟩
  have hlrb : mode = .ret → c.mem.readLE ((c.regs 4).toNat + 96) 8 < 2 ^ 47 ∧
      c.mem.accessible ((c.regs 4).toNat + 96) 8 false = true := by
    intro hm
    have h := hfm.w96 hm
    rw [show F.sp - 104 + 96 = (c.regs 4).toNat + 96 by omega] at h
    rw [h]
    obtain ⟨h1, h2⟩ := hI.hlr hm
    exact ⟨h1, by rw [show (c.regs 4).toNat + 96 = F.sp - 8 by omega]; exact h2⟩
  have hseg := seg_fin c mode F.bound hpc hal hsp h8 hacc hI.env.acc hw32 hend' hw24 hw8 hI.hbd hlrb
  obtain ⟨k, d, hk, hpd, hd1, hd2, hd3, hd4, hd5, hd6⟩ := reachesRet_transfer hp hseg
  refine ⟨k, d, hk, hd1, by rw [hd2]; exact hI.r5, by rw [hd3]; exact hI.r14, by rw [hd4]; exact hI.x15,
    by rw [hd5]; exact hI.dfc, fun hm => ?_, fun hm => ?_⟩
  · subst hm
    have h96 := hfm.w96 rfl
    rw [show F.sp - 104 + 96 = (c.regs 4).toNat + 96 by omega] at h96
    simp only [reduceIte] at hpd hd6
    rw [h96] at hpd
    refine ⟨hpd, ?_⟩
    rw [hd6]; exact add104_ofNat _ _ hL (by have := hI.hi; omega)
  · have hne : ¬ mode = .ret := hm
    simp only [hne, reduceIte] at hpd hd6
    exact ⟨hpd, hd6⟩

end steps

end Janus.Contracts.PanicSatAmd64

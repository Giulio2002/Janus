import Janus.Contracts.PanicSatAmd64Steps


/-!
# The amd64 model engine meets the `gopanic`, `Goexit` and `deferreturn` contracts: the loop

`engine_call` (a deferred call and everything after it) and `engine_loop` (the induction over the
frame's calls) show that `PanicAmd64.Engine` holds for the model engine's loop, for every list of
deferred calls: the x86-64 twin of the second half of `Janus.Contracts.PanicSatEngine`.
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

/-- The panic chain's top entry is not recovered or a goexit (what the loop needs of `ch` in panic mode). -/
def PanOK (mode : DeferMode) (ch : List PanicRec) : Prop :=
  mode = .panic → ∃ r rs, ch = r :: rs ∧ r.recovered = false ∧ r.goexit = false

theorem ofNat_toNat_self (x : W64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem inRanges_widen {a n lo lo' hi : Nat} {rs : List (Nat × Nat)} (h : lo ≤ lo')
    (hin : InRanges a n ((lo', hi) :: rs)) : InRanges a n ((lo, hi) :: rs) := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  rcases List.mem_cons.1 hr with rfl | hr
  · exact ⟨(lo, hi), List.mem_cons_self, by simp only at h1 ⊢; omega, h2⟩
  · exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩

theorem RPa_ofNat_toNat : (BitVec.ofNat 64 RPa).toNat = RPa := by
  have := RPa_lt
  simp only [BitVec.toNat_ofNat]; omega

/-- A deferred call, and everything after it: the model engine's loop reaches the call, and for every
way the call may end the loop goes on (or recovers). -/
theorem engine_call (hp : EngineAt p)
    {Fin : List PanicRec → Nat → State → State → Prop}
    (hFin : ∀ (ch : List PanicRec) (rm : Nat) (c c' d : State),
      MemFrame c.mem c'.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) →
      saved0 c'.mem = saved0 c.mem → Fin ch rm c' d → Fin ch rm c d)
    (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph) (hpm : PanOK mode ch)
    {it : Item} {rest : List Item} {e : State}
    (cs : CallSt p T m0 F items0 ds0 mode g bp lr c ch rm ph it rest e)
    (IH : ∀ (c' : State) (ch' : List PanicRec) (rm' ph' : Nat), c'.rip = BitVec.ofNat 64 eLH →
      (c'.regs 4).toNat + 104 = F.sp →
      Inv0 T m0 F items0 ds0 mode g bp lr c' ch' rm' ph' → PanOK mode ch' → curItems c'.mem F ph' = rest →
      Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch' rm' rest c') :
    Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch rm (it :: rest) c := by
  rw [Engine_cons]
  obtain ⟨k, hk⟩ := cs.steps
  have hrsp := cs.rsp
  have hhi := hI.hi
  have hRPtn := RPa_ofNat_toNat
  refine ⟨k, e, hk, cs.call, cs.mf, cs.bits, cs.chain, cs.inv.pan, cs.inv.room, ?_, ?_, ?_⟩
  · -- the return point and the saved state
    split
    · rename_i hret
      refine ⟨rfl, (saved0_none_iff _).2 (cs.inv.sv hret)⟩
    · refine ⟨?_, cs.sv⟩
      show RPa = _
      exact cs.rp.symm
  · -- the call returned
    intro e' hdr
    have hroomE : room0 e.mem ≤ room0 e'.mem := hdr.2.2.2.2.2.2.2.2.2.2
    have hdag := hdr.2.2.2.2.2.2.1
    have hRP : e'.rip = BitVec.ofNat 64 RPa := by
      apply BitVec.eq_of_toNat_eq
      rw [hRPtn, ← cs.rp]; exact hdr.1
    have hLe' : (e'.regs 4).toNat + 104 = F.sp := by
      rw [hdr.2.1]
      have := (e.regs 4).isLt
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [BitVec.toNat_add, h8]; omega
    have h5 : mode = .ret → e'.regs 5 = bp := fun hm => by rw [hdr.2.2.2.1]; exact cs.inv.r5 hm
    refine ⟨fun hpan' => ?_, fun hmode r rs hch hq _ => ?_⟩
    · obtain ⟨hI', hci⟩ := cs.inv.ret hrsp hdr h5 ch rm hpan' (Nat.le_trans cs.inv.room hroomE)
      obtain ⟨k', c', hk', hpc', hmem', hL', hI''⟩ := step_rp hp hI' hLe' hRP
        (by cases hmode : mode with
            | panic => right; obtain ⟨r, rs, h1, h2, -⟩ := hpm hmode; exact ⟨r, rs, h1, h2⟩
            | goexit => left; simp
            | ret => left; simp)
      have hnx := IH c' ch rm ph hpc' hL' hI'' hpm (by rw [hmem', hci]; exact cs.cur)
      refine Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' e' c' d (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) hf)
        hk' (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) rfl hnx
    · subst hmode
      have hq' : panics0 e'.mem = { r with recovered := true } :: rs := hq
      obtain ⟨hI', hci⟩ := cs.inv.ret hrsp hdr (fun h => by cases h) _ rm hq' (Nat.le_trans cs.inv.room hroomE)
      obtain ⟨kk, hk1, hk8, hrr, -⟩ := panics0_cons hI'.env hq'
      have hflag : rd e'.mem (panAt kk + 24) / 2 % 2 = 1 := by
        have h := congrArg PanicRec.recovered hrr
        rw [decPan_recovered] at h
        simpa using h.symm
      obtain ⟨k', d, hk', hpcd, hsp', hr5, hr14, hxd, hdfd, hmf, henvd, hpand, hdefd, hroomd, hsvd⟩ :=
        step_recover hp hI' hLe' hRP hk1 hk8 hflag
      refine ⟨k', d, hk', hpcd, hsp', hr5, hr14, hxd, hdfd, hmf, henvd, hpand, hdefd, ?_, hroomd⟩
      show saved0 d.mem = _
      rcases cs.recov with ⟨hb, hph0⟩ | ⟨b, ba, sa, hb, hF, hphne, hrdb⟩
      · have : it.bits.getD 0 = 0 := by rw [hb]; rfl
        rw [if_pos this]
        rcases hsvd with ⟨⟨hph, -⟩, -⟩ | ⟨-, h⟩
        · exact absurd hph0 hph
        · exact h
      · have hbyte : e'.mem.readLE ba 1 = b := by
          have := hdag.readLE (inRanges_tail (by rw [frameKeep_eq]; exact inRanges_bits hF (keepCore m0 F items0)))
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
    obtain ⟨⟨hUpc, hUsp, hU14⟩, hUx, hUdf⟩ := hU
    have hag' : Agrees e.mem u.mem (((e.regs 4).toNat + 8, F.sp) :: frameKeep m0 F items0) :=
      hag.mono' fun a n h => inRanges_widen (by omega) h
    have hroom' : rm ≤ room0 u.mem + 1 := hroom
    obtain ⟨hI', hci⟩ := cs.inv.ret' (e' := u) hrsp (by rw [hU14]; exact ofNat_toNat_self g)
      (fun h => by cases h) hUx hUdf hag' henv hdef hsav (r2 :: ch) (rm - 1) hpan2 (by omega)
    have hLu : (u.regs 4).toNat + 104 = F.sp := by
      rw [hUsp, BitVec.toNat_ofNat]; omega
    have hpm2 : PanOK .panic (r2 :: ch) := fun _ => ⟨r2, ch, rfl, hrc, hgx⟩
    obtain ⟨k', c', hk', hpc', hmem', hL', hI''⟩ := step_rp hp hI' hLu hUpc (Or.inr ⟨r2, ch, rfl, hrc⟩)
    have hnx := IH c' (r2 :: ch) (rm - 1) ph hpc' hL' hI'' hpm2 (by rw [hmem', hci]; exact cs.cur)
    exact Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' u c' d (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) hf)
      hk' (by rw [hmem']; exact MemFrame.refl _ _) (by rw [hmem']) rfl hnx


/-- The model engine's loop meets `PanicAmd64.Engine`, for every list of deferred calls. -/
theorem engine_loop (hp : EngineAt p)
    {Fin : List PanicRec → Nat → State → State → Prop}
    (hFin : ∀ (ch : List PanicRec) (rm : Nat) (c c' d : State),
      MemFrame c.mem c'.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F) →
      saved0 c'.mem = saved0 c.mem → Fin ch rm c' d → Fin ch rm c d)
    (hfin : ∀ (c : State) (ch : List PanicRec) (rm : Nat), c.rip = BitVec.ofNat 64 eLH →
      (c.regs 4).toNat + 104 = F.sp →
      Inv0 T m0 F items0 ds0 mode g bp lr c ch rm 0 → PanOK mode ch →
      (ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) →
      ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ Fin ch rm c d) :
    ∀ (n : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat), (curItems c.mem F ph).length = n →
      c.rip = BitVec.ofNat 64 eLH → (c.regs 4).toNat + 104 = F.sp →
      Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph → PanOK mode ch →
      Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  have inner : ∀ (m : Nat) (c : State) (ch : List PanicRec) (rm ph : Nat),
      (if ph = 0 then 0 else 1) * 9 + ndef c.mem ≤ m → (curItems c.mem F ph).length = n →
      c.rip = BitVec.ofNat 64 eLH → (c.regs 4).toNat + 104 = F.sp →
      Inv0 T m0 F items0 ds0 mode g bp lr c ch rm ph → PanOK mode ch →
      Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ihm =>
    intro c ch rm ph hm hn hpc hL hI hpm
    have silent : ∀ (ph2 : Nat) (c2 : State),
        SilentSt p T m0 F items0 ds0 mode g bp lr c ch rm ph ph2 c2 →
        Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
      intro ph2 c2 ss
      obtain ⟨⟨j, hj⟩, hpc2, hL2, hinv2, hcur2, hmf2, hsv2, hmeas⟩ := ss
      have := ihm _ (by omega) c2 ch rm ph2 (Nat.le_refl _) (by rw [hcur2]; exact hn) hpc2 hL2 hinv2 hpm
      rw [hcur2] at this
      exact Engine.of_prefix (fun ch' rm' d hf => hFin ch' rm' c c2 d hmf2 hsv2 hf) hj hmf2 hsv2 rfl this
    have finc : (ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) → ph = 0 →
        Engine p (P0 T RPa) U1 g F (frameKeep m0 F items0) mode Fin ch rm (curItems c.mem F ph) c := by
      intro hend hph0
      subst hph0
      rw [curItems_zero, (fin_items hI.env hend).1, Engine_nil]
      exact hfin c ch rm hpc hL hI hpm hend
    by_cases hph0 : ph = 0
    · subst hph0
      by_cases hnd : ndef c.mem = 0
      · exact finc (Or.inl hnd) rfl
      · obtain ⟨j, hj⟩ : ∃ j, ndef c.mem = j + 1 := ⟨ndef c.mem - 1, by omega⟩
        by_cases hrs : recSp c.mem j = F.sp
        · cases hnn : recN c.mem j with
          | zero =>
            obtain ⟨c2, ss⟩ := step_pop hp hI hL hpc rfl hj hrs hnn
            exact silent 0 c2 ss
          | succ n0 =>
            obtain ⟨e, cs⟩ := step_rec hp hI hL hpc rfl hj hrs hnn
            have hcur := (curItems_zero c.mem F).trans (rec_call_items hI.env hj hrs hnn)
            rw [hcur]
            refine engine_call hp hFin hI hpm cs ?_
            intro c' ch' rm' ph' hpc' hL' hI' hpm' hc'
            have hlt : (curItems c'.mem F ph').length < n := by
              rw [hc', ← hn, hcur]; simp
            exact (ihn _ hlt) c' ch' rm' ph' rfl hpc' hL' hI' hpm' |> fun h => by rw [hc'] at h; exact h
        · exact finc (Or.inr ⟨j, hj, hrs⟩) rfl
    · obtain ⟨⟨ba, sa⟩, hF⟩ : ∃ q, F.openAt = some q := by
        have hsome := hI.fm.hph hph0
        cases hq : F.openAt with
        | none => rw [hq] at hsome; simp at hsome
        | some q => exact ⟨q, rfl⟩
      by_cases hb : c.mem.readLE ba 1 = 0
      · obtain ⟨c2, ss⟩ := step_torec hp hI hL hpc hph0 hF hb
        exact silent 0 c2 ss
      · have hb0 : 0 < c.mem.readLE ba 1 := Nat.pos_of_ne_zero hb
        have hcur := curItems_open hph0 hF hb0
        obtain ⟨e, cs⟩ := step_open hp hI hL hpc hph0 hF hb0 hcur
        rw [hcur]
        refine engine_call hp hFin hI hpm cs ?_
        intro c' ch' rm' ph' hpc' hL' hI' hpm' hc'
        have hlt : (curItems c'.mem F ph').length < n := by
          rw [hc', ← hn, hcur]; simp
        exact (ihn _ hlt) c' ch' rm' ph' rfl hpc' hL' hI' hpm' |> fun h => by rw [hc'] at h; exact h
  exact fun c ch rm ph hn hpc hL hI hpm => inner _ c ch rm ph (Nat.le_refl _) hn hpc hL hI hpm


/-- `Engine.of_prefix` for `deferreturn`, whose prefix clears the saved state. -/
theorem Engine.of_prefix_ret {p : Janus.Amd64.Program} {P : PanicRuntime} {U : State → Nat → Nat → Prop} {g : W64}
    {F : Frame} {keep : List (Nat × Nat)}
    {Fin : List PanicRec → Nat → State → State → Prop} {c c' : State} {j : Nat}
    (hFin : ∀ ch rm d, Fin ch rm c' d → Fin ch rm c d) (hst : Janus.Amd64.Program.Steps p c j c')
    (hm : MemFrame c.mem c'.mem (P.priv ++ rtWin P F ++ bitsWin F))
    (hrp : P.rp c'.mem g.toNat = P.rp c.mem g.toNat) :
    ∀ {ch : List PanicRec} {rm : Nat} {L : List Item},
      Engine p P U g F keep .ret Fin ch rm L c' → Engine p P U g F keep .ret Fin ch rm L c
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

end Janus.Contracts.PanicSatAmd64

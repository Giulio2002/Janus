import Janus.Contracts.LiveStubGrow
import Janus.Contracts.IfaceLive

/-!
# `runtime.convTstring` / `runtime.convT64` live, at a program's own address (arm64)

`RtLiveContract linked addr 4096 (toyR tys ok) convTstringSpec convTstringLive` (and `convT64Spec`,
`convT64Live`) by a stub in `toyR`'s runtime. A call has two shapes (the specs' `if`s): it
**allocates** a box from the bump allocator (`convTstring` of a non-empty string: 16 bytes holding
`(ptr, len)`; `convT64` of `v ≥ 256`: 8 bytes holding `v`), or it returns a **static** box in the
runtime's ranges (the barrier buffer `WBUF` plays `&zeroVal` / `&staticuint64s[v]`: the stub writes
the words there). Each shape is its own stub, fixed by the request `ok` pins (`hok`):

```lean
theorem hs : RtLiveContract linked a 4096 R convTstringSpec convTstringLive := by
  janus_live_convtstring 5 hok            -- non-empty: allocates (the length is any numeral ≠ 0)
theorem he : RtLiveContract linked a 4096 R convTstringSpec convTstringLive := by
  janus_live_convtstring_empty hok        -- the empty string: `&zeroVal`
theorem h64 : … convT64Spec convT64Live := by janus_live_convt64 300 hok      -- v ≥ 256
theorem h8  : … convT64Spec convT64Live := by janus_live_convt64_small 7 hok  -- v < 256
```
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- Stores in `rs` keep the frame. -/
theorem memFrame_applyWrites {rs : List (Nat × Nat)} (ws : List Wr) (hws : ∀ w ∈ ws, InRanges w.1 w.2.1 rs) :
    ∀ m m' : Memory, MemFrame m m' rs → MemFrame m (applyWrites m' ws) rs := by
  induction ws with
  | nil => intro m m' h; exact h
  | cons w ws ih =>
    intro m m' h
    rw [applyWrites_cons]
    exact ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) _ _
      (h.writeLE_inRanges _ (hws w (List.mem_cons_self ..)))

/-- Stores inside `rt` and outside `L` are stores into the view. -/
theorem view_applyWrites_vis {rt L : List (Nat × Nat)} (ws : List Wr) (h1 : ∀ w ∈ ws, InRanges w.1 w.2.1 rt)
    (h2 : ∀ w ∈ ws, Outside w.1 w.2.1 L) :
    ∀ m : Memory, view rt L (applyWrites m ws) = applyWrites (view rt L m) ws := by
  induction ws with
  | nil => intro m; rfl
  | cons w ws ih =>
    intro m
    rw [applyWrites_cons, applyWrites_cons,
      ih (fun w' hw' => h1 w' (List.mem_cons_of_mem _ hw')) (fun w' hw' => h2 w' (List.mem_cons_of_mem _ hw')),
      view_writeLE_vis (h1 w (List.mem_cons_self ..)) (h2 w (List.mem_cons_self ..))]

/-! ### The spec's postconditions of the two shapes (independent of the ISA) -/

theorem convTstring_box {rt : List (Nat × Nat)} {m1 : Memory} {p ptr len : Nat} (hptr : ptr < 2 ^ 64)
    (hlen : len < 2 ^ 64) (hp : p + 16 ≤ 2 ^ 48) (hrt : InRanges p 16 rt)
    (hacc : m1.accessible p 16 false = true) :
    BoxWords' rt (applyWrites m1 [(p, 8, ptr), (p + 8, 8, len)]) p [ptr, len] := by
  refine ⟨by simpa using hp, by rw [accessible_applyWrites]; simpa using hacc, by simpa using hrt, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  simp only [applyWrites_cons, applyWrites_nil]
  rcases i with _ | _ | i
  · simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hptr)
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [show p + 8 * (0 + 1) = p + 8 by omega, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hlen)
  · omega

theorem convT64_box {rt : List (Nat × Nat)} {m1 : Memory} {p v : Nat} (hv : v < 2 ^ 64)
    (hp : p + 8 ≤ 2 ^ 48) (hrt : InRanges p 8 rt) (hacc : m1.accessible p 8 false = true) :
    BoxHolds' rt (applyWrites m1 [(p, 8, v)]) p 8 v := by
  refine ⟨hp, by rw [accessible_applyWrites]; exact hacc, hrt, ?_⟩
  simp only [applyWrites_cons, applyWrites_nil]
  rw [Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by simpa using hv)

/-- `accessible … true` gives `accessible … false`. -/
theorem acc_false {m : Memory} {a n : Nat} (h : m.accessible a n true = true) : m.accessible a n false = true := by
  obtain ⟨⟨r, hr, h1, h2, h3, h4⟩, hall⟩ := (Memory.accessible_iff m a n true).1 h
  exact (Memory.accessible_iff m a n false).2 ⟨⟨r, hr, h1, h2, h3, Or.inl rfl⟩, fun hw => by simp at hw⟩

set_option maxHeartbeats 2000000 in
/-- The return of an **allocating** stub (`BUMP` advanced by `A`, the stores `wsf p` inside the new box
`[p, p + K)`) meets the live contract of `sp`/`ls`. -/
theorem alloc_box_finish {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {K A : Nat} {wsf : Nat → List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords s sp.nargs) s.mem = [])
    (hA3 : A % 16 = 0) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hKpos : 0 < K)
    (hcost : ls.cost (argWords s sp.nargs) s.mem = K)
    (hfresh : ∀ r0 r1 r2, ls.fresh (argWords s sp.nargs) s.mem r0 r1 r2 = [(r0, r0 + K)])
    (hkeep : ∀ r0 r1 r2, ls.keep (argWords s sp.nargs) s.mem r0 r1 r2 = [])
    (hws : ∀ p, ∀ w ∈ wsf p, p ≤ w.1 ∧ w.1 + w.2.1 ≤ p + K)
    (hpost : ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true →
      sp.post (toyRt tys) (argWords s sp.nargs) s.mem p r1 r2 (applyWrites (s.mem.writeLE BUMP 8 (p + A)) (wsf p)))
    (pre : RtLivePre 4096 (toyR tys ok) sp ls addr L b s)
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A)) (wsf (s.mem.readLE BUMP 8))) :
    RtLivePost 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hcb : K ≤ b := hcost ▸ hcostb
  obtain ⟨p, hpm, hp1, hp2, hend, hfr, hlf, hap, hz, hacc, hinv'⟩ :=
    toy_alloc hty hA3 hA1 hA2 hcb hinvT
  have hp64 : p + A < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hpm] at hmem h0
  have hpost' := hpost p (fin.regs 1).toNat (fin.regs 2).toNat hp1 hend hacc
  generalize hm1 : s.mem.writeLE BUMP 8 (p + A) = m1 at hlf hz hacc hinv' hmem hpost'
  have hbytes : ∀ x, (x < p ∨ p + K ≤ x) → (applyWrites m1 (wsf p)).bytes x = m1.bytes x := fun x hx =>
    bytes_applyWrites_untouched _ (fun w hw => by have := hws p w hw; omega) m1
  have hbump : ∀ x, (x < BUMP ∨ BUMP + 8 ≤ x) → m1.bytes x = s.mem.bytes x := fun x hx =>
    by rw [← hm1]; exact Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  refine ⟨BitVec.ofNat 64 p, fin.regs 1, fin.regs 2, fin.regs, fin.flags, fin.vregs, fin.mem, fin.excl,
    fin.exclPass, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · simpa using h0
    · rfl
    · rfl
    · omega
  · refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · simp only [hrw, rtIf_true, hwr, List.append_nil, outside_append] at hout
      have hHB := outside_toyRt_heap_bump hout.1
      rw [hmem]
      refine Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Memory.accessible_writeLE]
  · rw [hpn]; rw [hmem]; exact hpost'
  · rw [hwr]
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Memory.readLE_congr (fun i hi => ?_)
    rw [hbytes (a + i) (by omega)]
  · rw [hfresh, hpn]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using hap
  · simp only [liveAdds, hfresh, hkeep, List.append_nil, hpn]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using apart_win (inRanges_heap (tys := tys) hp1 hpHE) hWs
  · simp only [liveAdds, hfresh, hkeep, hcost, List.append_nil, hpn]
    rw [hmem, view_applyWrites (wsf p) (hws p)
      (Or.inl ⟨(p, p + K), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by omega⟩)]
    exact hinv'

set_option maxHeartbeats 2000000 in
/-- The return of a **static** stub (stores `ws` into the barrier buffer, returns `WBUF`; nothing
allocated) meets the live contract of `sp`/`ls`. -/
theorem static_box_finish {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {n : Nat} (hn : n ≤ 8) {ws : List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords s sp.nargs) s.mem = [])
    (hcost : ls.cost (argWords s sp.nargs) s.mem = 0)
    (hfresh : ∀ r0 r1 r2, ls.fresh (argWords s sp.nargs) s.mem r0 r1 r2 = [])
    (hkeep : ∀ r0 r1 r2, ls.keep (argWords s sp.nargs) s.mem r0 r1 r2 = [])
    (hws : ∀ w ∈ ws, WBUF ≤ w.1 ∧ w.1 + w.2.1 ≤ WBUF + 8 * n)
    (hpost : ∀ r1 r2, (applyWrites s.mem ws).accessible WBUF (8 * n) true = true →
      sp.post (toyRt tys) (argWords s sp.nargs) s.mem WBUF r1 r2 (applyWrites s.mem ws))
    (pre : RtLivePre 4096 (toyR tys ok) sp ls addr L b s)
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (h0 : fin.regs 0 = BitVec.ofNat 64 WBUF) (hmem : fin.mem = applyWrites s.mem ws) :
    RtLivePost 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  obtain ⟨p, hpm, hH, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩ := hinvT
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) :=
    ⟨p, hpm, hH, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩
  have hacW' : s.mem.accessible WBUF 64 true = true := by rw [← view_accessible (toyRt tys) L s.mem]; exact hacW
  have hn0 : (BitVec.ofNat 64 WBUF).toNat = WBUF := by decide
  have hin : ∀ w ∈ ws, InRanges w.1 w.2.1 (toyRt tys) := fun w hw =>
    ⟨(WBUF, WBUF + 64), by simp [toyRt], (hws w hw).1, by have := (hws w hw).2; omega⟩
  have hout : ∀ w ∈ ws, Outside w.1 w.2.1 L := fun w hw =>
    outside_live hL (by have := hws w hw; simp only [WBUF, HEAP] at *; omega)
  have hfr : MemFrame s.mem (applyWrites s.mem ws) (toyRt tys) :=
    memFrame_applyWrites ws hin _ _ (MemFrame.refl _ _)
  refine ⟨BitVec.ofNat 64 WBUF, fin.regs 1, fin.regs 2, fin.regs, fin.flags, fin.vregs, fin.mem, fin.excl,
    fin.exclPass, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · simpa using h0
    · rfl
    · rfl
    · omega
  · rw [hmem]
    simp only [hrw, rtIf_true, hwr, List.append_nil]
    exact memFrame_applyWrites ws (fun w hw => (hin w hw).append_left _) _ _ (MemFrame.refl _ _)
  · rw [hn0, hmem]
    exact hpost _ _ (by rw [accessible_applyWrites]; exact Memory.accessible_mono _ hacW' (Nat.le_refl _) (by omega))
  · rw [hwr]
    refine ⟨fun a k hinL _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hinL
    have hr' := hL r hr
    rw [hmem]
    refine Memory.readLE_congr (fun i hi => ?_)
    exact bytes_applyWrites_untouched ws (fun w hw => by have := hws w hw; simp only [WBUF, HEAP] at *; omega) _
  · rw [hfresh]; simp [FreshFrom]
  · simp [liveAdds, hfresh, hkeep, LiveApart]
  · simp only [liveAdds, hfresh, hkeep, hcost, List.append_nil, Nat.sub_zero]
    show toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L fin.mem)
    rw [hmem, view_applyWrites_vis ws hin hout]
    exact toyInv.frame hty hn hinvT
      (memFrame_applyWrites ws (fun w hw => ⟨(WBUF, WBUF + 8 * n), List.mem_singleton_self _,
        (hws w hw).1, (hws w hw).2⟩) _ _ (MemFrame.refl _ _))

/-! ### The requests and the specs' branches -/

theorem convt_args2 {s : State} {p0 n : Nat} (h : argWords s convTstringSpec.nargs = [p0, n]) :
    (s.regs 0).toNat = p0 ∧ (s.regs 1).toNat = n := by
  have h0 := congrArg (fun l => l.getD 0 0) h
  have h1 := congrArg (fun l => l.getD 1 0) h
  exact ⟨by simpa [argWords, wordsFrom, convTstringSpec] using h0, by simpa [argWords, wordsFrom, convTstringSpec] using h1⟩

theorem convt_args1 {s : State} {v : Nat} (h : argWords s convT64Spec.nargs = [v]) : (s.regs 0).toNat = v := by
  have h0 := congrArg (fun l => l.getD 0 0) h
  simpa [argWords, wordsFrom, convT64Spec] using h0

theorem convTstring_alloc_live {a : List Nat} (m : Memory) (h : arg a 1 ≠ 0) :
    convTstringLive.cost a m = 16 ∧ (∀ r0 r1 r2, convTstringLive.fresh a m r0 r1 r2 = [(r0, r0 + 16)]) := by
  refine ⟨by simp only [convTstringLive, if_neg h]; decide, fun r0 r1 r2 => by simp only [convTstringLive, if_neg h]⟩

theorem convTstring_empty_live {a : List Nat} (m : Memory) (h : arg a 1 = 0) :
    convTstringLive.cost a m = 0 ∧ (∀ r0 r1 r2, convTstringLive.fresh a m r0 r1 r2 = []) := by
  refine ⟨by simp only [convTstringLive, if_pos h], fun r0 r1 r2 => by simp only [convTstringLive, if_pos h]⟩

theorem convT64_alloc_live {a : List Nat} (m : Memory) (h : ¬ arg a 0 < 256) :
    convT64Live.cost a m = 8 ∧ (∀ r0 r1 r2, convT64Live.fresh a m r0 r1 r2 = [(r0, r0 + 8)]) := by
  refine ⟨by simp only [convT64Live, if_neg h]; decide, fun r0 r1 r2 => by simp only [convT64Live, if_neg h]⟩

theorem convT64_small_live {a : List Nat} (m : Memory) (h : arg a 0 < 256) :
    convT64Live.cost a m = 0 ∧ (∀ r0 r1 r2, convT64Live.fresh a m r0 r1 r2 = []) := by
  refine ⟨by simp only [convT64Live, if_pos h], fun r0 r1 r2 => by simp only [convT64Live, if_pos h]⟩

theorem convTstring_hpost {tys : Tys} {s : State} {p0 n A : Nat} (hargs : argWords s convTstringSpec.nargs = [p0, n])
    (hn : n ≠ 0) (hA : 16 ≤ A) :
    ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND → (s.mem.writeLE BUMP 8 (p + A)).accessible p 16 true = true →
      convTstringSpec.post (toyRt tys) (argWords s convTstringSpec.nargs) s.mem p r1 r2
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) [(p, 8, (s.regs 0).toNat), (p + 8, 8, (s.regs 1).toNat)]) := by
  intro p r1 r2 hp hend hacc
  obtain ⟨h0, h1⟩ := convt_args2 hargs
  have hargs2 : argWords s 2 = [p0, n] := hargs
  simp only [convTstringSpec, hargs2, arg, List.getD_cons_succ, List.getD_cons_zero, if_neg hn]
  subst h0 h1
  exact convTstring_box (rt := toyRt tys) (m1 := s.mem.writeLE BUMP 8 (p + A)) (p := p)
    (ptr := (s.regs 0).toNat) (len := (s.regs 1).toNat) (s.regs 0).isLt (s.regs 1).isLt
    (by simp only [HEND, HEAP, HSIZE] at hend hp ⊢; omega) (inRanges_heap hp (by omega)) (acc_false hacc)

theorem convTstring_hpost_empty {tys : Tys} {s : State} {p0 : Nat} (hargs : argWords s convTstringSpec.nargs = [p0, 0]) :
    ∀ r1 r2, (applyWrites s.mem [(WBUF, 8, 0), (WBUF + 8, 8, 0)]).accessible WBUF (8 * 2) true = true →
      convTstringSpec.post (toyRt tys) (argWords s convTstringSpec.nargs) s.mem WBUF r1 r2
        (applyWrites s.mem [(WBUF, 8, 0), (WBUF + 8, 8, 0)]) := by
  intro r1 r2 hacc
  have hargs2 : argWords s 2 = [p0, 0] := hargs
  simp only [convTstringSpec, hargs2, arg, List.getD_cons_succ, List.getD_cons_zero, if_pos rfl]
  have := convTstring_box (rt := toyRt tys) (m1 := s.mem) (p := WBUF) (ptr := 0) (len := 0)
    (by decide) (by decide) (by decide) (inRanges_wbuf (n := 2) (by omega))
    (by rw [accessible_applyWrites] at hacc; exact acc_false (by simpa using hacc))
  simpa using this

theorem convT64_hpost {tys : Tys} {s : State} {v A : Nat} (hargs : argWords s convT64Spec.nargs = [v]) (hA : 8 ≤ A) :
    ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND → (s.mem.writeLE BUMP 8 (p + A)).accessible p 8 true = true →
      convT64Spec.post (toyRt tys) (argWords s convT64Spec.nargs) s.mem p r1 r2
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) [(p, 8, (s.regs 0).toNat)]) := by
  intro p r1 r2 hp hend hacc
  have h0 := convt_args1 hargs
  have hargs2 : argWords s 1 = [v] := hargs
  simp only [convT64Spec, hargs2, arg, List.getD_cons_zero]
  subst h0
  exact convT64_box (rt := toyRt tys) (m1 := s.mem.writeLE BUMP 8 (p + A)) (s.regs 0).isLt
    (by simp only [HEND, HEAP, HSIZE] at hend hp ⊢; omega) (inRanges_heap hp (by omega)) (acc_false hacc)

theorem convT64_hpost_small {tys : Tys} {s : State} {v : Nat} (hargs : argWords s convT64Spec.nargs = [v]) :
    ∀ r1 r2, (applyWrites s.mem [(WBUF, 8, (s.regs 0).toNat)]).accessible WBUF (8 * 1) true = true →
      convT64Spec.post (toyRt tys) (argWords s convT64Spec.nargs) s.mem WBUF r1 r2
        (applyWrites s.mem [(WBUF, 8, (s.regs 0).toNat)]) := by
  intro r1 r2 hacc
  have h0 := convt_args1 hargs
  have hargs2 : argWords s 1 = [v] := hargs
  simp only [convT64Spec, hargs2, arg, List.getD_cons_zero]
  subst h0
  exact convT64_box (rt := toyRt tys) (m1 := s.mem) (s.regs 0).isLt (by decide) (inRanges_wbuf (n := 1) (by omega))
    (by rw [accessible_applyWrites] at hacc; exact acc_false (by simpa using hacc))

/-- The barrier buffer is writable, from the invariant (for the run of a static stub). -/
theorem toy_wbuf_acc {tys : Tys} {b g : Nat} {m : Memory} {L' : List (Nat × Nat)}
    (h : toyInv tys b L' g (view (toyRt tys) L' m)) : m.accessible WBUF 64 true = true := by
  obtain ⟨p, -, -, -, -, -, -, -, -, hacW, -⟩ := h
  rwa [view_accessible] at hacW

/-! ### The stubs -/

/-- `convTstring` of a non-empty string: `X2 = [BUMP]; [BUMP] = X2 + A; [X2] = X0; [X2 + 8] = X1; X0 = X2`. -/
def convTstringCode (A : Nat) : List Nat :=
  [0xd2a00809, 0xf9400122, 0x9100004a + A * 1024, 0xf900012a, 0xf9000040, 0xf9000441, 0xaa0203e0, 0xd65f03c0]
def convTstringSeg (addr A : Nat) : Segment := ⟨"live-stub.convTstring", addr, convTstringCode A⟩

/-- `convTstring("")`: two zero words at `WBUF`, `X0 = WBUF` (the toy's `&zeroVal`). -/
def convTstringEmptyCode : List Nat := [0xd2a00809, 0x91040129, 0xf900013f, 0xf900053f, 0xaa0903e0, 0xd65f03c0]
def convTstringEmptySeg (addr : Nat) : Segment := ⟨"live-stub.convTstring", addr, convTstringEmptyCode⟩

/-- `convT64(v)`, `v ≥ 256`: a fresh 8-byte box holding `X0`. -/
def convT64Code (A : Nat) : List Nat :=
  [0xd2a00809, 0xf9400122, 0x9100004a + A * 1024, 0xf900012a, 0xf9000040, 0xaa0203e0, 0xd65f03c0]
def convT64Seg (addr A : Nat) : Segment := ⟨"live-stub.convT64", addr, convT64Code A⟩

/-- `convT64(v)`, `v < 256`: `v` stored at `WBUF`, `X0 = WBUF` (the toy's `&staticuint64s[v]`). -/
def convT64SmallCode : List Nat := [0xd2a00809, 0x91040129, 0xf9000120, 0xaa0903e0, 0xd65f03c0]
def convT64SmallSeg (addr : Nat) : Segment := ⟨"live-stub.convT64", addr, convT64SmallCode⟩

end Janus.Contracts.LiveStub

/-- `RtLiveContract linked a 4096 (toyR tys ok) convTstringSpec convTstringLive` for
`LiveStub.convTstringSeg a A` and a non-empty string: `hok : ∀ args, ok a args → ∃ p, args = [p, n]`,
`n ≠ 0` a numeral, `A` a multiple of 16, `16 ≤ A ≤ 1024`. -/
syntax "janus_live_convtstring " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_convtstring $n $A $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨p0, hargs⟩ := $hok _ hokx
      have hn : arg (argWords s Janus.Contracts.convTstringSpec.nargs) 1 ≠ 0 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convTstring_alloc_live s.mem hn
      have hK16 : 16 ≤ b := hK ▸ hcostx
      have hacB' := Janus.Contracts.LiveSat.bump_acc hinvx
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := 16) (g := (s.regs 28).toNat) (L' := L)
        (tys := _) hinvx hK16
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := 16) (g := (s.regs 28).toNat) (L' := L)
        (tys := _) hinvx hK16
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      open Janus.Contracts Janus.Tactic in
        refine Janus.Contracts.LiveStub.alloc_box_finish (by decide) (sp := convTstringSpec) (ls := convTstringLive)
          (K := 16) (A := $A)
          (wsf := fun p => [(p, 8, (s.regs 0).toNat), (p + 8, 8, (s.regs 1).toNat)]) rfl rfl
          (by decide) (by decide) (by decide) (by decide) hK hF (fun _ _ _ => rfl)
          (by intro p w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> simp <;> omega)
          (Janus.Contracts.LiveStub.convTstring_hpost hargs (by decide : ($n : Nat) ≠ 0) (by decide : 16 ≤ $A))
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [setReg, Janus.Contracts.Toy.BUMP]; done) | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))

/-- … for `LiveStub.convTstringEmptySeg a` and the empty string: `hok : ∀ args, ok a args → ∃ p, args = [p, 0]`. -/
syntax "janus_live_convtstring_empty " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_convtstring_empty $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨p0, hargs⟩ := $hok _ hokx
      have hn : arg (argWords s Janus.Contracts.convTstringSpec.nargs) 1 = 0 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convTstring_empty_live s.mem hn
      have hW := Janus.Contracts.LiveStub.toy_wbuf_acc (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx
      open Janus.Contracts.Toy in
        simp only [WBUF] at hW
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      open Janus.Contracts Janus.Tactic in
        refine Janus.Contracts.LiveStub.static_box_finish (by decide) (sp := convTstringSpec) (ls := convTstringLive)
          (n := 2) (by decide) (ws := [(Janus.Contracts.Toy.WBUF, 8, 0), (Janus.Contracts.Toy.WBUF + 8, 8, 0)]) rfl rfl
          hK hF (fun _ _ _ => rfl)
          (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> simp)
          (Janus.Contracts.LiveStub.convTstring_hpost_empty hargs)
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [setReg, Janus.Contracts.Toy.WBUF]; done)))

/-- … `convT64Spec`/`convT64Live` for `LiveStub.convT64Seg a A`, `v ≥ 256` a numeral:
`hok : ∀ args, ok a args → args = [v]`. -/
syntax "janus_live_convt64 " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_convt64 $v $A $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      have hargs := $hok _ hokx
      have hn : ¬ arg (argWords s Janus.Contracts.convT64Spec.nargs) 0 < 256 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convT64_alloc_live s.mem hn
      have hK8 : 8 ≤ b := hK ▸ hcostx
      have hacB' := Janus.Contracts.LiveSat.bump_acc hinvx
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := 8) (g := (s.regs 28).toNat) (L' := L)
        (tys := _) hinvx hK8
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := 8) (g := (s.regs 28).toNat) (L' := L)
        (tys := _) hinvx hK8
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump
      generalize hgs : Janus.Contracts.convT64Spec = spX at *
      generalize hgl : Janus.Contracts.convT64Live = lsX at *
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      subst hgs hgl
      open Janus.Contracts Janus.Tactic in
        refine Janus.Contracts.LiveStub.alloc_box_finish (by decide) (sp := convT64Spec) (ls := convT64Live)
          (K := 8) (A := $A) (wsf := fun p => [(p, 8, (s.regs 0).toNat)]) rfl rfl
          (by decide) (by decide) (by decide) (by decide) hK hF (fun _ _ _ => rfl)
          (by intro p w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl; simp)
          (Janus.Contracts.LiveStub.convT64_hpost hargs (by decide : 8 ≤ $A))
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [setReg, Janus.Contracts.Toy.BUMP]; done) | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))

/-- … `convT64Spec`/`convT64Live` for `LiveStub.convT64SmallSeg a`, `v < 256`: `hok : … args = [v]`. -/
syntax "janus_live_convt64_small " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_convt64_small $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      have hargs := $hok _ hokx
      have hn : arg (argWords s Janus.Contracts.convT64Spec.nargs) 0 < 256 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convT64_small_live s.mem hn
      have hW := Janus.Contracts.LiveStub.toy_wbuf_acc (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx
      open Janus.Contracts.Toy in
        simp only [WBUF] at hW
      generalize hgs : Janus.Contracts.convT64Spec = spX at *
      generalize hgl : Janus.Contracts.convT64Live = lsX at *
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      subst hgs hgl
      open Janus.Contracts Janus.Tactic in
        refine Janus.Contracts.LiveStub.static_box_finish (by decide) (sp := convT64Spec) (ls := convT64Live)
          (n := 1) (by decide) (ws := [(Janus.Contracts.Toy.WBUF, 8, (s.regs 0).toNat)]) rfl rfl
          hK hF (fun _ _ _ => rfl)
          (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl; simp)
          (Janus.Contracts.LiveStub.convT64_hpost_small hargs)
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [setReg, Janus.Contracts.Toy.WBUF]; done)))

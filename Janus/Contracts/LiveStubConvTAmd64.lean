import Janus.Contracts.LiveStubGrowAmd64
import Janus.Contracts.LiveStubConvT

/-!
# `runtime.convTstring` / `runtime.convT64` live, at a program's own address (amd64)

The amd64 twin of `LiveStubConvT.lean`: `RtLiveContract64 linked addr 4096 (toyR tys ok) convTstringSpec
convTstringLive` (and `convT64Spec`, `convT64Live`) by tactics `janus64_live_convtstring n A hok`,
`janus64_live_convtstring_empty hok`, `janus64_live_convt64 v A hok`, `janus64_live_convt64_small hok`
(arguments as the arm64 tactics). The request is `RAX = ptr`, `RBX = len` (`convTstring`), `RAX = v`
(`convT64`); the box comes back in `RAX`.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.LiveStub

set_option maxHeartbeats 2000000 in
/-- The return of an **allocating** stub (`BUMP` advanced by `A`, the stores `wsf p` inside the new box
`[p, p + K)`) meets the live contract of `sp`/`ls`. -/
theorem alloc_box_finish64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {K A : Nat} {wsf : Nat → List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords64 s sp.nargs) s.mem = [])
    (hA3 : A % 16 = 0) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hKpos : 0 < K)
    (hcost : ls.cost (argWords64 s sp.nargs) s.mem = K)
    (hfresh : ∀ r0 r1 r2, ls.fresh (argWords64 s sp.nargs) s.mem r0 r1 r2 = [(r0, r0 + K)])
    (hkeep : ∀ r0 r1 r2, ls.keep (argWords64 s sp.nargs) s.mem r0 r1 r2 = [])
    (hws : ∀ p, ∀ w ∈ wsf p, p ≤ w.1 ∧ w.1 + w.2.1 ≤ p + K)
    (hpost : ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true →
      sp.post (toyRt tys) (argWords64 s sp.nargs) s.mem p r1 r2 (applyWrites (s.mem.writeLE BUMP 8 (p + A)) (wsf p)))
    (pre : RtLivePre64 4096 (toyR tys ok) sp ls addr L b s)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A)) (wsf (s.mem.readLE BUMP 8))) :
    RtLivePost64 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  have hcb : K ≤ b := hcost ▸ hcostb
  obtain ⟨p, hpm, hp1, hp2, hend, hfr, hlf, hap, hz, hacc, hinv'⟩ :=
    toy_alloc hty hA3 hA1 hA2 hcb hinvT
  have hp64 : p + A < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hpm] at hmem h0
  have hpost' := hpost p (fin.regs 3).toNat (fin.regs 1).toNat hp1 hend hacc
  generalize hm1 : s.mem.writeLE BUMP 8 (p + A) = m1 at hlf hz hacc hinv' hmem hpost'
  have hbytes : ∀ x, (x < p ∨ p + K ≤ x) → (applyWrites m1 (wsf p)).bytes x = m1.bytes x := fun x hx =>
    bytes_applyWrites_untouched _ (fun w hw => by have := hws p w hw; omega) m1
  have hbump : ∀ x, (x < BUMP ∨ BUMP + 8 ≤ x) → m1.bytes x = s.mem.bytes x := fun x hx =>
    by rw [← hm1]; exact Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  refine ⟨BitVec.ofNat 64 p, fin.regs 3, fin.regs 1, fin.regs, fin.flags, fin.xmm, fin.ymmHi, fin.mem,
    fin.zmmHi, fin.kreg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Janus.Contracts.AllocSatAmd64.ret_of s fin [BitVec.ofNat 64 p, fin.regs 3, fin.regs 1]
      hrip h4 h5 h14 (by simpa using h0) (by simp) (by simp) hx hfs hdf hmx hx87 hfw
  · refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · simp only [hrw, rtIf_true, hwr, List.append_nil, outside_append] at hout
      have hHB := outside_toyRt_heap_bump hout.1
      rw [hmem]
      refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Janus.Arm64.Memory.accessible_writeLE]
  · rw [hpn]; rw [hmem]; exact hpost'
  · rw [hwr]
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
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
theorem static_box_finish64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {n : Nat} (hn : n ≤ 8) {ws : List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords64 s sp.nargs) s.mem = [])
    (hcost : ls.cost (argWords64 s sp.nargs) s.mem = 0)
    (hfresh : ∀ r0 r1 r2, ls.fresh (argWords64 s sp.nargs) s.mem r0 r1 r2 = [])
    (hkeep : ∀ r0 r1 r2, ls.keep (argWords64 s sp.nargs) s.mem r0 r1 r2 = [])
    (hws : ∀ w ∈ ws, WBUF ≤ w.1 ∧ w.1 + w.2.1 ≤ WBUF + 8 * n)
    (hpost : ∀ r1 r2, (applyWrites s.mem ws).accessible WBUF (8 * n) true = true →
      sp.post (toyRt tys) (argWords64 s sp.nargs) s.mem WBUF r1 r2 (applyWrites s.mem ws))
    (pre : RtLivePre64 4096 (toyR tys ok) sp ls addr L b s)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 WBUF) (hmem : fin.mem = applyWrites s.mem ws) :
    RtLivePost64 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  obtain ⟨p, hpm, hH, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩ := hinvT
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) :=
    ⟨p, hpm, hH, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩
  have hacW' : s.mem.accessible WBUF 64 true = true := by rw [← view_accessible (toyRt tys) L s.mem]; exact hacW
  have hn0 : (BitVec.ofNat 64 WBUF).toNat = WBUF := by decide
  have hin : ∀ w ∈ ws, InRanges w.1 w.2.1 (toyRt tys) := fun w hw =>
    ⟨(WBUF, WBUF + 64), by simp [toyRt], (hws w hw).1, by have := (hws w hw).2; omega⟩
  have hout : ∀ w ∈ ws, Outside w.1 w.2.1 L := fun w hw =>
    outside_live hL (by have := hws w hw; simp only [WBUF, HEAP] at *; omega)
  have hfr : MemFrame s.mem (applyWrites s.mem ws) (toyRt tys) :=
    memFrame_applyWrites ws hin _ _ (MemFrame.refl _ _)
  refine ⟨BitVec.ofNat 64 WBUF, fin.regs 3, fin.regs 1, fin.regs, fin.flags, fin.xmm, fin.ymmHi, fin.mem,
    fin.zmmHi, fin.kreg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Janus.Contracts.AllocSatAmd64.ret_of s fin [BitVec.ofNat 64 WBUF, fin.regs 3, fin.regs 1]
      hrip h4 h5 h14 (by simpa using h0) (by simp) (by simp) hx hfs hdf hmx hx87 hfw
  · rw [hmem]
    simp only [hrw, rtIf_true, hwr, List.append_nil]
    exact memFrame_applyWrites ws (fun w hw => (hin w hw).append_left _) _ _ (MemFrame.refl _ _)
  · rw [hn0, hmem]
    exact hpost _ _ (by rw [accessible_applyWrites]; exact Janus.Arm64.Memory.accessible_mono _ hacW' (Nat.le_refl _) (by omega))
  · rw [hwr]
    refine ⟨fun a k hinL _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hinL
    have hr' := hL r hr
    rw [hmem]
    refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
    exact bytes_applyWrites_untouched ws (fun w hw => by have := hws w hw; simp only [WBUF, HEAP] at *; omega) _
  · rw [hfresh]; simp [FreshFrom]
  · simp [liveAdds, hfresh, hkeep, LiveApart]
  · simp only [liveAdds, hfresh, hkeep, hcost, List.append_nil, Nat.sub_zero]
    show toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L fin.mem)
    rw [hmem, view_applyWrites_vis ws hin hout]
    exact toyInv.frame hty hn hinvT
      (memFrame_applyWrites ws (fun w hw => ⟨(WBUF, WBUF + 8 * n), List.mem_singleton_self _,
        (hws w hw).1, (hws w hw).2⟩) _ _ (MemFrame.refl _ _))


theorem convt_args2_64 {s : State} {p0 n : Nat} (h : argWords64 s convTstringSpec.nargs = [p0, n]) :
    (s.regs 0).toNat = p0 ∧ (s.regs 3).toNat = n := by
  have h0 := congrArg (fun l => l.getD 0 0) h
  have h1 := congrArg (fun l => l.getD 1 0) h
  exact ⟨by simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, convTstringSpec] using h0, by simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, convTstringSpec] using h1⟩

theorem convt_args1_64 {s : State} {v : Nat} (h : argWords64 s convT64Spec.nargs = [v]) : (s.regs 0).toNat = v := by
  have h0 := congrArg (fun l => l.getD 0 0) h
  simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, convT64Spec] using h0


theorem convTstring_hpost64 {tys : Tys} {s : State} {p0 n A : Nat} (hargs : argWords64 s convTstringSpec.nargs = [p0, n])
    (hn : n ≠ 0) (hA : 16 ≤ A) :
    ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND → (s.mem.writeLE BUMP 8 (p + A)).accessible p 16 true = true →
      convTstringSpec.post (toyRt tys) (argWords64 s convTstringSpec.nargs) s.mem p r1 r2
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) [(p, 8, (s.regs 0).toNat), (p + 8, 8, (s.regs 3).toNat)]) := by
  intro p r1 r2 hp hend hacc
  obtain ⟨h0, h1⟩ := convt_args2_64 hargs
  have hargs2 : argWords64 s 2 = [p0, n] := hargs
  simp only [convTstringSpec, hargs2, arg, List.getD_cons_succ, List.getD_cons_zero, if_neg hn]
  subst h0 h1
  exact convTstring_box (rt := toyRt tys) (m1 := s.mem.writeLE BUMP 8 (p + A)) (p := p)
    (ptr := (s.regs 0).toNat) (len := (s.regs 3).toNat) (s.regs 0).isLt (s.regs 3).isLt
    (by simp only [HEND, HEAP, HSIZE] at hend hp ⊢; omega) (inRanges_heap hp (by omega)) (acc_false hacc)

theorem convTstring_hpost_empty64 {tys : Tys} {s : State} {p0 : Nat} (hargs : argWords64 s convTstringSpec.nargs = [p0, 0]) :
    ∀ r1 r2, (applyWrites s.mem [(WBUF, 8, 0), (WBUF + 8, 8, 0)]).accessible WBUF (8 * 2) true = true →
      convTstringSpec.post (toyRt tys) (argWords64 s convTstringSpec.nargs) s.mem WBUF r1 r2
        (applyWrites s.mem [(WBUF, 8, 0), (WBUF + 8, 8, 0)]) := by
  intro r1 r2 hacc
  have hargs2 : argWords64 s 2 = [p0, 0] := hargs
  simp only [convTstringSpec, hargs2, arg, List.getD_cons_succ, List.getD_cons_zero, if_pos rfl]
  have := convTstring_box (rt := toyRt tys) (m1 := s.mem) (p := WBUF) (ptr := 0) (len := 0)
    (by decide) (by decide) (by decide) (inRanges_wbuf (n := 2) (by omega))
    (by rw [accessible_applyWrites] at hacc; exact acc_false (by simpa using hacc))
  simpa using this

theorem convT64_hpost64 {tys : Tys} {s : State} {v A : Nat} (hargs : argWords64 s convT64Spec.nargs = [v]) (hA : 8 ≤ A) :
    ∀ p r1 r2, HEAP ≤ p → p + A ≤ HEND → (s.mem.writeLE BUMP 8 (p + A)).accessible p 8 true = true →
      convT64Spec.post (toyRt tys) (argWords64 s convT64Spec.nargs) s.mem p r1 r2
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) [(p, 8, (s.regs 0).toNat)]) := by
  intro p r1 r2 hp hend hacc
  have h0 := convt_args1_64 hargs
  have hargs2 : argWords64 s 1 = [v] := hargs
  simp only [convT64Spec, hargs2, arg, List.getD_cons_zero]
  subst h0
  exact convT64_box (rt := toyRt tys) (m1 := s.mem.writeLE BUMP 8 (p + A)) (s.regs 0).isLt
    (by simp only [HEND, HEAP, HSIZE] at hend hp ⊢; omega) (inRanges_heap hp (by omega)) (acc_false hacc)

theorem convT64_hpost_small64 {tys : Tys} {s : State} {v : Nat} (hargs : argWords64 s convT64Spec.nargs = [v]) :
    ∀ r1 r2, (applyWrites s.mem [(WBUF, 8, (s.regs 0).toNat)]).accessible WBUF (8 * 1) true = true →
      convT64Spec.post (toyRt tys) (argWords64 s convT64Spec.nargs) s.mem WBUF r1 r2
        (applyWrites s.mem [(WBUF, 8, (s.regs 0).toNat)]) := by
  intro r1 r2 hacc
  have h0 := convt_args1_64 hargs
  have hargs2 : argWords64 s 1 = [v] := hargs
  simp only [convT64Spec, hargs2, arg, List.getD_cons_zero]
  subst h0
  exact convT64_box (rt := toyRt tys) (m1 := s.mem) (s.regs 0).isLt (by decide) (inRanges_wbuf (n := 1) (by omega))
    (by rw [accessible_applyWrites] at hacc; exact acc_false (by simpa using hacc))

/-! ### The stubs -/

/-- `convTstring` of a non-empty string: `R9 = BUMP; RDX = [R9]; R10 = RDX + A; [R9] = R10; [RDX] = RAX;
[RDX + 8] = RBX; RAX = RDX`. -/
def convTstringCode (A : Nat) : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x11, 0x4c, 0x8d, 0x92] ++ le32 A ++
  [0x4d, 0x89, 0x11, 0x48, 0x89, 0x02, 0x48, 0x89, 0x5a, 0x08, 0x48, 0x89, 0xd0, 0xc3]
def convTstringSeg (addr A : Nat) : Janus.Amd64.Segment := ⟨"live-stub.convTstring", addr, convTstringCode A⟩

/-- `convTstring("")`: two zero words at `WBUF`, `RAX = WBUF`. -/
def convTstringEmptyCode : List Nat :=
  [0x41, 0xb9, 0x00, 0x01, 0x40, 0x00, 0x49, 0xc7, 0x01, 0, 0, 0, 0, 0x49, 0xc7, 0x41, 0x08, 0, 0, 0, 0,
   0x4c, 0x89, 0xc8, 0xc3]
def convTstringEmptySeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.convTstring", addr, convTstringEmptyCode⟩

/-- `convT64(v)`, `v ≥ 256`: a fresh 8-byte box holding `RAX`. -/
def convT64Code (A : Nat) : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x11, 0x4c, 0x8d, 0x92] ++ le32 A ++
  [0x4d, 0x89, 0x11, 0x48, 0x89, 0x02, 0x48, 0x89, 0xd0, 0xc3]
def convT64Seg (addr A : Nat) : Janus.Amd64.Segment := ⟨"live-stub.convT64", addr, convT64Code A⟩

/-- `convT64(v)`, `v < 256`: `v` stored at `WBUF`, `RAX = WBUF`. -/
def convT64SmallCode : List Nat :=
  [0x41, 0xb9, 0x00, 0x01, 0x40, 0x00, 0x49, 0x89, 0x01, 0x4c, 0x89, 0xc8, 0xc3]
def convT64SmallSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.convT64", addr, convT64SmallCode⟩

/-- The barrier buffer is apart from the return-address slot. -/
theorem toy_wbuf_apart64 {tys : Tys} {ok : Nat → List Nat → Prop} {n m : Nat} {s : State}
    (hWs : LiveSep (liveWin64 s 4096 m) (toyR tys ok).rt) (hn : n ≤ 8) :
    Apart WBUF (8 * n) (s.regs 4).toNat 8 := by
  have hw := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
  simp only [Nat.add_sub_cancel_left] at hw
  exact ((inRanges_wbuf (tys := tys) hn).apart hw).symm

end Janus.Contracts.LiveStubAmd64

syntax "janus64_live_convtstring " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_convtstring $n $A $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨p0, hargs⟩ := $hok _ hokx
      have hn : arg (argWords64 s Janus.Contracts.convTstringSpec.nargs) 1 ≠ 0 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convTstring_alloc_live s.mem hn
      have hK16 : 16 ≤ b := hK ▸ hcostx
      have hacB' := Janus.Contracts.LiveSat.bump_acc hinvx
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := 16) (g := (s.regs 14).toNat) (L' := L)
        (tys := _) hinvx hK16
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := 16) (g := (s.regs 14).toNat) (L' := L)
        (tys := _) hinvx hK16
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 hWsx
      have hapH := Janus.Contracts.LiveStubAmd64.toy_heap_apart64 (ob := 16) (g := (s.regs 14).toNat)
        (L := L) (tys := _) hinvx hK16 hWsx
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump hapH
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        refine Janus.Contracts.LiveStubAmd64.alloc_box_finish64 (by decide) (sp := convTstringSpec) (ls := convTstringLive)
          (K := 16) (A := $A)
          (wsf := fun p => [(p, 8, (s.regs 0).toNat), (p + 8, 8, (s.regs 3).toNat)]) rfl rfl
          (by decide) (by decide) (by decide) (by decide) hK hF (fun _ _ _ => rfl)
          (by intro p w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> simp <;> omega)
          (Janus.Contracts.LiveStubAmd64.convTstring_hpost64 hargs (by decide : ($n : Nat) ≠ 0) (by decide : 16 ≤ $A))
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [retAddrOf, setRegF, Janus.Contracts.Toy.BUMP]; done) | (simp; done) | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))

syntax "janus64_live_convtstring_empty " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_convtstring_empty $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨p0, hargs⟩ := $hok _ hokx
      have hn : arg (argWords64 s Janus.Contracts.convTstringSpec.nargs) 1 = 0 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convTstring_empty_live s.mem hn
      have hW := Janus.Contracts.LiveStub.toy_wbuf_acc (g := (s.regs 14).toNat) (L' := L) (tys := _) hinvx
      have hapW := Janus.Contracts.LiveStubAmd64.toy_wbuf_apart64 (n := 2) hWsx (by omega)
      open Janus.Contracts.Toy in
        simp only [WBUF] at hW hapW
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        refine Janus.Contracts.LiveStubAmd64.static_box_finish64 (by decide) (sp := convTstringSpec) (ls := convTstringLive)
          (n := 2) (by decide) (ws := [(Janus.Contracts.Toy.WBUF, 8, 0), (Janus.Contracts.Toy.WBUF + 8, 8, 0)]) rfl rfl
          hK hF (fun _ _ _ => rfl)
          (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl <;> simp)
          (Janus.Contracts.LiveStubAmd64.convTstring_hpost_empty64 hargs)
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [retAddrOf, setRegF, Janus.Contracts.Toy.WBUF]; done) | (simp; done)))

syntax "janus64_live_convt64 " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_convt64 $v $A $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      have hargs := $hok _ hokx
      have hn : ¬ arg (argWords64 s Janus.Contracts.convT64Spec.nargs) 0 < 256 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convT64_alloc_live s.mem hn
      have hK8 : 8 ≤ b := hK ▸ hcostx
      have hacB' := Janus.Contracts.LiveSat.bump_acc hinvx
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := 8) (g := (s.regs 14).toNat) (L' := L)
        (tys := _) hinvx hK8
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := 8) (g := (s.regs 14).toNat) (L' := L)
        (tys := _) hinvx hK8
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 hWsx
      have hapH := Janus.Contracts.LiveStubAmd64.toy_heap_apart64 (ob := 8) (g := (s.regs 14).toNat)
        (L := L) (tys := _) hinvx hK8 hWsx
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump hapH
      generalize hgs : Janus.Contracts.convT64Spec = spX at *
      generalize hgl : Janus.Contracts.convT64Live = lsX at *
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      subst hgs hgl
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        refine Janus.Contracts.LiveStubAmd64.alloc_box_finish64 (by decide) (sp := convT64Spec) (ls := convT64Live)
          (K := 8) (A := $A) (wsf := fun p => [(p, 8, (s.regs 0).toNat)]) rfl rfl
          (by decide) (by decide) (by decide) (by decide) hK hF (fun _ _ _ => rfl)
          (by intro p w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl; simp)
          (Janus.Contracts.LiveStubAmd64.convT64_hpost64 hargs (by decide : 8 ≤ $A))
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [retAddrOf, setRegF, Janus.Contracts.Toy.BUMP]; done) | (simp; done) | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))

syntax "janus64_live_convt64_small " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_convt64_small $hok) => `(tactic| (
      intro L b s hpc pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      have pre0 := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      have hargs := $hok _ hokx
      have hn : arg (argWords64 s Janus.Contracts.convT64Spec.nargs) 0 < 256 := by rw [hargs]; simp [arg]
      obtain ⟨hK, hF⟩ := Janus.Contracts.LiveStub.convT64_small_live s.mem hn
      have hW := Janus.Contracts.LiveStub.toy_wbuf_acc (g := (s.regs 14).toNat) (L' := L) (tys := _) hinvx
      have hapW := Janus.Contracts.LiveStubAmd64.toy_wbuf_apart64 (n := 1) hWsx (by omega)
      open Janus.Contracts.Toy in
        simp only [WBUF] at hW hapW
      generalize hgs : Janus.Contracts.convT64Spec = spX at *
      generalize hgl : Janus.Contracts.convT64Live = lsX at *
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      subst hgs hgl
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        refine Janus.Contracts.LiveStubAmd64.static_box_finish64 (by decide) (sp := convT64Spec) (ls := convT64Live)
          (n := 1) (by decide) (ws := [(Janus.Contracts.Toy.WBUF, 8, (s.regs 0).toNat)]) rfl rfl
          hK hF (fun _ _ _ => rfl)
          (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl; simp)
          (Janus.Contracts.LiveStubAmd64.convT64_hpost_small64 hargs)
          pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | (simp [retAddrOf, setRegF, Janus.Contracts.Toy.WBUF]; done) | (simp; done)))

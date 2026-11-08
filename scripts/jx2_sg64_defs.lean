theorem P_bv' : (BitVec.ofNat 64 P).toNat = poolAddr := by rw [hP]; unfold P; decide
theorem sT_bv' : (BitVec.ofNat 64 sT).toNat = stkType := by rw [hTy]; unfold sT; decide
theorem uT_bv' : (BitVec.ofNat 64 uT).toNat = u64Type := by rw [hU]; unfold uT; decide
theorem pT_bv' : (BitVec.ofNat 64 pT).toNat = ptrType := by rw [hPT]; unfold pT; decide
theorem stk_lt : stkType + 16 ≤ 2 ^ 48 := by rw [hTy]; unfold sT; decide
theorem u64_lt : u64Type + 16 ≤ 2 ^ 48 := by rw [hU]; unfold uT; decide

set_option maxRecDepth 100000 in
/-- The descriptors of `stack` and `uint64` and their readability, in the call state's memory. -/
theorem descs : (s0.mem.readLE stkType 8 = 24 ∧ s0.mem.readLE (stkType + 8) 8 = 8) ∧
    (s0.mem.readLE u64Type 8 = 8 ∧ s0.mem.readLE (u64Type + 8) 8 = 0) ∧
    s0.mem.accessible stkType 16 false = true ∧ s0.mem.accessible u64Type 16 false = true := by
  rw [hTy, hU]
  unfold sT uT
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide +kernel

/-- A write inside the stack window keeps the frame. -/
theorem stkw (spv : Nat) (h1 : sp0 - 4280 ≤ spv) (h2 : spv + 8 ≤ sp0 + 16) :
    MemFrame mem0 (mem0.writeLE spv 8 ret) [(sp0 - 4280, sp0 + 16)] :=
  (MemFrame.refl _ _).writeLE ret (List.mem_singleton_self _) h1 h2

/-- The return address `ret` at `[RSP]` is below `2^47`. -/
theorem ra_ok (m : Arm64.Memory) (spv : Nat) (h : spv < 2 ^ 64) :
    (m.writeLE spv 8 ret).readLE (BitVec.ofNat 64 spv).toNat 8 < 2 ^ 47 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Arm64.Memory.readLE_writeLE_self]
  simp [ret]

/-- A call state at a runtime function's entry: `RSP` `spv`, arguments in `RAX, RBX, RCX, RSI, RDI`. -/
def mkS64 (pcA spv a0 a3 a1 a6 a7 : Nat) (m : Arm64.Memory) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 a0 else if i = 3 then BitVec.ofNat 64 a3
      else if i = 1 then BitVec.ofNat 64 a1 else if i = 6 then BitVec.ofNat 64 a6
      else if i = 7 then BitVec.ofNat 64 a7 else if i = 4 then BitVec.ofNat 64 spv
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 pcA, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := m.writeLE spv 8 ret }

def memP : Arm64.Memory := mem0.writeLE BUMP 8 (HEAP + 32)

theorem invK (k : Nat) (hk : k ≤ 32) :
    R.inv 0x400 [(HEAP, HEAP + k)] (s0.regs 14).toNat (view R.rt [(HEAP, HEAP + k)] memP) := by
  show toyInv tys 0x400 [(HEAP, HEAP + k)] (s0.regs 14).toNat (view (toyRt tys) [(HEAP, HEAP + k)] memP)
  have hb : Outside BUMP 8 [(HEAP, HEAP + k)] := by
    simp only [outside_cons, outside_nil, and_true, BUMP, HEAP]; omega
  refine ⟨HEAP + 32, ?_, by simp [HEAP], by simp [HEAP], by simp [HEAP, HEND, HSIZE], ?_, fun i hi hi' => ?_, ?_, ?_, ?_,
    fun t ht => absurd ht (by simp [tys])⟩
  · rw [readLE_view (inRanges_bump tys) hb, memP, Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simp [HEAP])
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only [HEAP]; omega
  · have ho : Outside i 1 [(HEAP, HEAP + k)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    rw [readLE_view (inRanges_heap (n := 1) (by simp only [HEAP] at *; omega) (by omega)) ho, memP,
      Arm64.Memory.readLE_writeLE_of_disjoint mem0 (a := BUMP) (n := 8) (b := i) (k := 1) (HEAP + 32)
        (by simp only [BUMP, HEAP] at *; omega), Arm64.Memory.readLE_one]
    show (bytes0 i).toNat = 0
    simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]; rfl
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide

/-- The call state at `sync.(*Pool).Get`'s entry (frame 144 below, return address written). -/
def wsG : State := mkS64 (Extracted.program.contractAddr "sync.(*Pool).Get") (sp0 - 144) P 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsG_pre : getSite R [] 0x400 wsG := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsG.regs 14 = s0.regs 14 := by simp [wsG, mkS64, s0]
  have hsp : (wsG.regs 4).toNat + 144 = (s0.regs 4).toNat := by simp [wsG, mkS64, s0, sp0]
  have hra : wsG.mem.readLE (wsG.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf : MemFrame s0.mem wsG.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]; exact stkw _ (by decide) (by decide)
  have h0 : (wsG.regs 0).toNat = poolAddr := by
    have := P_bv'; simpa [wsG, mkS64] using this
  have h := call_pre64 R [] 0x400 0 (Extracted.program.contractAddr "sync.(*Pool).Get") [(wsG.regs 0).toNat]
    (s := s0) (S := wsG) (lo := (s0.regs 4).toNat - 4280) (hi := (s0.regs 4).toNat + 16) (stack := 4096) (nargs := 1)
    (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg' hsp (by omega) hra (by omega) (by omega) (by omega)
    ha4 (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL
    (by rw [h0]; exact hokG) (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  refine ⟨h.1, h.2.1, ?_, h.2.2⟩
  rw [h0]; exact hnew0

/-- The call state at `runtime.newobject`'s entry. -/
def wsN : State := mkS64 (Extracted.program.contractAddr "runtime.newobject") (sp0 - 144) sT 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsN_pre : newSite R [] 0x400 wsN := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsN.regs 14 = s0.regs 14 := by simp [wsN, mkS64, s0]
  have hsp : (wsN.regs 4).toNat + 144 = (s0.regs 4).toNat := by simp [wsN, mkS64, s0, sp0]
  have hra : wsN.mem.readLE (wsN.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf : MemFrame s0.mem wsN.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]; exact stkw _ (by decide) (by decide)
  have h0 : (wsN.regs 0).toNat = stkType := by
    have := sT_bv'; simpa [wsN, mkS64] using this
  have hlt := stk_lt
  have hr : typSize wsN.mem (wsN.regs 0).toNat = 24 := by simp only [typSize]; rw [h0]; exact descs.1.1
  have hp : typPtrBytes wsN.mem (wsN.regs 0).toNat = 8 := by simp only [typPtrBytes]; rw [h0]; exact descs.1.2
  have hround : newobjectRound64 wsN = 24 := by
    simp only [newobjectRound64, hr, typNoscan, hp]; decide
  have h := call_pre64 R [] 0x400 24 (Extracted.program.contractAddr "runtime.newobject") [(wsN.regs 0).toNat]
    (s := s0) (S := wsN) (lo := (s0.regs 4).toNat - 4280) (hi := (s0.regs 4).toNat + 16) (stack := 4096) (nargs := 1)
    (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg' hsp (by omega) hra (by omega) (by omega) (by omega) ha4
    (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL
    (by rw [h0]; exact hokN) (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv) hb24
  unfold newSite
  rw [hround]
  refine ⟨⟨h.1, ⟨by omega, ?_⟩, ?_⟩, h.2.1, h.2.2⟩
  · rw [h0, hf.accessible]; exact descs.2.2.1
  · rw [hr]; simp [maxAlloc]

/-- The call state at `runtime.growslice`'s entry: `growslice(nil, 1, 0, 1, uint64)`. -/
def wsR : State := mkS64 (Extracted.program.contractAddr "runtime.growslice") (sp0 - 144) 0 1 0 uT 1 mem0

set_option maxRecDepth 100000 in
theorem wsR_pre : grSite R [] 0x400 wsR := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsR.regs 14 = s0.regs 14 := by simp [wsR, mkS64, s0]
  have hsp : (wsR.regs 4).toNat + 144 = (s0.regs 4).toNat := by simp [wsR, mkS64, s0, sp0]
  have hra : wsR.mem.readLE (wsR.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf : MemFrame s0.mem wsR.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]; exact stkw _ (by decide) (by decide)
  have hr0 : (wsR.regs 0).toNat = 0 := by simp [wsR, mkS64]
  have hr3 : (wsR.regs 3).toNat = 1 := by simp [wsR, mkS64]
  have hr1 : (wsR.regs 1).toNat = 0 := by simp [wsR, mkS64]
  have hr7 : (wsR.regs 7).toNat = 1 := by simp [wsR, mkS64]
  have hr6 : (wsR.regs 6).toNat = u64Type := by
    have := uT_bv'; simpa [wsR, mkS64] using this
  have hlt := u64_lt
  have hargs : growsliceArgs64 wsR = [0, 1, 0, 1, u64Type] := by
    simp only [growsliceArgs64, hr0, hr1, hr3, hr6, hr7]
  have hround : growsliceRound64 wsR = 8 * growCap8 1 0 := by
    simp only [growsliceRound64, hr3, hr1]
  have hbc := hbud 0 (by omega) (by decide)
  rw [show (1#64).toNat = 1 from rfl] at hbc
  have h := call_pre64 R [] 0x400 (growsliceRound64 wsR) (Extracted.program.contractAddr "runtime.growslice")
    (growsliceArgs64 wsR) (s := s0) (S := wsR) (lo := (s0.regs 4).toNat - 4280) (hi := (s0.regs 4).toNat + 16)
    (stack := 4096) (nargs := 5) (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg' hsp (by omega) hra
    (by omega) (by omega) (by omega) ha4
    (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL
    (by rw [hargs]; exact hokGr 0 0 (by omega) (by decide)) (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv)
    (by rw [hround]; omega)
  refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, h.2.1, h.2.2⟩
  · rw [hr6]; exact descs.2.2.2
  · simp only [typSize, hr6]; exact descs.2.1.1
  · simp only [typPtrBytes, hr6]; exact descs.2.1.2
  · omega
  · omega
  · omega
  · omega
  · intro hpos; rw [hr3, hr7] at hpos; omega

/-- The call state at `runtime.memclrNoHeapPointers`'s entry: clear 8 bytes of the stack window's bottom. -/
def wsM : State := mkS64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") (sp0 - 144) 1044296 8 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsM_pre : memSite R [] 0x400 wsM := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsM.regs 14 = s0.regs 14 := by simp [wsM, mkS64, s0]
  have hsp : (wsM.regs 4).toNat + 144 = (s0.regs 4).toNat := by simp [wsM, mkS64, s0, sp0]
  have hra : wsM.mem.readLE (wsM.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf : MemFrame s0.mem wsM.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]; exact stkw _ (by decide) (by decide)
  have hx15 : wsM.xmm 15 = 0 := rfl
  have hdf : wsM.df = false := rfl
  have h0 : (wsM.regs 0).toNat = 1044296 := by simp [wsM, mkS64]
  have h1 : (wsM.regs 3).toNat = 8 := by simp [wsM, mkS64]
  have h := call_pre64 R [] 0x400 0 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
    [(wsM.regs 0).toNat, (wsM.regs 3).toNat] (s := s0) (S := wsM) (lo := (s0.regs 4).toNat - 4280)
    (hi := (s0.regs 4).toNat + 16) (stack := 4096) (nargs := 2) (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt)
    hg' hsp (by omega) hra (by omega) (by omega) (by omega) ha4
    (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL
    (by rw [h0, h1]; have := hokClr 1044296 0 (by omega) (by decide); simpa using this)
    (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  have hrt : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl
  refine ⟨(memPre64_of hx15 hdf h).1, (memPre64_of hx15 hdf h).2, ?_, ?_, ?_, Or.inr ?_, ?_⟩
  · rw [h0, h1]; omega
  · rw [h0, h1]; exact Arm64.Memory.accessible_mono _ (by rw [hf.accessible]; exact hw4) (by omega) (by omega)
  · rw [h0, h1]
    simp only [calleeStack64, outside_cons, outside_nil, and_true]
    omega
  · rw [h0, h1, hrt]
    simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [h0, h1]
    simp only [outside_cons, outside_nil, and_true]
    omega

/-- The call state at `runtime.gcWriteBarrier2`'s entry. -/
def wsW : State := mkS64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") (sp0 - 144) 0 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsW_pre : wbSite R [] 0x400 wsW := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsW.regs 14 = s0.regs 14 := by simp [wsW, mkS64, s0]
  have hsp : (wsW.regs 4).toNat + 144 = (s0.regs 4).toNat := by simp [wsW, mkS64, s0, sp0]
  have hra : wsW.mem.readLE (wsW.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf : MemFrame s0.mem wsW.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]; exact stkw _ (by decide) (by decide)
  have h := call_pre64 R [] 0x400 0 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2]
    (s := s0) (S := wsW) (lo := (s0.regs 4).toNat - 4280) (hi := (s0.regs 4).toNat + 16) (stack := 4096) (nargs := 0)
    (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg' hsp (by omega) hra (by omega) (by omega) (by omega) ha4
    (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL
    hokWb (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  refine ⟨h.1, hokWb, by rw [hg']; exact RtInv.inv_frame hf hwrt hinv, fun r hr => absurd hr (by simp),
    LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega)⟩

/-- The call state at `sync.(*Pool).Put`'s entry: the zeroed stack header `[HEAP, HEAP+24)` (live) in `RCX`. -/
def wsU : State := mkS64 (Extracted.program.contractAddr "sync.(*Pool).Put") (sp0 - 184) P pT HEAP 0 0 memP

set_option maxRecDepth 100000 in
theorem wsU_pre : putSite R 1 [(HEAP, HEAP + 24)] 0x400 [(HEAP, HEAP + 24)] wsU := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  have hg3 := hg.below
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb4 ha4 hw4 hal
  have hs := s0_sp
  simp only [sp0] at hs
  have hg' : wsU.regs 14 = s0.regs 14 := by simp [wsU, mkS64, s0]
  have hsp : (wsU.regs 4).toNat + 184 = (s0.regs 4).toNat := by simp [wsU, mkS64, s0, sp0]
  have hra : wsU.mem.readLE (wsU.regs 4).toNat 8 < 2 ^ 47 := ra_ok _ _ (by decide)
  have hf0 : MemFrame memP wsU.mem [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [s0_sp]
    exact (MemFrame.refl memP _).writeLE ret (List.mem_singleton_self _) (by simp only [sp0]; omega)
      (by simp only [sp0]; omega)
  have hf : MemFrame s0.mem wsU.mem (R.rt ++ [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)]) :=
    MemFrame.trans (rs := R.rt ++ [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)])
      ((MemFrame.refl _ _).writeLE_inRanges _ ((inRanges_bump tys).append_left _)) hf0 (by frame_sub)
  have h0 : (wsU.regs 0).toNat = poolAddr := by
    have := P_bv'; simpa [wsU, mkS64] using this
  have h1 : (wsU.regs 3).toNat = ptrType := by
    have := pT_bv'; simpa [wsU, mkS64] using this
  have h2 : (wsU.regs 1).toNat = HEAP := by simp [wsU, mkS64, HEAP]
  have hwL1 : LiveSep [(HEAP, HEAP + 24)] [((s0.regs 4).toNat - 4280, (s0.regs 4).toNat + 16)] := by
    rw [hs]; simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, HEAP]; omega
  have h := call_pre64 R [(HEAP, HEAP + 24)] 0x400 0 (Extracted.program.contractAddr "sync.(*Pool).Put")
    [(wsU.regs 0).toNat] (s := s0) (S := wsU) (lo := (s0.regs 4).toNat - 4280) (hi := (s0.regs 4).toNat + 16)
    (stack := 4096) (nargs := 3) (fr := 184) hg1 hg2 (by omega) hgo hf hg' hsp (by omega) hra (by omega) (by omega)
    (by omega) ha4
    (by rw [show (s0.regs 4).toNat + 16 - ((s0.regs 4).toNat - 4280) = 4280 + 16 by omega]; exact hw4) hwrt hwL1
    (by rw [h0]; exact hokP)
    (by rw [hg']; exact RtInv.inv_frame hf0 hwrt (invK 24 (by omega))) (Nat.zero_le _)
  refine ⟨h.1, h.2.1, h1, ?_, fun r hr => hr, h.2.2⟩
  rw [h2]
  refine sliceObj_zero (by decide) (by simp [HEAP]) (by simp [HEAP]) (by simp [HEAP]) ?_ ?_
  · show (memP.writeLE _ 8 ret).accessible HEAP 24 true = true
    simp only [memP, Arm64.Memory.accessible_writeLE]; decide
  · intro i hi
    show (memP.writeLE (sp0 - 184) 8 ret).bytes (HEAP + i) = 0
    rw [Arm64.Memory.bytes_writeLE_outside memP (by simp only [sp0, HEAP]; omega), memP,
      Arm64.Memory.bytes_writeLE_outside mem0 (by simp only [BUMP, HEAP]; omega)]
    show bytes0 (HEAP + i) = 0
    simp only [bytes0, dataByte_none (HEAP + i) (by simp only [HEAP]; omega)]
    rw [if_neg (by simp only [BUMP, HEAP]; omega), if_neg (by simp only [sp0, HEAP]; omega)]

/-- The main post at the witness's values, from `correctness`. -/
theorem returnsPost : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R 1 1 [] 0x400 s0 s' :=
  correctness implAt R (SliceObj 1) 1 (by decide) (by rw [aG, hPT]; exact hget) (by rw [aP, hPT]; exact hput)
    (by rw [aN]; exact hnew) (by rw [aGr]; exact hgrow) (by rw [aM]; exact hclr) (by rw [aW]; exact hwb)
    1 [] 0x400 ret hret s0 setup ⟨⟨rfl, hfl'⟩, pre⟩

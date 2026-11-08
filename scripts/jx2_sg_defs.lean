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

/-- A call state of `StackGrow(1)` at a runtime function's entry: callee `SP` `spv`, arguments in `X0 … X4`. -/
def mkS (pcA spv a0 a1 a2 a3 a4 : Nat) (m : Memory) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 a0 else if i = 1 then BitVec.ofNat 64 a1
      else if i = 2 then BitVec.ofNat 64 a2 else if i = 3 then BitVec.ofNat 64 a3
      else if i = 4 then BitVec.ofNat 64 a4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 spv, pc := BitVec.ofNat 64 pcA, flags := ⟨false, false, false, false⟩, mem := m }

/-- The live set `[(HEAP, HEAP + k)]`, `k ≤ 32`, with the bump pointer at `HEAP + 32`. -/
def memP : Memory := mem0.writeLE BUMP 8 (HEAP + 32)

theorem invK (k : Nat) (hk : k ≤ 32) :
    R.inv 0x400 [(HEAP, HEAP + k)] (s0.regs 28).toNat (view R.rt [(HEAP, HEAP + k)] memP) := by
  show toyInv tys 0x400 [(HEAP, HEAP + k)] (s0.regs 28).toNat (view (toyRt tys) [(HEAP, HEAP + k)] memP)
  have hb : Outside BUMP 8 [(HEAP, HEAP + k)] := by
    simp only [outside_cons, outside_nil, and_true, BUMP, HEAP]; omega
  refine ⟨HEAP + 32, ?_, by simp [HEAP], by simp [HEAP], by simp [HEAP, HEND, HSIZE], ?_, fun i hi hi' => ?_, ?_, ?_, ?_,
    fun t ht => absurd ht (by simp [tys])⟩
  · rw [readLE_view (inRanges_bump tys) hb, memP, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simp [HEAP])
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only [HEAP]; omega
  · have ho : Outside i 1 [(HEAP, HEAP + k)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    rw [readLE_view (inRanges_heap (n := 1) (by simp only [HEAP] at *; omega) (by omega)) ho, memP,
      Memory.readLE_writeLE_of_disjoint mem0 (a := BUMP) (n := 8) (b := i) (k := 1) (HEAP + 32)
        (by simp only [BUMP, HEAP] at *; omega), Memory.readLE_one]
    show (bytes0 i).toNat = 0
    simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]; rfl
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide

/-- The call state at `sync.(*Pool).Get`'s entry (the frame is 144 below the entry `SP`). -/
def wsG : State := mkS (Extracted.program.contractAddr "sync.(*Pool).Get") (sp0 - 144) P 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsG_pre : getSite R [] 0x400 wsG := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsG.regs 28 = s0.regs 28 := by simp [wsG, mkS, s0]
  have hsp : wsG.sp.toNat + 144 = s0.sp.toNat := by simp [wsG, mkS, s0, sp0]
  have h30a : (wsG.regs 30).toNat % 4 = 0 := by simp [wsG, mkS, ret]
  have h30b : (wsG.regs 30).toNat < 2 ^ 48 := by simp [wsG, mkS, ret]
  have hf : MemFrame s0.mem wsG.mem [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := MemFrame.refl _ _
  have h0 : (wsG.regs 0).toNat = poolAddr := by
    have := P_bv'; simpa [wsG, mkS] using this
  have h := call_pre R [] 0x400 0 (Extracted.program.contractAddr "sync.(*Pool).Get") [(wsG.regs 0).toNat]
    (s := s0) (S := wsG) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24) (stack := 4096) (nargs := 1) (fr := 144)
    hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega)
    (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
    (by rw [h0]; exact hokG) (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  refine ⟨h.1, h.2.1, ?_, h.2.2⟩
  rw [h0]; exact hnew0

/-- The call state at `runtime.newobject`'s entry (`stack`'s descriptor in `X0`). -/
def wsN : State := mkS (Extracted.program.contractAddr "runtime.newobject") (sp0 - 144) sT 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsN_pre : newSite R [] 0x400 wsN := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsN.regs 28 = s0.regs 28 := by simp [wsN, mkS, s0]
  have hsp : wsN.sp.toNat + 144 = s0.sp.toNat := by simp [wsN, mkS, s0, sp0]
  have h30a : (wsN.regs 30).toNat % 4 = 0 := by simp [wsN, mkS, ret]
  have h30b : (wsN.regs 30).toNat < 2 ^ 48 := by simp [wsN, mkS, ret]
  have hf : MemFrame s0.mem wsN.mem [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := MemFrame.refl _ _
  have h0 : (wsN.regs 0).toNat = stkType := by
    have := sT_bv'; simpa [wsN, mkS] using this
  have hlt := stk_lt
  have hr : typSize wsN.mem (wsN.regs 0).toNat = 24 := by simp only [typSize]; rw [h0]; exact descs.1.1
  have hp : typPtrBytes wsN.mem (wsN.regs 0).toNat = 8 := by simp only [typPtrBytes]; rw [h0]; exact descs.1.2
  have hround : newobjectRound wsN = 24 := by
    simp only [newobjectRound, hr, typNoscan, hp]; decide
  have h := call_pre R [] 0x400 24 (Extracted.program.contractAddr "runtime.newobject") [(wsN.regs 0).toNat]
    (s := s0) (S := wsN) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24) (stack := 4096) (nargs := 1)
    (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide)
    (by omega) (by omega) (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
    (by rw [h0]; exact hokN) (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) hb24
  unfold newSite
  rw [hround]
  refine ⟨⟨h.1, ⟨by omega, ?_⟩, ?_⟩, h.2.1, h.2.2⟩
  · rw [h0]; exact descs.2.2.1
  · rw [hr]; simp [maxAlloc]

/-- The call state at `runtime.growslice`'s entry: `growslice(nil, 1, 0, 1, uint64)`. -/
def wsR : State := mkS (Extracted.program.contractAddr "runtime.growslice") (sp0 - 144) 0 1 0 1 uT mem0

set_option maxRecDepth 100000 in
theorem wsR_pre : grSite R [] 0x400 wsR := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsR.regs 28 = s0.regs 28 := by simp [wsR, mkS, s0]
  have hsp : wsR.sp.toNat + 144 = s0.sp.toNat := by simp [wsR, mkS, s0, sp0]
  have h30a : (wsR.regs 30).toNat % 4 = 0 := by simp [wsR, mkS, ret]
  have h30b : (wsR.regs 30).toNat < 2 ^ 48 := by simp [wsR, mkS, ret]
  have hf : MemFrame s0.mem wsR.mem [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := MemFrame.refl _ _
  have hr0 : (wsR.regs 0).toNat = 0 := by simp [wsR, mkS]
  have hr1 : (wsR.regs 1).toNat = 1 := by simp [wsR, mkS]
  have hr2 : (wsR.regs 2).toNat = 0 := by simp [wsR, mkS]
  have hr3 : (wsR.regs 3).toNat = 1 := by simp [wsR, mkS]
  have hr4 : (wsR.regs 4).toNat = u64Type := by
    have := uT_bv'; simpa [wsR, mkS] using this
  have hargs : growsliceArgs wsR = [0, 1, 0, 1, u64Type] := by
    simp only [growsliceArgs, hr0, hr1, hr2, hr3, hr4]
  have hround : growsliceRound wsR = 8 * growCap8 1 0 := by
    simp only [growsliceRound, hr1, hr2]
  have hlt := u64_lt
  have hbc := hbud 0 (by omega) (by decide)
  rw [show (1#64).toNat = 1 from rfl] at hbc
  have h := call_pre R [] 0x400 (growsliceRound wsR) (Extracted.program.contractAddr "runtime.growslice")
    (growsliceArgs wsR) (s := s0) (S := wsR) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24) (stack := 4096)
    (nargs := 5) (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide)
    (by omega) (by omega) (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
    (by rw [hargs]; exact hokGr 0 0 (by omega) (by decide)) (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv)
    (by rw [hround]; omega)
  refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, h.2.1, h.2.2⟩
  · rw [hr4]; exact descs.2.2.2
  · simp only [typSize, hr4]; exact descs.2.1.1
  · simp only [typPtrBytes, hr4]; exact descs.2.1.2
  · omega
  · omega
  · omega
  · omega
  · intro hpos; rw [hr1, hr3] at hpos; omega

/-- The call state at `runtime.memclrNoHeapPointers`'s entry: clear 8 bytes of the stack window's bottom. -/
def wsM : State := mkS (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") (sp0 - 144) 1044288 8 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsM_pre : memSite R [] 0x400 wsM := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsM.regs 28 = s0.regs 28 := by simp [wsM, mkS, s0]
  have hsp : wsM.sp.toNat + 144 = s0.sp.toNat := by simp [wsM, mkS, s0, sp0]
  have h30a : (wsM.regs 30).toNat % 4 = 0 := by simp [wsM, mkS, ret]
  have h30b : (wsM.regs 30).toNat < 2 ^ 48 := by simp [wsM, mkS, ret]
  have hf : MemFrame s0.mem wsM.mem [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := MemFrame.refl _ _
  have h0 : (wsM.regs 0).toNat = 1044288 := by simp [wsM, mkS]
  have h1 : (wsM.regs 1).toNat = 8 := by simp [wsM, mkS]
  have h := call_pre R [] 0x400 0 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
    [(wsM.regs 0).toNat, (wsM.regs 1).toNat] (s := s0) (S := wsM) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24)
    (stack := 4096) (nargs := 2) (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b
    (by decide) (by omega) (by omega) (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
    (by rw [h0, h1]; have := hokClr 1044288 0 (by omega) (by decide); simpa using this)
    (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  have hrt : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl
  refine ⟨(memPre_of h).1, (memPre_of h).2, ?_, ?_, ?_, Or.inr ?_⟩
  · rw [h0, h1]; omega
  · rw [h0, h1]; exact Memory.accessible_mono _ hw4 (by omega) (by omega)
  · rw [h0, h1]
    simp only [calleeStack, outside_cons, outside_nil, and_true]
    omega
  · rw [h0, h1, hrt]
    simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide

/-- The call state at `runtime.gcWriteBarrier2`'s entry. -/
def wsW : State := mkS (Extracted.program.contractAddr "runtime.gcWriteBarrier2") (sp0 - 144) 0 0 0 0 0 mem0

set_option maxRecDepth 100000 in
theorem wsW_pre : wbSite R [] 0x400 wsW := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsW.regs 28 = s0.regs 28 := by simp [wsW, mkS, s0]
  have hsp : wsW.sp.toNat + 144 = s0.sp.toNat := by simp [wsW, mkS, s0, sp0]
  have h30a : (wsW.regs 30).toNat % 4 = 0 := by simp [wsW, mkS, ret]
  have h30b : (wsW.regs 30).toNat < 2 ^ 48 := by simp [wsW, mkS, ret]
  have hf : MemFrame s0.mem wsW.mem [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := MemFrame.refl _ _
  have h := call_pre R [] 0x400 0 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2]
    (s := s0) (S := wsW) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24) (stack := 4096) (nargs := 0)
    (fr := 144) hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide)
    (by omega) (by omega) (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL
    hokWb (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
  refine ⟨h.1, hokWb, by rw [hg]; exact RtInv.inv_frame hf hwrt hinv, fun r hr => absurd hr (by simp),
    LiveSep.sub_win_rt hwrt (by omega) (by omega) (by omega)⟩

/-- The call state at `sync.(*Pool).Put`'s entry: the zeroed stack header `[HEAP, HEAP+24)` (live) in `X2`. -/
def wsU : State := mkS (Extracted.program.contractAddr "sync.(*Pool).Put") (sp0 - 192) P pT HEAP 0 0 memP

set_option maxRecDepth 100000 in
theorem wsU_pre : putSite R 1 [(HEAP, HEAP + 24)] 0x400 [(HEAP, HEAP + 24)] wsU := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hsin, hu64, hfacc, hokG, hokP, hokN, hokGr, hokClr, hokWb,
    hnew0, hinv, hn40, hb24, hbud, hcapB⟩ := pre
  have hs := s0_sp
  simp only [sp0] at hs
  have hg : wsU.regs 28 = s0.regs 28 := by simp [wsU, mkS, s0]
  have hsp : wsU.sp.toNat + 192 = s0.sp.toNat := by simp [wsU, mkS, s0, sp0]
  have h30a : (wsU.regs 30).toNat % 4 = 0 := by simp [wsU, mkS, ret]
  have h30b : (wsU.regs 30).toNat < 2 ^ 48 := by simp [wsU, mkS, ret]
  have hf : MemFrame s0.mem wsU.mem (R.rt ++ [(s0.sp.toNat - 4288, s0.sp.toNat + 24)]) :=
    (MemFrame.refl _ _).writeLE_inRanges _ ((inRanges_bump tys).append_left _)
  have h0 : (wsU.regs 0).toNat = poolAddr := by
    have := P_bv'; simpa [wsU, mkS] using this
  have h1 : (wsU.regs 1).toNat = ptrType := by
    have := pT_bv'; simpa [wsU, mkS] using this
  have h2 : (wsU.regs 2).toNat = HEAP := by simp [wsU, mkS, HEAP]
  have hwL1 : LiveSep [(HEAP, HEAP + 24)] [(s0.sp.toNat - 4288, s0.sp.toNat + 24)] := by
    rw [hs]; simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, HEAP]; omega
  have h := call_pre R [(HEAP, HEAP + 24)] 0x400 0 (Extracted.program.contractAddr "sync.(*Pool).Put")
    [(wsU.regs 0).toNat] (s := s0) (S := wsU) (lo := s0.sp.toNat - 4288) (hi := s0.sp.toNat + 24) (stack := 4096)
    (nargs := 3) (fr := 192) hg1 hg2 (by omega) hgo hf hg hsp (by omega) h30a h30b (by decide)
    (by omega) (by omega) (by omega) ha4
    (by rw [show s0.sp.toNat + 24 - (s0.sp.toNat - 4288) = 4288 + 24 by omega]; exact hw4) hwrt hwL1
    (by rw [h0]; exact hokP) (by rw [hg]; exact invK 24 (by omega)) (Nat.zero_le _)
  refine ⟨h.1, h.2.1, h1, ?_, fun r hr => hr, h.2.2⟩
  rw [h2]
  refine sliceObj_zero (by decide) (by simp [HEAP]) (by simp [HEAP]) (by simp [HEAP]) ?_ ?_
  · show memP.accessible HEAP 24 true = true
    simp only [memP, Memory.accessible_writeLE]; decide
  · intro i hi
    show memP.bytes (HEAP + i) = 0
    rw [memP, Memory.bytes_writeLE_outside mem0 (by simp only [BUMP, HEAP]; omega)]
    show bytes0 (HEAP + i) = 0
    simp only [bytes0, dataByte_none (HEAP + i) (by simp only [HEAP]; omega)]
    rw [if_neg (by simp only [BUMP, HEAP]; omega)]

/-- The main post at the witness's values, from `correctness`. -/
theorem returnsPost : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R 1 1 [] 0x400 s0 s' :=
  correctness implAt R (SliceObj 1) 1 (by decide) (by rw [aG, hPT]; exact hget) (by rw [aP, hPT]; exact hput)
    (by rw [aN]; exact hnew) (by rw [aGr]; exact hgrow) (by rw [aM]; exact hclr) (by rw [aW]; exact hwb)
    1 [] 0x400 ret hret s0 setup ⟨⟨rfl, hfl'⟩, pre⟩

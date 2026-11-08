import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
name=sys.argv[1]
path=f'examples/proofs-amd64/{name}/Proof.lean'
FT='FTb' if name=='BigLocal' else 'FTs'
defs='''def mAddr : Nat := Extracted.stubs.head!.addr

/-- The memory at the `morestack` stub: the glue address (the function's entry) at `[RSP]` and the caller's
return address above it. -/
def memm : Memory := (mem0.writeLE (spw + 8) 8 ret).writeLE spw 8 Extracted.entry

theorem memm_desc : memm.readLE G0 8 = SL ∧ memm.readLE (G0 + 8) 8 = SH ∧
    memm.readLE (G0 + 16) 8 = SL + stackGuard := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  refine ⟨?_, ?_, ?_⟩ <;> unfold memm <;>
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0, spw, SL]),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by simp [G0, spw, SL])] <;> assumption

/-- The state at the stub. -/
def sm : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 G0 else if i = 4 then BitVec.ofNat 64 spw else 0,
    rip := BitVec.ofNat 64 mAddr, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := memm }

theorem sm_pre : Janus.Contracts.StackAmd64.MorestackPre64 Extracted.program FTb pool rt H G0 SL SH sm := by
  obtain ⟨d1, d2, d3⟩ := memm_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hsp : (sm.regs 4).toNat = spw := by decide
  have hg : (sm.regs 14).toNat = G0 := by decide
  have eg : gluePcOf sm = Extracted.entry := by decide
  have ef : fspOf sm = spw + 8 := by decide
  have hv : FTb.valid Extracted.entry = true := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
  have hs : FTb.stop Extracted.entry = false := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
  have hi : FTb.injected Extracted.entry = false := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
  have hd : FTb.spdelta Extracted.entry = 0 := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
  have e : Arch.amd64.fp FTb Extracted.entry (spw + 8) = spw + 16 := by
    show spw + 8 + FTb.spdelta Extracted.entry + 8 = spw + 16; rw [hd]
  have e2 : Arch.amd64.fp FTb ret (spw + 16) = spw + 24 := by
    show spw + 16 + FTb.spdelta ret + 8 = spw + 24; rw [show FTb.spdelta ret = 0 from rfl]
  have e3 : Arch.amd64.lrOf sm.mem (spw + 8) (spw + 16) none = ret := by decide
  refine ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by decide,
    ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩,
    by simp [pool, G0, SL, SH, BL, BH], ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_⟩,
    ⟨[⟨Extracted.entry, spw + 8, Arch.amd64.fp FTb Extracted.entry (spw + 8)⟩,
      ⟨ret, spw + 16, spw + 24⟩], ?_⟩, ⟨by decide, by decide⟩, ⟨code, laws.1⟩,
    ⟨rfl, .inl ⟨?_, ?_⟩⟩, ?_⟩
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · rw [eg, ef]
    refine Chain.cons hv hs hi (by decide) (by rw [e]; decide) ?_
    rw [e, e3]
    have := Chain.stop (A := Arch.amd64) (FT := FTb) (m := sm.mem) (hi := SH) (pc := ret) (sp := spw + 16)
      (lr0 := none) rfl rfl rfl (by decide) (by rw [e2]; decide)
    rw [e2] at this; exact this
  · rw [readLE_rtView hin0]; exact d1
  · rw [readLE_rtView hin8]; exact d2
  · exact (mem0_noptr.writeLE _ ⟨(SL, SH), by simp [pool], by decide, by decide⟩).writeLE _
      ⟨(SL, SH), by simp [pool], by decide, by decide⟩
'''
if FT!='FTb': defs=defs.replace('FTb',FT)
c='(∃ (g lo hi : Nat) (s_m : State), Janus.Contracts.StackAmd64.MorestackPre64 Extracted.program FT pool rt H g lo hi s_m)'
RUN={'BigLocal':("GrownReturns64 (Extracted.program.withExit ret) reloc s fun s' => s'.regs 0 = if (0#64).toNat % 16 = 0 then 7#64 else 0",
  "correctness FTb pool rt H (reloc FTb) (contract64 _ FTb) agrees 7#64 0#64 ret hret s0 setup pre"),
 'HoldPtr':("GrownReturns64 (Extracted.program.withExit ret) reloc s fun s' => s'.regs 0 = hres 16#64",
  "correctness FTs pool rt H (reloc FTs) (contract64 _ FTs) env 16#64 ret hret s0 setup pre"),
 'SumRec':("GrownReturns64 (Extracted.program.withExit ret) reloc s fun s' => s'.regs 0 = BitVec.ofNat 64 (sumTo (3#64).toNat)",
  "correctness FTs pool rt H (reloc FTs) (contract64 _ FTs) env 3#64 ret hret s0 setup pre")}
rc,rp=RUN[name]
patch(path,defs,[(c,'⟨G0, SL, SH, sm, sm_pre⟩')],runconj=rc,retproof=rp)

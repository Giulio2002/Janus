import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
name=sys.argv[1]
path=f'examples/proofs/{name}.lean'
defs='''def mAddr : Nat := Extracted.stubs.head!.addr

/-- The state at the `morestack` stub: `s0`'s stack and goroutine, `X30` = the function's entry (the glue after
the call, in the function's frame record) and `X3` = the caller's return address. -/
def sm : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G0 else if i = 29 then BitVec.ofNat 64 (spw - 8)
      else if i = 30 then BitVec.ofNat 64 Extracted.entry else if i = 3 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 spw, pc := BitVec.ofNat 64 mAddr,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem sm_pre : Janus.Contracts.Stack.MorestackPre Extracted.program FTb pool rt H G0 SL SH sm := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  refine ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by decide,
    ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩,
    by simp [pool, G0, SL, SH, BL, BH], ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, ⟨⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_⟩,
    ⟨[⟨Extracted.entry, spw, Arch.arm64.fp FTb Extracted.entry spw⟩, ⟨ret, spw, spw⟩], ?_⟩, ⟨by decide, by decide⟩, ⟨code, laws.1⟩, ⟨rfl, .inl ⟨?_, ?_⟩⟩, mem0_noptr⟩
  · intro r hr
    simp only [pool, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · have e30 : (sm.regs 30).toNat = Extracted.entry := by decide
    have e3 : (sm.regs 3).toNat = ret := by decide
    have esp : sm.sp.toNat = spw := by decide
    have hv : FTb.valid Extracted.entry = true := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
    have hs : FTb.stop Extracted.entry = false := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
    have hi : FTb.injected Extracted.entry = false := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
    have hd : FTb.spdelta Extracted.entry = 0 := by first | decide | rfl | simp [FTb, FrameTable.ofRecs, extraT]
    have e : Arch.arm64.fp FTb Extracted.entry spw = spw := by
      show spw + FTb.spdelta Extracted.entry = spw; rw [hd, Nat.add_zero]
    have e2 : Arch.arm64.fp FTb ret spw = spw := by
      show spw + FTb.spdelta ret = spw; rw [show FTb.spdelta ret = 0 from rfl, Nat.add_zero]
    have inner : Chain Arch.arm64 FTb sm.mem SH ret spw none [⟨ret, spw, spw⟩] := by
      have := Chain.stop (A := Arch.arm64) (FT := FTb) (m := sm.mem) (hi := SH) (pc := ret) (sp := spw)
        (lr0 := none) rfl rfl rfl (by decide) (by rw [e2]; decide)
      rw [e2] at this; exact this
    have hl : Arch.arm64.lrOf sm.mem spw spw (some ret) = ret := by first | rfl | simp [Arch.lrOf]
    rw [e30, e3, esp]
    refine Chain.cons hv hs hi (by decide) (by rw [e]; decide) ?_
    rw [e, hl]; exact inner
  · rw [readLE_rtView hin0]; exact d1
  · rw [readLE_rtView hin8]; exact d2
'''
c='(∃ (g lo hi : Nat) (s_m : State), Janus.Contracts.Stack.MorestackPre Extracted.program FT pool rt H g lo hi s_m)'
RUN={'BigLocal':("GrownReturns (Extracted.program.withExit ret) reloc s fun s' => s'.regs 0 = if (0#64).toNat % 16 = 0 then 7#64 else 0",
  "correctness FTb pool rt H (reloc FTb) (contract _ FTb) 7#64 0#64 ret hret s0 setup ⟨agrees, pre⟩")}
rc,rp=RUN[name]
patch(path,defs,[(c,'⟨G0, SL, SH, sm, sm_pre⟩')],runconj=rc,retproof=rp)

import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
path='examples/proofs/CopyTrees.lean'
defs='''def tmR : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 Janus.Contracts.IfaceModel.TD
  else if i = 1 then BitVec.ofNat 64 DST else if i = 2 then BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL else 0

@[reducible] def tmSite (M : MemModel) (wb d : Nat) (s_c : State) : Prop :=
  TPre M wb d 3 s_c ∧ TypeOK s_c.mem (s_c.regs 0).toNat ∧
    Outside (s_c.regs 0).toNat 16 (calleeStack s_c d 3) ∧
    Input s_c d 3 (s_c.regs 2).toNat (typSize s_c.mem (s_c.regs 0).toNat) ∧
    Dest M s_c d 3 (s_c.regs 1).toNat (typSize s_c.mem (s_c.regs 0).toNat)

theorem tmSite_stock : tmSite M0 WB 64 (MemSat.wstate tmR) := by
  have h0 : ((MemSat.wstate tmR).regs 0).toNat = Janus.Contracts.IfaceModel.TD := by
    simp [tmR, MemSat.wstate, Janus.Contracts.IfaceModel.TD]
  have h1 : ((MemSat.wstate tmR).regs 1).toNat = DST := by simp [tmR, MemSat.wstate, DST]
  have h2 : ((MemSat.wstate tmR).regs 2).toNat = Janus.Contracts.IfaceModel.VAL := by
    simp [tmR, MemSat.wstate, Janus.Contracts.IfaceModel.VAL]
  obtain ⟨ht1, ht2, ht3⟩ := MemSat.wstate_typ tmR 3
  refine ⟨MemSat.wstate_tPre _ 3 (by decide), ?_, ?_, ?_, ?_⟩ <;> simp only [h0, MemSat.wstate_mem]
  · exact ht1
  · exact ht2
  · rw [h2, ht3]; exact MemSat.wstate_input _ 3 _ _ (by decide) (by decide)
  · rw [h1, ht3]; exact MemSat.wstate_dest _ 3 _ _ (by decide) (by decide)

theorem tmSite_pc (M : MemModel) (wb d : Nat) (s : State) (x : BitVec 64) (h : tmSite M wb d s) :
    tmSite M wb d { s with pc := x } := by
  obtain ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩ := h
  exact ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩

def wsCall : State := { MemSat.wstate tmR with pc := BitVec.ofNat 64 cAddr }

theorem wsCall_pre : tmSite M0 WB 64 wsCall := tmSite_pc _ _ _ _ _ tmSite_stock
'''
c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typedmemmove") ∧\n      tmSite M wb d s_c)'
rc=runconj_auto(path,{})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof='correctness implAt M0 M0_laws WB 64 (model WB 64) dst src ret hret s0 setup hpre')

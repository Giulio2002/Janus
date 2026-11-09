import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
path='examples/proofs/ClearTrees.lean'
defs='''def tmR : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 DST else if i = 1 then 64#64 else 0

@[reducible] def clSite (M : MemModel) (wb d : Nat) (s_c : State) : Prop :=
  TPre M wb d 2 s_c ∧ (s_c.regs 0).toNat % 8 = 0 ∧ (s_c.regs 1).toNat % 8 = 0 ∧
    Dest M s_c d 2 (s_c.regs 0).toNat (s_c.regs 1).toNat

theorem clSite_stock : clSite M0 WB 64 (MemSat.wstate tmR) := by
  have h0 : ((MemSat.wstate tmR).regs 0).toNat = DST := by simp [tmR, MemSat.wstate, DST]
  have h1 : ((MemSat.wstate tmR).regs 1).toNat = 64 := by simp [tmR, MemSat.wstate]
  refine ⟨MemSat.wstate_tPre _ 2 (by decide), by rw [h0]; decide, by rw [h1], ?_⟩
  rw [h0, h1]; exact MemSat.wstate_dest _ 2 _ _ (by decide) (by decide)

theorem clSite_pc (M : MemModel) (wb d : Nat) (s : State) (x : BitVec 64) (h : clSite M wb d s) :
    clSite M wb d { s with pc := x } := by
  obtain ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩ := h
  exact ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩

def wsCall : State := { MemSat.wstate tmR with pc := BitVec.ofNat 64 cAddr }

theorem wsCall_pre : clSite M0 WB 64 wsCall := clSite_pc _ _ _ _ _ clSite_stock
'''
c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrHasPointers") ∧\n      clSite M wb d s_c)'
rc=runconj_auto(path,{})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof='correctness implAt M0 M0_laws WB 64 (model WB 64) p n n ret hret s0 setup hpre')

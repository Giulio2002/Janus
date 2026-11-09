import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
path='examples/proofs/StrEq.lean'
defs='''theorem eqpre_pc {d n : Nat} {s : State} (x : BitVec 64) (h : EqPre d n s) :
    EqPre d n { s with pc := x } := by
  obtain ⟨⟨g1, g2, g3⟩, hc, ho⟩ := h
  exact ⟨⟨g1, g2, g3⟩, hc, ho⟩

def wsCall : State := { MemSat.wstate MemSat.eqArgs with pc := BitVec.ofNat 64 cAddr }

@[reducible] def meSite (d : Nat) (s_c : State) : Prop :=
  EqPre d 0 s_c ∧ Input s_c d 0 (s_c.regs 0).toNat (s_c.regs 2).toNat ∧
    Input s_c d 0 (s_c.regs 1).toNat (s_c.regs 2).toNat

theorem wsCall_pre : meSite 64 wsCall :=
  ⟨eqpre_pc _ (MemSat.wstate_eqPre MemSat.eqArgs 0 (by decide)),
    (MemSat.wstate_input MemSat.eqArgs 0 _ _ (by decide) (by decide) :
      Input (MemSat.wstate MemSat.eqArgs) 64 0 (MemSat.eqArgs 0).toNat (MemSat.eqArgs 2).toNat),
    (MemSat.wstate_input MemSat.eqArgs 0 _ _ (by decide) (by decide) :
      Input (MemSat.wstate MemSat.eqArgs) 64 0 (MemSat.eqArgs 1).toNat (MemSat.eqArgs 2).toNat)⟩
'''
c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memequal") ∧\n      meSite d s_c)'
rc=runconj_auto(path,{})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof='correctness implAt 64 (model 64) p l p l ret hret s0 setup hpre')

import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
path='examples/proofs-amd64/StrEq/Proof.lean'
S='Janus.Contracts.MemSatAmd64'
defs=f'''theorem eqpre_rip {{d n : Nat}} {{s : Janus.Amd64.State}} (x : BitVec 64) (h : MemAmd64.EqPre d n s) :
    MemAmd64.EqPre d n {{ s with rip := x }} := by
  obtain ⟨⟨g1, g2, g3⟩, hc, ho⟩ := h
  exact ⟨⟨g1, g2, g3⟩, hc, ho⟩

def cAddr' : Nat := Extracted.program.contractAddr "runtime.memequal"

def wsCall : Janus.Amd64.State :=
  {{ {S}.wstate ({S}.args IfaceModel.VAL IfaceModel.VAL 8 0) with rip := BitVec.ofNat 64 cAddr }}

@[reducible] def meSite (d : Nat) (s_c : Janus.Amd64.State) : Prop :=
  MemAmd64.EqPre d 0 s_c ∧ MemAmd64.Input s_c d 0 (s_c.regs 0).toNat (s_c.regs 1).toNat ∧
    MemAmd64.Input s_c d 0 (s_c.regs 3).toNat (s_c.regs 1).toNat

theorem wsCall_pre : meSite 64 wsCall :=
  ⟨eqpre_rip _ ({S}.wstate_eqPre _ 0 (by decide)), (by simp only [MemAmd64.Input, Janus.Contracts.MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil, wsCall]; decide),
    (by simp only [MemAmd64.Input, Janus.Contracts.MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil, wsCall]; decide)⟩
'''
defs=defs.replace("def cAddr' : Nat := Extracted.program.contractAddr \"runtime.memequal\"\n\n","")
c='(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memequal") ∧\n      meSite d s_c)'
rc=runconj_auto(path,{})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof='correctness implAt 64 (model 64) p l p l ret hret s0 setup hpre')

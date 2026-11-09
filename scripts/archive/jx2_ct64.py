import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
which=sys.argv[1]
S='Janus.Contracts.MemSatAmd64'
INP="simp only [Janus.Contracts.MemAmd64.Input, Janus.Contracts.MemAmd64.StrInput, Janus.Contracts.MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil]; decide"
DST="simp only [Janus.Contracts.MemAmd64.Dest, Janus.Contracts.MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil, Janus.Contracts.EqHashModel.M0]; decide"
TR="""  obtain ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩ := h
  exact ⟨⟨hE, ⟨g1, g2, g3⟩, hc, ho, hi, hw, h1, h2⟩, hr⟩
"""
if which=='ct':
    path='examples/proofs-amd64/CopyTrees/Proof.lean'
    sym='runtime.typedmemmove'; site='tmSite'
    argsE=f"{S}.args Janus.Contracts.IfaceModel.TD DST Janus.Contracts.IfaceModel.VAL 0"
    body=f'''@[reducible] def tmSite (M : MemModel) (wb d : Nat) (s_c : Janus.Amd64.State) : Prop :=
  MemAmd64.TPre M wb d 3 s_c ∧ Janus.Contracts.TypeOK s_c.mem (s_c.regs 0).toNat ∧
    Outside (s_c.regs 0).toNat 16 (MemAmd64.calleeStack s_c d 3) ∧
    MemAmd64.Input s_c d 3 (s_c.regs 1).toNat (Janus.Contracts.typSize s_c.mem (s_c.regs 0).toNat) ∧
    MemAmd64.Dest M s_c d 3 (s_c.regs 3).toNat (Janus.Contracts.typSize s_c.mem (s_c.regs 0).toNat)

theorem tmSite_stock : tmSite M0 WB 64 ({S}.wstate ({argsE})) :=
  ⟨{S}.wstate_tPre _ 3 (by decide), by unfold Janus.Contracts.TypeOK; decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil]; decide,
    by simp only [Janus.Contracts.typSize]; {INP},
    by simp only [Janus.Contracts.typSize]; {DST}⟩
'''
    retproof='correctness implAt M0 M0_laws WB 64 (model WB 64) dst src ret hret s0 setup hpre'
else:
    path='examples/proofs-amd64/ClearTrees/Proof.lean'
    sym='runtime.memclrHasPointers'; site='tmSite'
    argsE=f"{S}.args DST 64 0 0"
    body=f'''@[reducible] def tmSite (M : MemModel) (wb d : Nat) (s_c : Janus.Amd64.State) : Prop :=
  MemAmd64.TPre M wb d 2 s_c ∧ (s_c.regs 0).toNat % 8 = 0 ∧ (s_c.regs 3).toNat % 8 = 0 ∧
    MemAmd64.Dest M s_c d 2 (s_c.regs 0).toNat (s_c.regs 3).toNat

theorem tmSite_stock : tmSite M0 WB 64 ({S}.wstate ({argsE})) :=
  ⟨{S}.wstate_tPre _ 2 (by decide), by decide, by decide, by {DST}⟩
'''
    retproof='correctness implAt M0 M0_laws WB 64 (model WB 64) p n n ret hret s0 setup hpre'
defs=body+f'''
theorem tmSite_rip (M : MemModel) (wb d : Nat) (s : Janus.Amd64.State) (x : BitVec 64) (h : tmSite M wb d s) :
    tmSite M wb d {{ s with rip := x }} := by
{TR}
def wsCall : Janus.Amd64.State := {{ {S}.wstate ({argsE}) with rip := BitVec.ofNat 64 cAddr }}

theorem wsCall_pre : tmSite M0 WB 64 wsCall := tmSite_rip _ _ _ _ _ tmSite_stock
'''
c=f'(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "{sym}") ∧\n      tmSite M wb d s_c)'
rc=runconj_auto(path,{})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof=retproof)

import sys; sys.path.insert(0,'/srv/janus-jx1/scripts')
from jx1gen import patch
P='/srv/janus-jx1/examples/proofs/'
RTPRE='''  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, %s
  simp only [%s_priv, %s_depth, priv0, outside_cons, outside_nil, and_true]; decide
'''
def wscall(name, regs, frame, addr='cA', mem='mem0', dn='wsCall'):
    return f'''/-- The call state of the `{name}` contract (U-WITNESS-CALLSITE): at the callee's entry, the caller's frame lowered. -/
def {dn} : State :=
  {{ regs := fun i => {regs}
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (wsp - {frame}), pc := BitVec.ofNat 64 {addr},
    flags := ⟨false, false, false, false⟩, mem := {mem} }}
'''
def name_suffix(name): return ''
def mapsite(site, ctr, nargs, Mt='MapModel (BitVec 64) (BitVec 64)'):
    return f'''/-- The precondition of `{ctr}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {site} (M : {Mt}) (f : AMap (BitVec 64) (BitVec 64)) (s_c : State) : Prop :=
  RTPre M {nargs} s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f
'''
def conj(site, addr, extra='M', f=True):
    if f: return f'''(∃ (f : AMap (BitVec 64) (BitVec 64)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site} {extra} f s_c)'''
    return f'''(∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site} {extra} s_c)'''
TERM_F=lambda ws: f'⟨AMap.empty, {ws}, by simp only [{ws}]; exact addr.symm ▸ rfl, {ws}_pre⟩'
# ---- Delete
def delete():
    ws=wscall('mapdelete_fast64','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP else if i = 2 then 5',48)
    ws+='''
set_option maxRecDepth 100000 in
theorem wsCall_pre : DeleteSite (ME (BitVec 64)) AMap.empty wsCall := by
'''+RTPRE%('trivial, pre.2.2⟩','ME','ME')
    patch(P+'Delete.lean', mapsite('DeleteSite','Delete',3)+'\n'+ws,
      [conj('DeleteSite','runtime.mapdelete_fast64')], [TERM_F('wsCall')],
      [('s0','s'),('implAt','impl'),('(ME (BitVec 64))','M')])
def clear():
    ws=wscall('mapclear','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP',32)
    ws+='''
set_option maxRecDepth 100000 in
theorem wsCall_pre : ClearSite (ME (BitVec 64)) emp wsCall := by
'''+RTPRE%('trivial, pre.2.2⟩','ME','ME')
    patch(P+'ClearMap.lean', mapsite('ClearSite','Clear',2).replace('RTPre M 2','RTPre M 2')+'\n'+ws,
      [conj('ClearSite','runtime.mapclear')], [TERM_F('wsCall')],
      [('s0','s'),('implAt','impl'),('(ME (BitVec 64))','M')])
if __name__=='__main__':
    for n in sys.argv[1:]: globals()[n]()
def newmap():
    ws=wscall('makemap_small','if i = 0 then 0',16)
    ws=ws.replace('fun i => if i = 0 then 0\n      else if i = 28','fun i => if i = 28')
    site='''/-- The precondition of `MakeSmall`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def MakeSmallSite (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (s_c : State) : Prop :=
  RTPre M 0 s_c ∧ Ready H M.priv [] s_c
'''
    ws+='''
set_option maxRecDepth 100000 in
theorem wsCall_pre : MakeSmallSite (MC ck64) HMake wsCall := by
'''+RTPRE%('by unfold Ready HMake; decide⟩','MC','MC')
    patch(P+'NewMap.lean', site+'\n'+ws,
      [conj('MakeSmallSite','runtime.makemap_small',extra='M H',f=False)],
      ['⟨wsCall, by simp only [wsCall]; exact addr.symm ▸ rfl, wsCall_pre⟩'],
      [('s0','s'),('implAt','impl'),('(MC ck64)','M')])
def insertget():
    wa=wscall('mapassign_fast64','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP else if i = 2 then 5',48,'cA',dn='wsCallA')
    wb=wscall('mapaccess1_fast64','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP else if i = 2 then 5',48,'cB',dn='wsCallB')
    siteA='''/-- The precondition of `Assign`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def AssignSite (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (f : AMap (BitVec 64) (BitVec 64)) (s_c : State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 1).toNat f ∧
    Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, (s_c.regs 2).toNat] s_c
'''
    txt=siteA+'\n'+mapsite('Access1Site','Access1',3)+'\n'+wa+'''
set_option maxRecDepth 100000 in
theorem wsCallA_pre : AssignSite (MC ck64) HAssign AMap.empty wsCallA := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, trivial, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, by unfold Ready HAssign; decide⟩
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide

'''+wb+'''
set_option maxRecDepth 100000 in
theorem wsCallB_pre : Access1Site (MC ck64) AMap.empty wsCallB := by
'''+RTPRE%('trivial, pre.2.2.2.1⟩','MC','MC')
    patch(P+'InsertGet.lean', txt,
      [conj('AssignSite','runtime.mapassign_fast64',extra='M H'), conj('Access1Site','runtime.mapaccess1_fast64')],
      [TERM_F('wsCallA').replace('addr.symm','addr.symm'), TERM_F('wsCallB').replace('addr.symm','addrB.symm')],
      [('s0','s'),('implAt','impl'),('(MC ck64)','M')])
HELP='''theorem rtpre_pc {K V : Type} {M : MapModel K V} {n : Nat} {s : State} (a : BitVec 64) (h : RTPre M n s) :
    RTPre M n { s with pc := a } := h

'''
def lookupptr():
    ws=HELP+'''/-- The call state of the `mapaccess1_fast64` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSat`, at the contract address. -/
def wsCall : State := { mstate mmem (args pv 0) with pc := BitVec.ofNat 64 cAddr }

theorem wsCall_pre : Access1Site (ME (BitVec 64)) AMap.empty wsCall :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard), trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _)⟩
'''
    patch(P+'LookupPtr.lean', mapsite('Access1Site','Access1',3)+'\n'+ws,
      [conj('Access1Site','runtime.mapaccess1_fast64')], ['⟨AMap.empty, wsCall, rfl, wsCall_pre⟩'],
      [('s0','s'),('implAt','impl'),('(ME (BitVec 64))','M'),('(ME _)','M')])
def sumvalues():
    site=HELP+'''/-- The precondition of `IterStart`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def IterStartSite (M : MapModel (BitVec 64) (BitVec 64)) (f : AMap (BitVec 64) (BitVec 64)) (s_c : State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f ∧
    s_c.mem.accessible (s_c.regs 2).toNat iterSize true = true ∧
    Outside (s_c.regs 2).toNat iterSize M.priv ∧ Outside (s_c.regs 2).toNat iterSize (calleeStack s_c M.depth 3)

/-- The precondition of `IterNext`'s summary at the call state `s_c`. -/
@[reducible] def IterNextSite (M : MapModel (BitVec 64) (BitVec 64)) (mp : Nat) (f : AMap (BitVec 64) (BitVec 64))
    (k : BitVec 64) (ks : List (BitVec 64)) (s_c : State) : Prop :=
  RTPre M 1 s_c ∧ IsMap M s_c.mem mp f ∧ M.Iter s_c.mem (s_c.regs 0).toNat mp f (k :: ks) ∧
    Outside (s_c.regs 0).toNat iterSize M.priv ∧ Outside (s_c.regs 0).toNat iterSize (calleeStack s_c M.depth 1)

/-- The call states of the two iteration contracts (U-WITNESS-CALLSITE): the stock witness states of `MapSat`, at the contract addresses. -/
def wsCallS : State := { mstate mmem (args (BitVec.ofNat 64 IT) 0) with pc := BitVec.ofNat 64 sAddr }
def wsCallN : State := { mstate mmem (fun i => if i = 0 then BitVec.ofNat 64 IT else 0) with pc := BitVec.ofNat 64 nAddr }

theorem wsCallS_pre : IterStartSite (MEI (BitVec 64)) AMap.empty wsCallS :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard), trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), by decide,
    by simp only [MEI_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [calleeStack, MEI_depth, outside_cons, outside_nil, and_true]; decide⟩

theorem wsCallN_pre : IterNextSite (MEI (BitVec 64)) MP AMap.empty 7#64 [] wsCallN :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 1 (by decide) mmem_zenv mmem_guard),
    (isMap_of_ne (by decide)).2 (mmem_rep _), ⟨by decide, by decide⟩,
    by simp only [MEI_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [calleeStack, MEI_depth, outside_cons, outside_nil, and_true]; decide⟩
'''
    cs='''(∃ (f : AMap (BitVec 64) (BitVec 64)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapIterStart") ∧ IterStartSite M f s_c)'''
    cn='''(∃ (mp : Nat) (f : AMap (BitVec 64) (BitVec 64)) (k : BitVec 64) (ks : List (BitVec 64)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapIterNext") ∧ IterNextSite M mp f k ks s_c)'''
    patch(P+'SumValues.lean', site, [cs,cn],
      ['⟨AMap.empty, wsCallS, rfl, wsCallS_pre⟩','⟨MP, AMap.empty, 7#64, [], wsCallN, rfl, wsCallN_pre⟩'],
      [('s0','s'),('implAt','impl'),('(MEI (BitVec 64))','M'),('(MEI _)','M')])

import sys,re; sys.path.insert(0,'/srv/janus-jx1/scripts')
from jx1gen import patch
import jx1_arm_map2 as A
S='Janus.Amd64.State'
HELP64='''theorem rtpre_pc {K V : Type} {M : MapModel K V} {n : Nat} {s : Janus.Amd64.State} (a : BitVec 64) (h : RTPre M n s) :
    RTPre M n { s with rip := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩

'''
def path(fn): return f'/srv/janus-jx1/examples/proofs-amd64/{fn}/Proof.lean'
def site(name, ctr, Mt, ft, body, extra=''):
    fp = f'(f : {ft}) ' if ft else ''
    return f'''/-- The precondition of `{ctr}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {name} (M : {Mt}) {extra}{fp}(s_c : {S}) : Prop :=
  {body}
'''
def conj(site_, addr, ft, extra='M'):
    if ft: return f'''(∃ (f : {ft}) (s_c : {S}),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site_} {extra} f s_c)'''
    return f'''(∃ (s_c : {S}), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site_} {extra} s_c)'''
def rterm(fn):
    t=open(path(fn)).read()
    r=t.index('theorem returns'); blk=t[r:t.index('end Witness',r)]
    m=re.search(r'correctness .*?\b(pre0|pre)\b',blk,re.S)
    return re.sub(r'\s+',' ',m.group(0))
def post(fn):
    return A.auto_post(path(fn))
def run(fn, st, ws, pre, cj, terms, derive=None):
    p=path(fn)
    if derive is not None:
        cjs = cj if isinstance(cj,list) else [cj]
        ts = terms if isinstance(terms,list) else [terms]
        patch(p, st+'\n'+ws+'\n'+pre, cjs, ts, [('s0','s'),('implAt','impl')]+derive)
        return
    cjs = cj if isinstance(cj,list) else [cj]
    ts = terms if isinstance(terms,list) else [terms]
    patch(p, st+'\n'+ws+'\n'+pre, cjs, ts, [('s0','s'),('implAt','impl')], returns_term=rterm(fn),
          rstmt_override="ABIReturn s s' ∧ ("+post(fn)+")")
PCM=lambda fnname: 'by show BitVec.ofNat 64 cA = _; rw [addr]'
FT='AMap (BitVec 64) (BitVec 64)'
RT3='rtpre_pc _ (mstate64_rtpre _ rfl rfl mmem64 rfl _ %d (by decide) mmem64_zenv mmem64_guard mmem64_ret)'
def wsdef(c, mem='mmem64', args='(args 7#64 0)', pcx='BitVec.ofNat 64 cA'):
    return f'/-- The call state of the `{c}` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSatAmd64`, at the contract address. -/\ndef wsCall : {S} := {{ mstate64 {mem} {args} with rip := {pcx} }}\n'
PC_A="by show BitVec.ofNat 64 cA = _; rw [addr]"
PC_B="by show BitVec.ofNat 64 cB = _; rw [addrB]"
def mapacc(fn, site_name, ctr_name, addr, pcproof, M, nargs=3, cA='cA', derive=None):
    st=HELP64+site(site_name,ctr_name,'MapModel (BitVec 64) (BitVec 64)',FT,f'RTPre M {nargs} s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f')
    ws=wsdef(addr,pcx=f'BitVec.ofNat 64 {cA}')
    pre=f'''theorem wsCall_pre : {site_name} ({M}) AMap.empty wsCall :=
  ⟨{RT3%nargs}, trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩
'''
    run(fn,st,ws,pre,conj(site_name,addr,FT),'⟨AMap.empty, wsCall, '+pcproof+', wsCall_pre⟩', derive)
DM=[('(ME (BitVec 64))','M'),('(MC ck64)','M')]
def delete(): mapacc('Delete','DeleteSite','Delete','runtime.mapdelete_fast64',PC_A,'ME (BitVec 64)',derive=DM)
def lookup(): mapacc('Lookup','Access2Site','Access2','runtime.mapaccess2_fast64',PC_A,'ME (BitVec 64)',derive=DM)
def clearmap(): mapacc('ClearMap','ClearSite','Clear','runtime.mapclear',PC_A,'ME (BitVec 64)',nargs=2,derive=DM)
def lookupptr(): mapacc('LookupPtr','Access1Site','Access1','runtime.mapaccess1_fast64','rfl','ME (BitVec 64)',cA='cAddr')
def insert():
    st=HELP64+site('AssignSite','Assign','MapModel (BitVec 64) (BitVec 64)',FT,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧\n    Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] s_c',extra='(H : Contracts.RtReady) ')
    pre=f'''theorem wsCall_pre : AssignSite (MC ck64) HAssign AMap.empty wsCall :=
  ⟨{RT3%3}, trivial, by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩
'''
    run('Insert',st,wsdef('mapassign_fast64'),pre,conj('AssignSite','runtime.mapassign_fast64',FT,'M H'),'⟨AMap.empty, wsCall, '+PC_A+', wsCall_pre⟩',DM)
def newmap():
    st=HELP64+'''/-- The precondition of `MakeSmall`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def MakeSmallSite (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 0 s_c ∧ Contracts.Ready64 H M.priv [] s_c
'''
    ws=wsdef('makemap_small',mem='mmem64Dead',args='(args 0 0)')
    pre='''theorem wsCall_pre : MakeSmallSite (MC ck64) HMake wsCall :=
  ⟨rtpre_pc _ (mstate64_rtpre _ rfl rfl mmem64Dead rfl _ 0 (by decide)
      (show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide)) mmem64Dead_guard mmem64Dead_ret),
    hMake_dead64 _ _ _⟩
'''
    run('NewMap',st,ws,pre,conj('MakeSmallSite','runtime.makemap_small',None,'M H'),'⟨wsCall, '+PC_A+', wsCall_pre⟩',DM)
def insertget():
    st=HELP64+site('AssignSite','Assign','MapModel (BitVec 64) (BitVec 64)',FT,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧\n    Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] s_c',extra='(H : Contracts.RtReady) ')
    st+='\n'+site('Access1Site','Access1','MapModel (BitVec 64) (BitVec 64)',FT,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f')
    ws=wsdef('mapassign_fast64').replace('wsCall','wsCallA')+'\n'+wsdef('mapaccess1_fast64',pcx='BitVec.ofNat 64 cB').replace('wsCall','wsCallB')
    pre=f'''theorem wsCallA_pre : AssignSite (MC ck64) HAssign AMap.empty wsCallA :=
  ⟨{RT3%3}, trivial, by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩

theorem wsCallB_pre : Access1Site (MC ck64) AMap.empty wsCallB :=
  ⟨{RT3%3}, trivial, (isMap_of_ne (by decide)).2 (mmem64_repC _)⟩
'''
    run('InsertGet',st,ws,pre,[conj('AssignSite','runtime.mapassign_fast64',FT,'M H'),conj('Access1Site','runtime.mapaccess1_fast64',FT)],
        ['⟨AMap.empty, wsCallA, '+PC_A+', wsCallA_pre⟩','⟨AMap.empty, wsCallB, '+PC_B+', wsCallB_pre⟩'],DM)

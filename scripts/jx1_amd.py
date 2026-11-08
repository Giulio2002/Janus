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
def varfile(fn, site_name, ctr, M, ft, nargs, body, extra, pre_body, addr, cj_extra='M', rterm_override=None):
    st=HELP64+site(site_name,ctr,M[0],ft,body,extra=extra)
    ws=wsdef(addr.split('/')[-1],pcx='BitVec.ofNat 64 cAddr',args=M[2])
    ws=ws.replace('mstate64 mmem64',f'mstate64 {M[3]}')
    pre=f'theorem wsCall_pre : {site_name} {M[1]} AMap.empty wsCall :=\n  {pre_body}\n'
    run(fn,st,ws,pre,conj(site_name,addr,ft,cj_extra),'⟨AMap.empty, wsCall, rfl, wsCall_pre⟩')
RTV=RT3%3
def has32():
    varfile('Has32','Access1F32Site','Access1F32',('MapModel (BitVec 32) (BitVec (8 * 1))','(ME1 (BitVec 32))','(args kv 0)','mmem64'),
      'AMap (BitVec 32) (BitVec (8 * 1))',3,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f','',
      f'⟨{RTV}, trivial, (isMap_of_ne (by decide)).2 mmem64_rep1⟩','runtime.mapaccess1_fast32')
def insertptr():
    varfile('InsertPtr','Assign64PtrSite','Assign64Ptr',('MapModel (BitVec 64) (BitVec (8 * 8))','(MC ck64) HAssign','(args kv 0)','mmem64'),
      'AMap (BitVec 64) (BitVec (8 * 8))',3,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧\n    Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] s_c','(H : Contracts.RtReady) ',
      f'⟨{RTV}, trivial, by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩','runtime.mapassign_fast64ptr','M H')
def makehint():
    st=HELP64+'''/-- The precondition of `MakeMap`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def MakeMapSite (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat = 0 ∧ Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, 0] s_c
'''
    ws=wsdef('makemap',mem='mmem64Dead',args='(args 0 0)',pcx='BitVec.ofNat 64 cAddr')
    pre='''theorem wsCall_pre : MakeMapSite (MC ck64) HMake wsCall :=
  ⟨rtpre_pc _ (mstate64_rtpre _ rfl rfl mmem64Dead rfl _ 3 (by decide)
      (show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide)) mmem64Dead_guard mmem64Dead_ret),
    trivial, by decide, hMake_dead64 _ _ _⟩
'''
    run('MakeHint',st,ws,pre,conj('MakeMapSite','runtime.makemap',None,'M H'),'⟨wsCall, rfl, wsCall_pre⟩')
FS='AMap (Nat × Nat) (BitVec (8 * 8))'
MS='MapModel (Nat × Nat) (BitVec (8 * 8))'
def strfile(fn, site_name, ctr, addr, kind):
    if kind=='insert':
        body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧ StrIn64 s_c M.depth 4 ∧\n    StrOwned M (s_c.regs 1).toNat (s_c.regs 7).toNat ∧\n    Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat, (s_c.regs 7).toNat] s_c'
        extra='(H : Contracts.RtReady) '; M='(MC ckStr) HAssignStr'; a='(args (BitVec.ofNat 64 SK) 8#64)'
        pre=f'''theorem wsCall_pre : {site_name} {M} AMap.empty wsCall := by
  obtain ⟨a, b, c⟩ := strIn_w SK (by decide) (by decide) (Or.inl (by decide)) 4 (by decide)
  exact ⟨{RT3%4}, trivial, by decide, mmem64_repC _, ⟨a, b, c⟩,
    Or.inr (inPriv0 (by decide) (by decide)),
    ⟨by show (Contracts.rtView priv0 mmem64).readLE MP 8 = 0
        rw [readLE_rtView0 (by decide) (by decide)]; decide,
      Or.inr (Or.inl (by decide))⟩⟩
'''
        cx='M H'
    else:
        body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f ∧ StrIn64 s_c M.depth 4'
        extra=''; M='(ME (Nat × Nat))'; a='(args (BitVec.ofNat 64 VAL) 8#64)'
        pre=f'''theorem wsCall_pre : {site_name} {M} AMap.empty wsCall := by
  obtain ⟨a, b, c⟩ := strIn_w VAL (by decide) (by decide) (Or.inr (by decide)) 4 (by decide)
  exact ⟨{RT3%4}, trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _), ⟨a, b, c⟩⟩
'''
        cx='M'
    st=HELP64+site(site_name,ctr,MS,FS,body,extra=extra)
    ws=wsdef(addr.split('_')[-1],pcx='BitVec.ofNat 64 cAddr',args=a)
    run(fn,st,ws,pre,conj(site_name,addr,FS,cx),'⟨AMap.empty, wsCall, rfl, wsCall_pre⟩')
def deletes(): strfile('DeleteS','DeleteStr64Site','DeleteStr64','runtime.mapdelete_faststr','del')
def lookups(): strfile('LookupS','Access1Str64Site','Access1Str64','runtime.mapaccess1_faststr','look')
def inserts(): strfile('InsertS','AssignStr64Site','AssignStr64','runtime.mapassign_faststr','insert')
def set32():
    varfile('Set32','AssignF32Site','AssignF32',('MapModel (BitVec 32) (BitVec (8 * 1))','(MCW ck32) HAssign','(args kv 0)','mmem64'),
      'AMap (BitVec 32) (BitVec (8 * 1))',3,'RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧\n    Contracts.Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (key32 s_c).toNat] s_c','(H : Contracts.RtReady) ',
      f'⟨{RTV}, trivial, by decide, ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩,\n    by show (rtView privW mmem64).readLE MP 8 = 0\n       rw [readLE_rtView (inPrivW (by decide) (by decide))]; decide⟩','runtime.mapassign_fast32','M H')
def sumvalues():
    st=HELP64+'''/-- The precondition of `IterStart`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def IterStartSite (M : MapModel (BitVec 64) (BitVec 64)) (f : AMap (BitVec 64) (BitVec 64)) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f ∧
    s_c.mem.accessible (s_c.regs 1).toNat iterSize true = true ∧
    Outside (s_c.regs 1).toNat iterSize M.priv ∧ Outside (s_c.regs 1).toNat iterSize (calleeStack s_c M.depth 3) ∧
    Outside (s_c.regs 1).toNat iterSize (retSlot s_c)

/-- The precondition of `IterNext`'s summary at the call state `s_c`. -/
@[reducible] def IterNextSite (M : MapModel (BitVec 64) (BitVec 64)) (mp : Nat) (f : AMap (BitVec 64) (BitVec 64))
    (k : BitVec 64) (ks : List (BitVec 64)) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 1 s_c ∧ IsMap M s_c.mem mp f ∧ M.Iter s_c.mem (s_c.regs 0).toNat mp f (k :: ks) ∧
    Outside (s_c.regs 0).toNat iterSize M.priv ∧ Outside (s_c.regs 0).toNat iterSize (calleeStack s_c M.depth 1) ∧
    Outside (s_c.regs 0).toNat iterSize (retSlot s_c)
'''
    ws=wsdef('mapIterStart',pcx='BitVec.ofNat 64 sAddr',args='(args (BitVec.ofNat 64 IT) 0)').replace('wsCall','wsCallS')+'\n'+wsdef('mapIterNext',pcx='BitVec.ofNat 64 nAddr',args='(fun i => if i = 0 then BitVec.ofNat 64 IT else 0)').replace('wsCall','wsCallN')
    pre=f'''theorem wsCallS_pre : IterStartSite (MEi (BitVec 64)) AMap.empty wsCallS :=
  ⟨{RT3%3}, trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _), by decide,
    by simp only [MEi, ME_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.retSlot, outside_cons, outside_nil, and_true]; decide⟩

theorem wsCallN_pre : IterNextSite (MEi (BitVec 64)) MP AMap.empty 0 [] wsCallN :=
  ⟨{RT3%1}, (isMap_of_ne (by decide)).2 (mmem64_rep _), ⟨by decide, by decide⟩,
    by simp only [MEi, ME_priv, priv0, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]; decide,
    by simp only [Janus.Contracts.MapAmd64.retSlot, outside_cons, outside_nil, and_true]; decide⟩
'''
    cs=conj('IterStartSite','runtime.mapIterStart',FT,'M')
    cn=f'''(∃ (mp : Nat) (f : {FT}) (k : BitVec 64) (ks : List (BitVec 64)) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapIterNext") ∧ IterNextSite M mp f k ks s_c)'''
    run('SumValues',st,ws,pre,[cs,cn],['⟨AMap.empty, wsCallS, rfl, wsCallS_pre⟩','⟨MP, AMap.empty, 0, [], wsCallN, rfl, wsCallN_pre⟩'])

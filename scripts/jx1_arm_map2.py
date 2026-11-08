import sys,re; sys.path.insert(0,'/srv/janus-jx1/scripts')
from jx1gen import patch
from jx1_arm_map1 import HELP
P='/srv/janus-jx1/examples/proofs/'
def auto_post(path):
    t=open(path).read()
    c=t.index('theorem correctness'); e=t.index(':= by',c)
    seg=t[c:e]
    i=seg.rindex('(fun ')
    lam=seg[i:].strip()
    assert lam.endswith(')')
    lam=lam[1:-1]
    m=re.match(r"fun (\S+) s' =>\s*",lam)
    body=lam[m.end():]
    if m.group(1) not in ('_','s'): body=re.sub(r'\b'+re.escape(m.group(1))+r'\b','s',body)
    return body
def site(name, ctr, Mt, ft, nargs_pre, extra_params='', body=''):
    return f'''/-- The precondition of `{ctr}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {name} (M : {Mt}) {extra_params}(f : {ft}) (s_c : State) : Prop :=
  {body}
'''
def go(fn, st, wsdef, wspre, conj_, term, rterm, rname='wsCall'):
    path=P+fn+'.lean'
    patch(path, st+'\n'+wsdef+'\n'+wspre, [conj_], [term],
      [('s0','s'),('implAt','impl')], returns_term=rterm,
      rstmt_override="ABIReturn s s' ∧ ("+auto_post(path)+")")
def conjF(site_, addr, ftype, extra='M'):
    return f'''(∃ (f : {ftype}) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site_} {extra} f s_c)'''
STD='⟨AMap.empty, wsCall, rfl, wsCall_pre⟩'
def has32():
    ft='AMap (BitVec 32) (BitVec (8 * 1))'
    st=HELP+site('Access1F32Site','Access1F32','MapModel (BitVec 32) (BitVec (8 * 1))',ft,3,body='RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f')
    ws='/-- The call state of the `mapaccess1_fast32` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem (args kv 0) with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : Access1F32Site (ME1 (BitVec 32)) AMap.empty wsCall :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard), trivial,
    (isMap_of_ne (by decide)).2 mmem_rep1⟩
'''
    go('Has32',st,ws,pre,conjF('Access1F32Site','runtime.mapaccess1_fast32',ft),STD,
       'correctness implAt (ME1 _) (ME1_laws _) model mv kv AMap.empty ret hret s0 setup pre0')
def set32():
    ft='AMap (BitVec 32) (BitVec (8 * 1))'
    st=HELP+site('AssignF32Site','AssignF32','MapModel (BitVec 32) (BitVec (8 * 1))',ft,3,extra_params='(H : RtReady) ',
      body='RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 1).toNat f ∧\n    Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, (key32 s_c).toNat] s_c')
    ws='/-- The call state of the `mapassign_fast32` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem (args kv 0) with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : AssignF32Site (MCW ck32) HAssign AMap.empty wsCall :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard), trivial, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩,
    by show (rtView privW mmem).readLE MP 8 = 0
       rw [readLE_rtView (inPrivW (by decide) (by decide))]; decide⟩
'''
    go('Set32',st,ws,pre,conjF('AssignF32Site','runtime.mapassign_fast32',ft,'M H').replace("(f : ","(f : "),STD.replace('wsCall_pre','wsCall_pre'),
       'correctness implAt (MCW _) (MCW_laws _) HAssign model mv kv AMap.empty ret hret s0 setup pre0')
def insertptr():
    ft='AMap (BitVec 64) (BitVec (8 * 8))'
    st=HELP+site('Assign64PtrSite','Assign64Ptr','MapModel (BitVec 64) (BitVec (8 * 8))',ft,3,extra_params='(H : RtReady) ',
      body='RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 1).toNat f ∧\n    Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, (s_c.regs 2).toNat] s_c')
    ws='/-- The call state of the `mapassign_fast64ptr` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem (args kv 0) with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : Assign64PtrSite (MC ck64) HAssign AMap.empty wsCall :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 3 (by decide) mmem_zenv mmem_guard), trivial, by decide,
    mmem_repC _, hAssign_mmem _ _ _⟩
'''
    go('InsertPtr',st,ws,pre,conjF('Assign64PtrSite','runtime.mapassign_fast64ptr',ft,'M H'),STD,
       'correctness implAt (MC _) (MC_laws _) HAssign model mv kv v AMap.empty ret hret s0 setup pre0')
def makehint():
    st=HELP+'''/-- The precondition of `MakeMap`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def MakeMapSite (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (s_c : State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 2).toNat = 0 ∧ Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, 0] s_c
'''
    ws='/-- The call state of the `makemap` contract (U-WITNESS-CALLSITE): the stock witness state of `MapVarSat`, at the contract address. -/\ndef wsCall : State := { mstate mmemDead (args 0 0) with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : MakeMapSite (MC ck64) HMake wsCall :=
  ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmemDead rfl _ 3 (by decide)
      (show ZEnv mmemDead from mmem_zenv.writeLE _ (by decide)) mmemDead_guard), trivial, by decide,
    hMake_dead _ _ _⟩
'''
    cj='''(∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makemap") ∧ MakeMapSite M H s_c)'''
    go('MakeHint',st,ws,pre,cj,'⟨wsCall, rfl, wsCall_pre⟩','correctness implAt (MC _) (MC_laws _) HMake model n ret hret s0 setup pre0')
def auto_rterm(fn):
    t=open(P+fn+'.lean').read()
    r=t.index('theorem returns'); blk=t[r:t.index('end Witness',r)]
    m=re.search(r'correctness .*?\b(pre0|pre)\b',blk,re.S)
    return re.sub(r'\s+',' ',m.group(0))
def go2(fn, st, ws, pre, conj_, term):
    go(fn,st,ws,pre,conj_,term,auto_rterm(fn))
STRPRE='obtain ⟨a, b, c⟩ := strIn_s\n'
def strsite(name, ctr, vs, extra_p, body_extra, nargs=4):
    return site(name,ctr,f'MapModel (Nat × Nat) (BitVec (8 * {vs}))','AMap (Nat × Nat) (BitVec (8 * 8))',4,extra_params=extra_p,body=body_extra)
FT_S='AMap (Nat × Nat) (BitVec (8 * 8))'
def deletes():
    st=HELP+site('DeleteStrSite','DeleteStr','MapModel (Nat × Nat) (BitVec (8 * 8))',FT_S,4,
      body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f ∧ StrIn s_c M.depth 4')
    ws='/-- The call state of the `mapdelete_faststr` contract (U-WITNESS-CALLSITE): the stock witness state of `MapStrSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem sargs with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : DeleteStrSite (ME (Nat × Nat)) AMap.empty wsCall := by
  obtain ⟨a, b, c⟩ := strIn_s
  exact ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard), trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), ⟨a, b, c⟩⟩
'''
    go2('DeleteS',st,ws,pre,conjF('DeleteStrSite','runtime.mapdelete_faststr',FT_S),STD)
def lookups():
    st=HELP+site('Access1StrSite','Access1Str','MapModel (Nat × Nat) (BitVec (8 * 8))',FT_S,4,
      body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f ∧ StrIn s_c M.depth 4')
    ws='/-- The call state of the `mapaccess1_faststr` contract (U-WITNESS-CALLSITE): the stock witness state of `MapStrSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem sargs with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : Access1StrSite (ME (Nat × Nat)) AMap.empty wsCall := by
  obtain ⟨a, b, c⟩ := strIn_s
  exact ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard), trivial,
    (isMap_of_ne (by decide)).2 (mmem_rep _), ⟨a, b, c⟩⟩
'''
    go2('LookupS',st,ws,pre,conjF('Access1StrSite','runtime.mapaccess1_faststr',FT_S),STD)
def inserts():
    st=HELP+site('AssignStrSite','AssignStr','MapModel (Nat × Nat) (BitVec (8 * 8))',FT_S,4,extra_params='(H : RtReady) ',
      body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 1).toNat f ∧ StrIn s_c M.depth 4 ∧\n    StrOwned M (s_c.regs 2).toNat (s_c.regs 3).toNat ∧\n    Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, (s_c.regs 2).toNat, (s_c.regs 3).toNat] s_c')
    ws='/-- The call state of the `mapassign_faststr` contract (U-WITNESS-CALLSITE): the stock witness state of `MapStrSat`, at the contract address. -/\ndef wsCall : State := { mstate mmem aargs with pc := BitVec.ofNat 64 cAddr }\n'
    pre='''theorem wsCall_pre : AssignStrSite (MC ckStr) HAssignS AMap.empty wsCall := by
  refine ⟨rtpre_pc _ (mstate_rtpre _ rfl rfl mmem rfl _ 4 (by decide) mmem_zenv mmem_guard), trivial, by decide,
    mmem_repC _, ⟨by decide, by decide, ?_⟩, Or.inr (inPriv0 (by decide) (by decide)), ?_, ?_⟩
  · simp only [calleeStack, outside_cons, outside_nil, and_true]
    constructor <;> simp [wsCall, mstate, aargs, args, IfaceModel.wsp, SK]
  · show (rtView priv0 mmem).readLE MP 8 = 0
    rw [readLE_rtView0 (by decide) (by decide)]; decide
  · exact Or.inr (Or.inr (by decide))
'''
    go2('InsertS',st,ws,pre,conjF('AssignStrSite','runtime.mapassign_faststr',FT_S,'M H'),STD)
def lookupstr():
    FS2='AMap (Nat × Nat) (BitVec 64)'
    st=site('Access2StrSite','Access2Str','MapModel (Nat × Nat) (BitVec 64)',FS2,2,
      body='RTPre M 4 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f ∧\n    (s_c.regs 2).toNat + (s_c.regs 3).toNat ≤ 2 ^ 48 ∧ s_c.mem.accessible (s_c.regs 2).toNat (s_c.regs 3).toNat false = true ∧\n    Outside (s_c.regs 2).toNat (s_c.regs 3).toNat (calleeStack s_c M.depth 4)')
    ws='''/-- The call state of the `mapaccess2_faststr` contract (U-WITNESS-CALLSITE): the stock witness state of `MapStrSat`, at the contract address. -/
def wsCall : State :=
  { regs := fun i => if i = 2 then BitVec.ofNat 64 VAL else if i = 3 then 8#64
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩,
    mem := EqHashModel.wmem }
'''
    pre='''theorem wsCall_pre : Access2StrSite MS0 AMap.empty wsCall := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, trivial,
      by simp [IsMap, wsCall], by decide, by decide, ?_⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [calleeStack, MS0, outside_cons, outside_nil, and_true]; decide
'''
    go2('LookupStr',st,ws,pre,conjF('Access2StrSite','runtime.mapaccess2_faststr',FS2),STD)

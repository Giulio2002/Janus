import sys,re; sys.path.insert(0,'/srv/janus-jx1/scripts')
from jx1gen import patch, ident_sub
import jx1_arm_map2 as A
ARM='/srv/janus-jx1/examples/proofs/%s.lean'
AMD='/srv/janus-jx1/examples/proofs-amd64/%s/Proof.lean'
def P(isa,fn): return (ARM if isa=='arm64' else AMD)%fn
ST={'arm64':'State','amd64':'Janus.Amd64.State'}
PC={'arm64':'pc','amd64':'rip'}
def post_of(isa,fn,subs=()):
    b=A.auto_post(P(isa,fn))
    for o,n in subs: b=ident_sub(b,o,n)
    return b
RTPRE_PC={'arm64':'''theorem rtpre_pc {n : Nat} {R : IfaceModel} {s : State} (a : BitVec 64) (h : RTPre R n s) :
    RTPre R n { s with pc := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c, o⟩
''','amd64':'''theorem rtpre_pc {n : Nat} {R : IfaceModel} {s : Janus.Amd64.State} (a : BitVec 64) (h : RTPre R n s) :
    RTPre R n { s with rip := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩
'''}
def conj(isa,site,addr,extra,bind=''):
    s=ST[isa]
    return f'''(∃ {bind}(s_c : {s}), s_c.{PC[isa]} = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site} {extra} s_c)'''
def go(isa,fn,sitedefs,conjs,terms,subs,rterm,extra_post_subs=(),fix=None):
    path=P(isa,fn)
    body=post_of(isa,fn,extra_post_subs)
    patch(path, sitedefs, conjs, terms, [('s0','s'),('implAt','impl')], returns_term=rterm,
          rstmt_override="ABIReturn s s' ∧ ("+body+")")
    if fix:
        t=open(path).read(); assert fix[0] in t; open(path,'w').write(t.replace(fix[0],fix[1]))
def site(isa,name,ctr,params,body):
    return f'''/-- The precondition of `{ctr}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {name} {params}(s_c : {ST[isa]}) : Prop :=
  {body}
'''
def box(isa):
    rp=RTPRE_PC[isa]
    nm='ConvT64Site'
    st=site(isa,nm,'ConvT64','(R : IfaceModel) (H : Janus.Contracts.RtReady) ',
      "RTPre R 1 s_c ∧ "+("Janus.Contracts.Ready64" if isa=='amd64' else "Ready")+" H R.priv [(s_c.regs 0).toNat] s_c")
    ws=f'''/-- The call state of the `runtime.convT64` contract (U-WITNESS-CALLSITE): the stock witness state of `IfaceSat`, at the contract address. -/
def wsCall : {ST[isa]} := {{ wstate (fun i => if i = 0 then 42#64 else 0) with {PC[isa]} := BitVec.ofNat 64 cAddr }}

theorem wsCall_pre : {nm} R0 Htrue wsCall :=
  ⟨rtpre_pc _ (wstate_rtpre _ 1 (by decide)), trivial⟩
'''
    go(isa,'Box',rp+'\n'+st+'\n'+ws,[conj(isa,nm,'runtime.convT64','R H')],['⟨wsCall, rfl, wsCall_pre⟩'],[],
       'correctness implAt R0 R0_laws Htrue model 42#64 ret hret s0 setup ⟨pre, trivial⟩',
       [('x','(42#64)')])

def regs_arm(d): return 'fun i => '+' else '.join(d)+' else 0'
def wsdef(isa, regs, mem, comment, extra_regs=()):
    """regs: list of 'if i = k then v' items"""
    if isa=='arm64':
        items=regs+['if i = 28 then BitVec.ofNat 64 wg','if i = 30 then BitVec.ofNat 64 ret']
        return f'''/-- {comment} -/
def wsCall : State :=
  {{ regs := fun i => {' else '.join(items)} else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := {mem} }}
'''
    items=regs+['if i = 4 then BitVec.ofNat 64 wsp','if i = 14 then BitVec.ofNat 64 wg']
    return f'''/-- {comment} -/
def wsCall : Janus.Amd64.State :=
  {{ regs := fun i => {' else '.join(items)} else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := {mem} }}
'''
def rtpre_refine(isa, env, n):
    if isa=='arm64':
        return f'⟨{env}, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩'
    return f'⟨{env}, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩'
CLOSE='''  all_goals first
    | decide +kernel
    | (simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel)
'''
def ashasher(isa):
    t='1' if isa=='arm64' else '3'
    rd='Ready' if isa=='arm64' else 'Janus.Contracts.Ready64'
    nm='TypeAssertSite'
    body=f'''RTPre R 2 s_c ∧ TADescOK R s_c.mem (s_c.regs 0).toNat ∧ (s_c.regs {t}).toNat ≠ 0 ∧
    ((s_c.regs {t}).toNat ≠ 0 → R.IsType (s_c.regs {t}).toNat ∧
      (taCanFail s_c.mem (s_c.regs 0).toNat = true ∨
        (R.itab (taInter s_c.mem (s_c.regs 0).toNat) (s_c.regs {t}).toNat).isSome)) ∧
    {rd} H R.priv [(s_c.regs 0).toNat, (s_c.regs {t}).toNat] s_c'''
    st=site(isa,nm,'TypeAssert','(R : IfaceModel) (H : Janus.Contracts.RtReady) ',body)
    ws=wsdef(isa,['if i = 0 then BitVec.ofNat 64 desc',f'if i = {t} then td'],'mem1',
      'The call state of the `runtime.typeAssert` contract (U-WITNESS-CALLSITE): `desc` and the type word `td`, in the witness memory.')
    ws+=f'''
set_option maxRecDepth 100000 in
theorem wsCall_pre : {nm} R0 Htrue wsCall := by
  refine ⟨{rtpre_refine(isa,'mem1_env (wsCall.regs '+('28' if isa=='arm64' else '14')+')',2)},
    by show TADescOK R0 mem1 (BitVec.ofNat 64 desc).toNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; exact mem1_desc,
    ?_, fun _ => ⟨Or.inl rfl, Or.inl ?_⟩, trivial⟩
{CLOSE}'''
    go(isa,'AsHasher',RTPRE_PC[isa]+'\n'+st+'\n'+ws,[conj(isa,nm,'runtime.typeAssert','R H')],['⟨wsCall, rfl, wsCall_pre⟩'],[],
       'correctness implAt R0 R0_laws Htrue model td val ret hret s0 setup ⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩',
       fix=('pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial, ⟨wsCall','⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩, ⟨wsCall'))

CLOSE2=CLOSE+'    | exact Or.inl rfl\n'
def classify(isa):
    t='1' if isa=='arm64' else '3'
    rd='Ready' if isa=='arm64' else 'Janus.Contracts.Ready64'
    nm='InterfaceSwitchSite'
    body=f'''RTPre R 2 s_c ∧ ISDescOK R s_c.mem (s_c.regs 0).toNat cs ∧ (s_c.regs {t}).toNat ≠ 0 ∧
    R.IsType (s_c.regs {t}).toNat ∧ {rd} H R.priv [(s_c.regs 0).toNat, (s_c.regs {t}).toNat] s_c'''
    st=site(isa,nm,'InterfaceSwitch','(R : IfaceModel) (H : Janus.Contracts.RtReady) (cs : List Nat) ',body)
    ws=wsdef(isa,['if i = 0 then BitVec.ofNat 64 desc',f'if i = {t} then td'],'mem2',
      'The call state of the `runtime.interfaceSwitch` contract (U-WITNESS-CALLSITE): `desc` and the type word `td`, in the witness memory.')
    ws+=f'''
set_option maxRecDepth 100000 in
theorem wsCall_pre : {nm} R0 Htrue [ID] wsCall := by
  refine ⟨{rtpre_refine(isa,'mem2_env (wsCall.regs '+('28' if isa=='arm64' else '14')+')',2)},
    by show ISDescOK R0 mem2 (BitVec.ofNat 64 desc).toNat [ID]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; exact mem2_desc,
    ?_, ?_, trivial⟩
{CLOSE2}'''
    go(isa,'Classify',RTPRE_PC[isa]+'\n'+st+'\n'+ws,[conj(isa,nm,'runtime.interfaceSwitch','R H cs','(cs : List Nat) ')],['⟨[ID], wsCall, rfl, wsCall_pre⟩'],[],
       'correctness implAt R0 R0_laws Htrue model ID td val ret hret s0 setup ⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩',
       fix=('pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial, ⟨[ID]','⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩, ⟨[ID]'))

def equal(isa):
    a,b=('1','2') if isa=='arm64' else ('3','1')
    nm='EfaceeqSite'
    st=site(isa,nm,'Efaceeq','(R : IfaceModel) ',f'RTPre R 3 s_c ∧ EqOK R s_c.mem (s_c.regs 0).toNat (s_c.regs {a}).toNat (s_c.regs {b}).toNat')
    ws=f'''/-- The call state of the `runtime.efaceeq` contract (U-WITNESS-CALLSITE): the stock witness state of `IfaceSat`, at the contract address. -/
def wsCall : {ST[isa]} := {{ wstate (fun i => if i = 0 then BitVec.ofNat 64 TD else if i = {a} ∨ i = {b} then BitVec.ofNat 64 VAL else 0) with {PC[isa]} := BitVec.ofNat 64 cAddr }}

theorem wsCall_pre : {nm} R0 wsCall :=
  ⟨rtpre_pc _ (wstate_rtpre _ 3 (by decide)), fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩⟩
'''
    go(isa,'Equal',RTPRE_PC[isa]+'\n'+st+'\n'+ws,[conj(isa,nm,'runtime.efaceeq','R')],['⟨wsCall, rfl, wsCall_pre⟩'],[],
       'correctness implAt R0 R0_laws model td val td val ret hret s0 setup pre')

def pc_helpers(isa, inputns, eqns):
    s=ST[isa]; f=PC[isa]
    return f'''theorem eqpre_pc {{d n : Nat}} {{s : {s}}} (a : BitVec 64) (h : {eqns}.EqPre d n s) :
    {eqns}.EqPre d n {{ s with {f} := a }} := by
  obtain ⟨⟨g1, g2, g3⟩, c, o⟩ := h
  exact ⟨⟨g1, g2, g3⟩, c, o⟩

theorem input_pc {{d n x k : Nat}} {{s : {s}}} (a : BitVec 64) (h : {inputns}.Input s d n x k) :
    {inputns}.Input {{ s with {f} := a }} d n x k := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩
'''
def eqfkey(isa):
    nm='MemequalSite'
    ns='Janus.Contracts.Mem' if isa=='arm64' else 'Janus.Contracts.MemAmd64'
    a,b,n=('0','1','2') if isa=='arm64' else ('0','3','1')
    st=site(isa,nm,'Memequal','(d : Nat) ',f'{ns}.EqPre d 0 s_c ∧ {ns}.Input s_c d 0 (s_c.regs {a}).toNat (s_c.regs {n}).toNat ∧\n    {ns}.Input s_c d 0 (s_c.regs {b}).toNat (s_c.regs {n}).toNat')
    ms='Janus.Contracts.MemSat' if isa=='arm64' else 'Janus.Contracts.MemSatAmd64'
    args=f'{ms}.eqArgs' if isa=='arm64' else f'({ms}.args IfaceModel.VAL IfaceModel.VAL 8 0)'
    inp=(lambda: f'{ms}.wstate_input _ 0 _ _ (by decide) (by decide)') if isa=='arm64' else (lambda: 'by inp')
    ws=f'''/-- The call state of the `runtime.memequal` contract (U-WITNESS-CALLSITE): the stock witness state of `MemSat`, at the contract address. -/
def wsCall : {ST[isa]} := {{ {ms}.wstate {args} with {PC[isa]} := BitVec.ofNat 64 cAddr }}

theorem wsCall_pre : {nm} 64 wsCall :=
  ⟨eqpre_pc _ ({ms}.wstate_eqPre _ 0 (by decide)), input_pc _ ({inp()}), input_pc _ ({inp()})⟩
'''
    go(isa,'EqFKey',pc_helpers(isa,ns,ns)+'\n'+st+'\n'+ws,[conj(isa,nm,'runtime.memequal','d')],['⟨wsCall, rfl, wsCall_pre⟩'],[],
       'correctness implAt 64 (model 64) k k ret hret s0 setup hpre')

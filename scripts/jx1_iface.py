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
def go(isa,fn,sitedefs,conjs,terms,subs,rterm,extra_post_subs=()):
    path=P(isa,fn)
    body=post_of(isa,fn,extra_post_subs)
    patch(path, sitedefs, conjs, terms, [('s0','s'),('implAt','impl')], returns_term=rterm,
          rstmt_override="ABIReturn s s' ∧ ("+body+")")
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
if __name__=='__main__':
    for a in sys.argv[2:]: globals()[sys.argv[1]](a)

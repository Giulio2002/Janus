#!/usr/bin/env python3
"""jx2gen: patch an example proof's Witness section with call-site conjuncts.
patch(path, defs, sites, isa='arm64'): defs = Lean text inserted before the nonvacuous docstring;
sites = list of (conjunct_text, proof_text). The `returns` theorem is moved before nonvacuous and
instantiated at the bound state `s` as a Returns conjunct (unless already a conjunct)."""
import re,sys
def patch(path, defs, sites, st='s', has_returns_conj=False, retproof='returns', norun=False, runconj=None):
    t=open(path).read()
    # tail "end Witness ... end Proof"
    m=re.search(r'\nend Witness\s*\nend Proof\s*$',t)
    assert m, 'no tail'
    tail=t[m.start():]; t=t[:m.start()]
    ri=t.index('theorem returns')
    d=t.rfind('/--',0,ri)
    if d>=0 and t[d:ri].rstrip().endswith('-/'): ri=d
    retblk=t[ri:]; t=t[:ri].rstrip()+"\n"
    nv=t.index('theorem nonvacuous')
    nvd=t.rfind('/--',0,nv)
    # returns statement
    rm=re.search(r'theorem returns :(.*?):=\n',retblk,re.S)
    stmt=rm.group(1)
    conj=re.sub(r'\bs0\b',st,stmt).strip()
    t=t[:nvd]+defs.rstrip()+"\n\n"+retblk.rstrip()+"\n\n"+t[nvd:]
    # nonvacuous: find ':=\n  ⟨' at the end
    k=t.rindex(':=\n  ⟨')
    head=t[:k].rstrip(); body=t[k:].rstrip()
    assert body.endswith("⟩"), repr(body[-200:])
    cj=''.join(f" ∧\n    {c}" for c,_ in sites)+f" ∧\n    {conj}"
    pr=''.join(f", {p}" for _,p in sites)+f", {retproof}"
    if norun:
        cj=''.join(f" ∧\n    {c}" for c,_ in sites); pr=''.join(f", {p}" for _,p in sites)
    elif runconj:
        cj=''.join(f" ∧\n    {c}" for c,_ in sites)+f" ∧\n    {runconj}"
    t=head+cj+" "+body[:-1]+pr+"⟩\n"
    open(path,'w').write(t+tail.lstrip('\n') if False else t+tail)

def newobj(name, isa, ty):
    if isa=='arm64':
        path=f'examples/proofs/{name}.lean'
        defs=f'''def cAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- The call state at `runtime.newobject`'s entry (argument `{ty}`, callee `SP` 48 below). -/
def wsCall : State :=
  {{ regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := s0.mem }}

@[reducible] def nwSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : State) : Prop :=
  NewobjectPre 4096 s_c ∧ Ready H rt [(s_c.regs 0).toNat] s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : nwSite rt H wsCall := by
  have h := hH
  have hpt : {ty} = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  exact h
'''
        c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧\n      nwSite rt H s_c)'
    else:
        path=f'examples/proofs-amd64/{name}/Proof.lean'
        defs=f'''def cAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- The call state at `runtime.newobject`'s entry (argument `{ty}`, callee `SP` 32 below). -/
def wsCall : Janus.Amd64.State :=
  {{ regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 4 then BitVec.ofNat 64 (sp0 - 32)
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }}

@[reducible] def nwSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  NewobjectPre64 4096 s_c ∧ Contracts.Ready64 H rt [(s_c.regs 0).toNat] s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : nwSite rt H wsCall := by
  have h := hH
  have hpt : {ty} = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  exact h
'''
        c='(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧\n      nwSite rt H s_c)'
    patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')])

def runconj_auto(path, subst, link='(Extracted.program.link impl)', st='s'):
    """Run conjunct from the `correctness` statement's post: subst = {var: closed term}."""
    t=open(path).read()
    c=t.index('theorem correctness')
    i=t.index('(fun s s\' =>',c)
    d=0;j=i
    while True:
        ch=t[j]
        if ch=='(': d+=1
        elif ch==')':
            d-=1
            if d==0: break
        j+=1
    body=t[i+len("(fun s s' =>"):j].strip()
    # the body is written with s (pre state) and s'
    for k,v in subst.items(): body=re.sub(r'\b'+re.escape(k)+r'\b',v,body)
    if st!='s': body=re.sub(r"\bs\b",st,body)
    return f"Returns ({link}.withExit ret) {st} fun s' => ABIReturn {st} s' ∧\n      ({body})"

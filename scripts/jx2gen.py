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
    nvd=nv
    while True:
        pre_=t[:nvd].rstrip('\n')
        ls=pre_.rfind('\n')+1
        line=pre_[ls:]
        if line.startswith('set_option') and line.endswith(' in'): nvd=ls; continue
        if pre_.endswith('-/'):
            d=pre_.rfind('/--')
            if d>=0 and '\ntheorem' not in pre_[d:] and '\ndef' not in pre_[d:]: nvd=d; continue
        break
    # returns statement
    rm=re.search(r'theorem returns :(.*?):=(?: by)?\n',retblk,re.S)
    stmt=rm.group(1)
    conj=re.sub(r'\bs0\b',st,stmt).strip().replace('link implAt','link impl')
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
    for k,v in subst.items(): body=re.sub(r'(?<![\w.])'+re.escape(k)+r'\b',v,body)
    if st!='s': body=re.sub(r"\bs\b",st,body)
    return f"Returns ({link}.withExit ret) {st} fun s' => ABIReturn {st} s' ∧\n      ({body})"

def rtzero(name, isa, spec, n, kind, sym, ):
    """zero-operand Rt family (H0, stock wmem). kind: 'concat' | 'sbts' (pre: ⟨Or.inl, ⟨dec, simp⟩, absurd⟩)"""
    arm = isa=='arm64'
    path = f'examples/proofs/{name}.lean' if arm else f'examples/proofs-amd64/{name}/Proof.lean'
    St = 'State' if arm else 'Janus.Amd64.State'
    pcf = 'pc' if arm else 'rip'
    pre = 'RtPre' if arm else 'RtPre64'
    if arm:
        regs="(wstate (args [])).regs"
        extra="sp := BitVec.ofNat 64 (wsp - 64), pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩, mem := wmem }"
        cok="⟨by decide, by decide, by decide, by decide, by decide, by decide, Memory.accessible_mono _ hw (by decide) (by decide)⟩"
        wsd="argWords"
    else:
        regs="(wstate (args [])).regs"
        extra="rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := wmem }"
        cok="⟨by decide, by decide, by decide, by decide, Arm64.Memory.accessible_mono _ hw (by decide) (by decide)⟩"
        wsd="argWords64"
    argw = 'argWords' if arm else 'argWords64'
    ws = 'wstate' 
    if kind=='concat':
        pretac=f"""  · intro x hx
    rw [mem_strPairs_zero _ ha _ _ _ hx]
    exact ⟨⟨by decide, by simp⟩, fun h => absurd (ha 0) h⟩"""
        # structure: pre = ⟨Or.inl (ha 0), fun ...⟩
        prepart=f"⟨Or.inl (ha 0), ?_⟩"
        reads=f"""  · intro r hr
    rw [mem_strPairs_zero _ ha _ _ _ hr]
    exact outside_zero _"""
        rest=f"{prepart}, ?_,"
        tacs=pretac+"\n"+reads
        spec_unfold=''
    else:
        rest="?_, ?_,"
        tacs=f"""  · simp only [{spec_head(spec)}] at ha ⊢
    rw [{rewr(kind)}]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [{spec_head(spec)}] at ha ⊢
    unfold ReadsOutside
    rw [{rewr2(kind)}]
    simp [outside_zero]"""
    defs=f'''def cAddr : Nat := Extracted.program.contractAddr "{sym}"

/-- The call state at `{sym}`'s entry (all operands `0`; the stock witness memory). -/
def wsCall : {St} :=
  {{ regs := {regs},
    {extra}

@[reducible] def rpSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : {St}) : Prop :=
  {pre} rt 4096 H ({spec}) s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : rpSite rtW H0 wsCall := by
  have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  have ha : ∀ j, arg ({argw} wsCall ({spec}).nargs) j = 0 := fun j => args_zero _ j (by decide)
  refine ⟨{cok}, {rest} trivial, ready_intro rfl ha⟩
{tacs}
'''
    if kind=='concat':
        defs=defs.replace("refine ⟨"+cok+", "+rest+" trivial, ready_intro rfl ha⟩","refine ⟨"+cok+", "+rest+" trivial, ready_intro rfl ha⟩")
    if 'def cAddr' in open(path).read(): defs=defs.split('\n',2)[2]
    if not arm: defs='open Janus.Contracts.Sat (mem_strPairs_zero outside_zero)\n\n'+defs
    c=f'(∃ s_c : {St}, s_c.{pcf} = BitVec.ofNat 64 (Extracted.program.contractAddr "{sym}") ∧\n      rpSite rt H s_c)'
    return path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')]
def spec_head(spec): return spec.split()[0]
def rewr(kind): return "ha 0, ha 1, ha 2"
def rewr2(kind): return "ha 1, ha 2"

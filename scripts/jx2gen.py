#!/usr/bin/env python3
"""jx2gen: patch an example proof's Witness section with call-site conjuncts.
patch(path, defs, sites, isa='arm64'): defs = Lean text inserted before the nonvacuous docstring;
sites = list of (conjunct_text, proof_text). The `returns` theorem is moved before nonvacuous and
instantiated at the bound state `s` as a Returns conjunct (unless already a conjunct)."""
import re,sys
def patch(path, defs, sites, st='s', has_returns_conj=False, retproof='returns'):
    t=open(path).read()
    # tail "end Witness ... end Proof"
    m=re.search(r'\nend Witness\s*\nend Proof\s*$',t)
    assert m, 'no tail'
    tail=t[m.start():]; t=t[:m.start()]
    ri=t.index('/-- The theorem fires') if '/-- The theorem fires' in t else t.index('theorem returns')
    ri=min(ri, t.index('theorem returns'))
    # docstring start of returns
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
    assert body.endswith('⟩')
    cj=''.join(f" ∧\n    {c}" for c,_ in sites)+f" ∧\n    {conj}"
    pr=''.join(f", {p}" for _,p in sites)+f", {retproof}"
    t=head+cj+" "+body[:-1]+pr+"⟩\n"
    open(path,'w').write(t+tail.lstrip('\n') if False else t+tail)

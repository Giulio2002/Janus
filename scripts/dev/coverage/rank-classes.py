#!/usr/bin/env python3
"""Rank rejected instruction classes over `insn -json` outputs (docs/COVERAGE.md 5.3).

usage: rank-classes.py LABEL=insn.json ...  -> functions blocked / sole blocker per class, then
the greedy order (the class that makes the most functions fully decodable next)."""
import json,sys,collections,re
funcs=[]
for a in sys.argv[1:]:
    lab,p=a.split('=',1)
    d=json.load(open(p))
    for f in d['functions']:
        funcs.append((lab,f['Name'],frozenset(f.get('Classes') or [])))
def norm(c): return re.sub(r' \(vector\)','',c)
blocked=[frozenset(norm(c) for c in cs) for l,n,cs in funcs if cs]
tot=len(funcs)
print(f"functions: {tot}, blocked before: {len(blocked)} ({100*(tot-len(blocked))/tot:.1f}% fully decode)")
cnt=collections.Counter(); sole=collections.Counter()
for cs in blocked:
    for c in cs: cnt[c]+=1
    if len(cs)==1: sole[next(iter(cs))]+=1
print("\n| class | functions blocked | sole blocker |\n|---|---:|---:|")
for c,k in cnt.most_common(): print(f"| `{c}` | {k} | {sole[c]} |")
rem=[set(cs) for cs in blocked]; added=set(); dec=tot-len(blocked)
print("\n| step | class added | + functions | fully decodable |\n|---:|---|---:|---:|")
step=0
while any(rem):
    freq=collections.Counter(c for r in rem for c in r if c not in added)
    best=max(freq, key=lambda c:(sum(1 for r in rem if r and r<=added|{c}), freq[c], c))
    added.add(best)
    gain=sum(1 for r in rem if r and r<=added)
    rem=[set() if (r and r<=added) else r for r in rem]
    dec+=gain; step+=1
    print(f"| {step} | `{best}` | +{gain} | {dec} ({100*dec/tot:.1f}%) |")

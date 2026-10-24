import json,sys
hw={}; md={}; cases={}
for l in open(sys.argv[1]):
    j=json.loads(l); hw[j["id"]]=j
for l in open(sys.argv[2]):
    j=json.loads(l); md[j["id"]]=j
for l in open(sys.argv[3]):
    j=json.loads(l); cases[j["id"]]=j
def norm(x): return int(x,16)
def flags(v): return v & ((1<<0)|(1<<2)|(1<<4)|(1<<6)|(1<<7)|(1<<11))
mm=[]; gap=0; agree=0; bothf=0; err=0
for i,h in hw.items():
    m=md.get(i)
    if m is None: continue
    if h["status"]=="error" or m.get("status")=="error":
        err+=1; continue
    if h["status"] in ("escaped","selfloop"):
        continue
    hwfault = h["status"]=="fault"
    mfault = m["status"]=="fault"
    if hwfault and mfault:
        bothf+=1; agree+=1; continue
    if hwfault and not mfault:
        mm.append((i,"hw fault, model ok",h,m)); continue
    if mfault and not hwfault:
        gap+=1; continue
    # both ok
    diffs=[]
    for r in range(16):
        if norm(h["regs"][r])!=norm(m["regs"][r]): diffs.append(f"reg{r} hw {h['regs'][r]} md {m['regs'][r]}")
    defmask=m.get("defined",0)
    if (h["rflags"]&defmask)!=(m["rflags"]&defmask): diffs.append(f"flags hw {h['rflags']:x} md {m['rflags']:x} defmask {defmask:x}")
    if norm(h["pc"])!=norm(m["pc"]): diffs.append(f"pc hw {h['pc']} md {m['pc']}")
    for r in range(16):
        if norm(h["xmm"][r])!=norm(m["xmm"][r]): diffs.append(f"xmm{r}")
    hm={tuple(x) for x in h.get("mem",[])}; mmm={tuple(x) for x in m.get("mem",[])}
    if hm!=mmm: diffs.append(f"mem hw {sorted(hm)} md {sorted(mmm)}")
    if diffs:
        mm.append((i,"; ".join(diffs),h,m))
    else:
        agree+=1
print(f"agree={agree} (bothfault={bothf}) model-gap={gap} MISMATCH={len(mm)} err={err}")
for i,d,h,m in mm[:20]:
    print("MISMATCH id",i,":",d)
    print("  seq:", cases[i]["seq"])

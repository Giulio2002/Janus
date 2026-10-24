import json,sys
hw={};md={};cs={}
for l in open(sys.argv[1]):
    j=json.loads(l); hw[j["id"]]=j
for l in open(sys.argv[2]):
    j=json.loads(l); md[j["id"]]=j
for l in open(sys.argv[3]):
    j=json.loads(l); cs[j["id"]]=j
def nx(x): return int(x,16)
mm=[];agree=0;bothf=0;gap=0;err=0;unobs=0
for i,h in hw.items():
    m=md.get(i)
    if m is None: continue
    if h["status"]=="error" or m.get("status")=="error": err+=1; continue
    TestPC=0x10_0000_0800
    n=len(cs[i]["words"]); blkend=TestPC+4*n
    hf = h["status"]=="fault"
    if h["status"]=="escaped":
        # a mid-block instruction fault: pc landed inside the block with a fault signal
        pc=nx(h.get("pc","0x0"))
        if TestPC<=pc<blkend and h.get("sig",0) in (4,5,7,8,11):
            hf=True
        else:
            unobs+=1; continue
    elif h["status"]=="selfloop": unobs+=1; continue
    mf=m["status"]=="fault"
    if hf and mf: bothf+=1; agree+=1; continue
    if hf and not mf: mm.append((i,"hw fault model ok",h,m)); continue
    if mf and not hf: gap+=1; continue
    diffs=[]
    for r in range(31):
        if nx(h["x"][r])!=nx(m["x"][r]): diffs.append(f"x{r} hw {h['x'][r]} md {m['x'][r]}")
    if nx(h["sp"])!=nx(m["sp"]): diffs.append("sp")
    if h["nzcv"]!=m["nzcv"]: diffs.append(f"nzcv hw {h['nzcv']} md {m['nzcv']}")
    if nx(h["pc"])!=nx(m["pc"]): diffs.append(f"pc hw {h['pc']} md {m['pc']}")
    hv=h.get("v"); mv=m.get("v")
    if hv and mv:
        for r in range(32):
            if nx(hv[r])!=nx(mv[r]): diffs.append(f"v{r}")
    if h.get("fpcr") and m.get("fpcr") and nx(h["fpcr"])!=nx(m["fpcr"]): diffs.append("fpcr")
    if h.get("fpsr") and m.get("fpsr") and nx(h["fpsr"])!=nx(m["fpsr"]): diffs.append("fpsr")
    hm={tuple(x) for x in h.get("mem",[])}; mmm={tuple(x) for x in m.get("mem",[])}
    if hm!=mmm: diffs.append(f"mem")
    if diffs: mm.append((i,"; ".join(diffs),h,m))
    else: agree+=1
print(f"agree={agree} (bothfault={bothf}) model-gap={gap} MISMATCH={len(mm)} err={err} unobs={unobs}")
for i,d,h,m in mm[:20]:
    print("MISMATCH id",i,":",d); print("  words:",cs[i]["words"])

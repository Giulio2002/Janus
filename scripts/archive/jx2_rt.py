import sys; sys.path.insert(0,'scripts')
from jx2gen import *
name,isa=sys.argv[1],sys.argv[2]
cfg={'Concat':("concatstringSpec 2",5,'concat','runtime.concatstring2'),
 'FromBytes':("slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»",3,'sbts','runtime.slicebytetostring'),
 'ToBytes':("stringtoslicebyteSpec",3,'sbts','runtime.stringtoslicebyte')}
spec,n,kind,sym=cfg[name]
path,defs,sites=rtzero(name,isa,spec,n,kind,sym)
import re
txt=open(path).read()
m=re.search(r"theorem correctness.*?\(H : RtReady\)((?:\s*\([^()]*: BitVec 64\))+)",txt,re.S)
ps=[]
for g in re.findall(r"\(([^()]*): BitVec 64\)",m.group(1)): ps+=g.split()
rc=runconj_auto(path,{k:'(0 : BitVec 64)' for k in ps})
patch(path,defs,sites,runconj=rc,retproof='correctness implAt rtW H0 '+' '.join('0' for _ in ps)+' model ret hret s0 setup pre')

import sys; sys.path.insert(0,'scripts')
from jx2gen import *
name,isa=sys.argv[1],sys.argv[2]
cfg={'Concat':("concatstringSpec 2",5,'concat','runtime.concatstring2'),
 'FromBytes':("slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»",3,'sbts','runtime.slicebytetostring'),
 'ToBytes':("stringtoslicebyteSpec",3,'sbts','runtime.stringtoslicebyte')}
spec,n,kind,sym=cfg[name]
path,defs,sites=rtzero(name,isa,spec,n,kind,sym)
patch(path,defs,sites)

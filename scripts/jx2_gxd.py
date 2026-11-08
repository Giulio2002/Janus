import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
from jx2gp import gp_defs, gr_defs
isa=sys.argv[1]; arm=isa=='arm64'
path='examples/proofs/GoexitDefer.lean' if arm else 'examples/proofs-amd64/GoexitDefer/Proof.lean'
W='0x48000' if arm else '0x4ff00'
d,c,p=gp_defs(isa,'goexit','example.com/basic.GoexitDefer',48 if arm else 40,25,8,'0x6c' if arm else '0x68',
  'loc_GoexitDefer_68' if arm else 'loc_GoexitDefer_69',
  [(32,'func1A'),(24,'0'),(16,f'{W} - 32'),(33,'1')],[(32,0)],1)
d2,c2,p2=gr_defs(isa)
patch(path,d+"\n"+d2,[(c,p),(c2,p2)],subs={'PW':'P','implW':'impl','U0':'U','U1':'U'})

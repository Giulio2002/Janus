import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
from jx2gp import gp_defs
isa=sys.argv[1]; arm=isa=='arm64'
path='examples/proofs/NestedPanic.lean' if arm else 'examples/proofs-amd64/NestedPanic/Proof.lean'
d,c,p=gp_defs(isa,'gopanic','example.com/basic.NestedPanic',96 if arm else 88,57,16,'0x80' if arm else '0x86',
  'loc_NestedPanic_124' if arm else 'loc_NestedPanic_133',
  [(24,'0x48000 - 40' if arm else '0x4ff00 - 40'),(16,'0x48000 - 64' if arm else '0x4ff00 - 64'),(40,'func1A'),(64,'func2A'),(32,'0'),(56,'0'),(48,'0'),(65,'3')],
  [(64,1),(40,0)],3)
subs={'PW':'P','implW':'impl','U0':'U','U1':'U'}
patch(path,d,[(c,p)],subs=subs)

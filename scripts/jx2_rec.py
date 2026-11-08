import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
from jx2gp import gp_defs, gr_defs, dr_defs
name=sys.argv[1]; isa=sys.argv[2]; arm=isa=='arm64'
path=f'examples/proofs/{name}.lean' if arm else f'examples/proofs-amd64/{name}/Proof.lean'
W='0x48000' if arm else '0x4ff00'
if name=='RecoverSet':
    a=dict(F=80 if arm else 64,bo=33,so=8,res='0x84' if arm else '0x86',lr='loc_RecoverSet_128' if arm else 'loc_RecoverSet_133',
      words=[(32,'func1A'),(24,f'{W} - 40'),(16,f'{W} - 32'),(41,'1')],items=[(32,0)],bv=1)
else:
    a=dict(F=112 if arm else 96,bo=65,so=16,res='0x80' if arm else '0x8d',lr='loc_NestedRecover_124' if arm else 'loc_NestedRecover_140',
      words=[(24,f'{W} - 40'),(16,f'{W} - 64'),(40,'func1A'),(64,'func2A'),(32,f'{W} - 72'),(56,'0'),(48,'0'),(73,'3')],items=[(64,1),(40,0)],bv=3)
d,c,p=gp_defs(isa,'gopanic','example.com/basic.'+name,a['F'],a['bo'],a['so'],a['res'],a['lr'],a['words'],a['items'],a['bv'])
d2,c2,p2=gr_defs(isa); d3,c3,p3=dr_defs(isa)
patch(path,d+"\n"+d2+"\n"+d3,[(c,p),(c2,p2),(c3,p3)],subs={'PW':'P','implW':'impl','U0':'U','U1':'U'})

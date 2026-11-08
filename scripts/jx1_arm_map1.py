import sys; sys.path.insert(0,'/srv/janus-jx1/scripts')
from jx1gen import patch
P='/srv/janus-jx1/examples/proofs/'
RTPRE='''  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, %s
  simp only [%s_priv, %s_depth, priv0, outside_cons, outside_nil, and_true]; decide
'''
def wscall(name, regs, frame, addr='cA', mem='mem0'):
    return f'''/-- The call state of the `{name}` contract (U-WITNESS-CALLSITE): at the callee's entry, the caller's frame lowered. -/
def wsCall{name_suffix(name)} : State :=
  {{ regs := fun i => {regs}
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (wsp - {frame}), pc := BitVec.ofNat 64 {addr},
    flags := ⟨false, false, false, false⟩, mem := {mem} }}
'''
def name_suffix(name): return ''
def mapsite(site, ctr, nargs, Mt='MapModel (BitVec 64) (BitVec 64)'):
    return f'''/-- The precondition of `{ctr}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {site} (M : {Mt}) (f : AMap (BitVec 64) (BitVec 64)) (s_c : State) : Prop :=
  RTPre M {nargs} s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 1).toNat f
'''
def conj(site, addr, extra='M', f=True):
    if f: return f'''(∃ (f : AMap (BitVec 64) (BitVec 64)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site} {extra} f s_c)'''
    return f'''(∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "{addr}") ∧ {site} {extra} s_c)'''
TERM_F=lambda ws: f'⟨AMap.empty, {ws}, by simp only [{ws}]; exact addr.symm ▸ rfl, {ws}_pre⟩'
# ---- Delete
def delete():
    ws=wscall('mapdelete_fast64','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP else if i = 2 then 5',48)
    ws+='''
set_option maxRecDepth 100000 in
theorem wsCall_pre : DeleteSite (ME (BitVec 64)) AMap.empty wsCall := by
'''+RTPRE%('trivial, pre.2.2⟩','ME','ME')
    patch(P+'Delete.lean', mapsite('DeleteSite','Delete',3)+'\n'+ws,
      [conj('DeleteSite','runtime.mapdelete_fast64')], [TERM_F('wsCall')],
      [('s0','s'),('implAt','impl'),('(ME (BitVec 64))','M')])
def clear():
    ws=wscall('mapclear','if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP',32)
    ws+='''
set_option maxRecDepth 100000 in
theorem wsCall_pre : ClearSite (ME (BitVec 64)) emp wsCall := by
'''+RTPRE%('trivial, pre.2.2⟩','ME','ME')
    patch(P+'ClearMap.lean', mapsite('ClearSite','Clear',2).replace('RTPre M 2','RTPre M 2')+'\n'+ws,
      [conj('ClearSite','runtime.mapclear')], [TERM_F('wsCall')],
      [('s0','s'),('implAt','impl'),('(ME (BitVec 64))','M')])
if __name__=='__main__':
    for n in sys.argv[1:]: globals()[n]()

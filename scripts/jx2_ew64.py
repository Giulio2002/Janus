import sys,re; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs-amd64/ErrWrap/Proof.lean'
t=open(path).read()
L=t.split('\n')
ci=next(i for i,l in enumerate(L) if l.startswith('theorem correctness'))
sk=next(i for i,l in enumerate(L) if l.startswith('  have key :'))
pf=next(i for i,l in enumerate(L) if l.startswith('  have post_facts'))
ji=next(i for i,l in enumerate(L) if l.startswith('  janus64_intro hs'))
ii=next(i for i in range(ci,ji) if L[i].startswith('  intro ret hret'))
pat=' '.join(x.strip() for x in L[ii:ji]).split('hs ',1)[1]
ke=next(i for i in range(sk,pf) if L[i].rstrip().endswith(':= by'))
concl='\n'.join(L[sk:ke+1]).split('have key :',1)[1].rsplit(':= by',1)[0]
cs=concl.index('(CallOK64 S')
hyps=concl[:cs]; site=concl[cs:].strip()
body=L[ji+1:pf]
lemma=f'''/-- The precondition of the `fmt.errorf` call at its entry `S`. -/
@[reducible] def erSite (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (S : State) : Prop :=
  {site}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem siteKey (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s : State) (hP : Pre R L bud tp tl s) :
    {hyps.rstrip()} erSite R L bud S := by
  obtain {pat} := hP
''' + '\n'.join(body) + '\n  exact key\n\n'
t='\n'.join(L[:ci-2])+'\n'+lemma+'\n'.join(L[ci-2:])
open(path,'w').write(t)
W='sp0'
defs='''/-- The call state at `fmt.errorf`'s entry: `ErrWrap`'s frame (104 below), the three `any` operands in place, the return address at `[RSP]`. -/
def mC : Arm64.Memory :=
  (((((((mem0.writeLE (sp0 - 56) 8 tErr).writeLE (sp0 - 48) 8 evData).writeLE (sp0 - 40) 8 tInt).writeLE (sp0 - 32) 8
    Extracted.dataAddr.«.rodata#4de38626»).writeLE (sp0 - 24) 8 tInt).writeLE (sp0 - 16) 8
    Extracted.dataAddr.«.rodata#b4a1072f»).writeLE (sp0 - 104) 8 (Extracted.entry + 0x88))

def wsC : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 fmtAddr else if i = 3 then 26#64 else if i = 1 then BitVec.ofNat 64 (sp0 - 56)
      else if i = 7 then 3#64 else if i = 6 then 3#64 else if i = 14 then BitVec.ofNat 64 g0 else if i = 4 then BitVec.ofNat 64 (sp0 - 104) else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := mC }

theorem fr_step {m : Arm64.Memory} {a v : Nat} (h : MemFrame mem0 m [(sp0 - 4200, sp0 + 8)]) (h1 : sp0 - 4200 ≤ a) (h2 : a + 8 ≤ sp0 + 8) :
    MemFrame mem0 (m.writeLE a 8 v) [(sp0 - 4200, sp0 + 8)] := h.writeLE v (List.mem_singleton.2 rfl) h1 h2

theorem mC_frame : MemFrame s0.mem wsC.mem [((s0.regs 4).toNat - 4200, (s0.regs 4).toNat + 8)] := by
  show MemFrame mem0 mC [(sp0 - 4200, sp0 + 8)]
  unfold mC sp0
  exact fr_step (fr_step (fr_step (fr_step (fr_step (fr_step (fr_step (MemFrame.refl _ _) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)
'''
rds=[(56,'adrTErr'),(48,'adrEvData'),(40,'adrTInt'),(32,'adrQ1'),(24,'adrTInt'),(16,'adrQ2')]
for k,(o,v) in enumerate(rds):
    defs+=f"""
theorem mC_rd{k} : wsC.mem.readLE ((s0.regs 4).toNat - {o}) 8 = {v} := by
  show mC.readLE (sp0 - {o}) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)
"""
defs+="""
theorem mC_ra : wsC.mem.readLE (wsC.regs 4).toNat 8 = adrRet := by
  show mC.readLE (sp0 - 104) 8 = _
  unfold mC sp0
  simp only [Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem wsC_pre : erSite R0 [] 116 wsC :=
  siteKey R0 [] 116 textAddr 10 s0 pre0 wsC mC_frame rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) mC_ra mC_rd0 mC_rd1 mC_rd2 mC_rd3 mC_rd4 mC_rd5
"""
c='(∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.errorf") ∧\n      erSite R L bud s_c)'
patch(path,defs,[(c,'⟨wsC, rfl, wsC_pre⟩')],runconj="Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R L bud tp tl s s'")

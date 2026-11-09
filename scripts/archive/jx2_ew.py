import sys,re; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs/ErrWrap.lean'
t=open(path).read()
L=t.split('\n')
# locate
ci=next(i for i,l in enumerate(L) if l.startswith('theorem correctness'))
sk=next(i for i,l in enumerate(L) if l.startswith('  have key :'))
pf=next(i for i,l in enumerate(L) if l.startswith('  have post_facts'))
jd=next(i for i,l in enumerate(L) if l.startswith('  janus_data hd [hw4]'))
intro_i=next(i for i in range(ci,jd) if L[i].startswith('  intro ret hret'))
pat=' '.join(L[intro_i:jd-1]).split('hs ',1)[1]   # ⟨...⟩
# key statement
ks=sk; ke=next(i for i in range(sk,pf) if L[i].rstrip().endswith(':= by'))
keystmt='\n'.join(L[ks:ke+1])
concl=keystmt.split('have key :',1)[1].rsplit(':= by',1)[0]
body=L[jd:pf]
# body includes 'have key ... := by' proof; add exact key
cs=concl.index('(CallOK S 4096 5')
hyps=concl[:cs]; site=concl[cs:].strip()
erdef=f'''/-- The precondition of the `fmt.errorf` call at its entry `S`. -/
@[reducible] def erSite (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (S : State) : Prop :=
  {site}

'''
concl=hyps.rstrip()+' erSite R L bud S'
lemma=erdef+f'''set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `fmt.errorf`, for every state `S` that is the call's entry from `s`. -/
theorem siteKey (R : RtInv) (L : List (Nat × Nat)) (bud tp tl : Nat) (s : State) (hP : Pre R L bud tp tl s) :
    {concl.strip()} := by
  obtain {pat} := hP
''' + '\n'.join(body) + '\n  exact key\n\n'
t='\n'.join(L[:ci-2])+'\n'+lemma+'\n'.join(L[ci-2:])
open(path,'w').write(t)
defs='''/-- The call state at `fmt.errorf`'s entry: `ErrWrap`'s frame (112 below), the three `any` operands in place. -/
def mC : Memory :=
  ((((((mem0.writeLE (sp0 - 56) 8 tErr).writeLE (sp0 - 48) 8 evData).writeLE (sp0 - 40) 8 tInt).writeLE (sp0 - 32) 8
    Extracted.dataAddr.«.rodata#4de38626»).writeLE (sp0 - 24) 8 tInt).writeLE (sp0 - 16) 8
    Extracted.dataAddr.«.rodata#df6f96c5»)

def wsC : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 fmtAddr else if i = 1 then 26#64 else if i = 2 then BitVec.ofNat 64 (sp0 - 56)
      else if i = 3 then 3#64 else if i = 4 then 3#64 else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 (Extracted.entry + 0x68) else 0,
    sp := BitVec.ofNat 64 (sp0 - 112), pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩, mem := mC }
'''
open('.sw/ew_defs.txt','w').write(defs)

defs=open('.sw/ew_defs.txt').read()+"""
theorem fr_step {m : Memory} {a v : Nat} (h : MemFrame mem0 m [(sp0 - 4208, sp0)]) (h1 : sp0 - 4208 ≤ a) (h2 : a + 8 ≤ sp0) :
    MemFrame mem0 (m.writeLE a 8 v) [(sp0 - 4208, sp0)] := h.writeLE v (List.mem_singleton.2 rfl) h1 h2

theorem mC_frame : MemFrame s0.mem wsC.mem [(s0.sp.toNat - 4208, s0.sp.toNat)] := by
  show MemFrame mem0 mC [(sp0 - 4208, sp0)]
  unfold mC sp0
  exact fr_step (fr_step (fr_step (fr_step (fr_step (fr_step (MemFrame.refl _ _) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)) (by unfold sp0; omega) (by unfold sp0; omega)

theorem wsC_pre : erSite R0 [] 116 wsC :=
  siteKey R0 [] 116 textAddr 10 s0 pre0 wsC mC_frame rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) mC_rd0 mC_rd1 mC_rd2 mC_rd3 mC_rd4 mC_rd5
"""
rd=''
for k,(o,v) in enumerate([(56,'adrTErr'),(48,'adrEvData'),(40,'adrTInt'),(32,'adrQ1'),(24,'adrTInt'),(16,'adrQ2')]):
    rd+=f"""
theorem mC_rd{k} : wsC.mem.readLE (s0.sp.toNat - {o}) 8 = {v} := by
  show mC.readLE (sp0 - {o}) 8 = _
  unfold mC sp0
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt (by decide +kernel)
"""
defs=defs.replace("\ntheorem wsC_pre",rd+"\ntheorem wsC_pre")
c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.errorf") ∧\n      erSite R L bud s_c)'
patch(path,defs,[(c,'⟨wsC, rfl, wsC_pre⟩')],runconj="Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R L bud tp tl s s'")

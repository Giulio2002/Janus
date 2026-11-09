import sys,re; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs/ScratchSum.lean'
t=open(path).read()
L=t.split('\n')
def idx(pfx,start=0): return next(i for i in range(start,len(L)) if L[i].startswith(pfx))
ci=idx('theorem correctness')
# pre conjuncts (without B = BufObj)
i0=idx('    Ensures',ci)
k1=idx('  have key1 :',ci); k1e=next(i for i in range(k1,len(L)) if L[i].rstrip().endswith(':= by') and 'intro' in L[i+1])
j1=next(i for i in range(k1e,len(L)) if L[i].startswith('  janus_run until'))
key1body=L[k1e+2:j1]   # after 'intro S ...'
k2=idx('    have key2 :',ci); k2e=next(i for i in range(k2,len(L)) if L[i].rstrip().endswith(':= by') and 'intro' in L[i+1])
k2end=next(i for i in range(k2e,len(L)) if L[i].startswith('    refine Reaches.call (Summary.withExit (hnew.pos'))
key2body=L[k2e+2:k2end]
dd=idx('  have hdesc',ci); 
hdesc=L[dd:idx('  have hsp48',ci)]
hoBblk_s=idx('    have hoB',ci); hoBblk=L[hoBblk_s:idx('    janus_run until [Extracted.program.contractAddr "runtime.newobject"]',ci)]
open('.sw/ss_dbg.txt','w').write('\n'.join(key1body)+'\n=====\n'+'\n'.join(key2body)+'\n=====\n'+'\n'.join(hdesc)+'\n====\n'+'\n'.join(hoBblk))
def ded(ls,n): return [l[n:] if l.startswith(' '*n) else l for l in ls]
key1b='\n'.join(ded(key1body,2))
key2b='\n'.join(ded(key2body,4))
key2b=key2b.replace("  rw [hround]\n","  unfold newSite\n  rw [hround]\n")
key1b=key1b.replace("rw [hf.readLE","rw [h0, hf.readLE")
hd='\n'.join(ded(hdesc,0)); hob='\n'.join(ded(hoBblk,2)).replace("m1.readLE","m1.readLE")
prestmt=L[i0+1:i0+1]
# pre conjunct text from correctness statement
ps=idx('      (fun s => B = BufObj',ci)
pe=next(i for i in range(ps,len(L)) if L[i].rstrip().endswith('32 ≤ bud)'))
pretxt='\n'.join(L[ps:pe+1]).replace('(fun s => B = BufObj ∧ ','').rstrip()
assert pretxt.endswith('32 ≤ bud)'); pretxt=pretxt[:-1]
blk=f'''/-- The pre of `correctness` without the shape equation. -/
@[reducible] def PreS (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) : Prop :=
  {pretxt.strip()}

/-- The precondition of `sync.(*Pool).Get` at its call state `S`. -/
@[reducible] def getSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  CallOK S 4096 1 ∧ StackRoom S 4096 1 ∧ S.mem.readLE ((S.regs 0).toNat + newOffset) 8 = 0 ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L b 0 (S.regs 28).toNat S.mem
      (calleeStack S 4096 1)

/-- The precondition of `runtime.newobject` at its call state `S`. -/
@[reducible] def newSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L b (newobjectRound S)
      (S.regs 28).toNat S.mem (calleeStack S 4096 1)

/-- The precondition of `sync.(*Pool).Put` at its call state `S`. -/
@[reducible] def putSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (S : State) : Prop :=
  CallOK S 4096 3 ∧ StackRoom S 4096 3 ∧ (S.regs 1).toNat = ptrType ∧ BufObj S.mem (S.regs 2).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Put") [(S.regs 0).toNat] L b 0 (S.regs 28).toNat S.mem
      (calleeStack S 4096 3)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `Get`, for every state `S` that is the call's entry from `s`. -/
theorem siteGet (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) (hPre : PreS R L bud s) :
    ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4144, s.sp.toNat + 24)] →
      S.regs 28 = s.regs 28 → S.sp.toNat + 48 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 →
      (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = (poolN) → getSite R L bud S := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩ := hPre
  janus_eval_nat hP : poolAddr
  rw [hP] at hpin hokG hokP hnew0
  intro S hf hg hsp h30a h30b h0
{key1b}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `newobject`, for every state `S` that is the call's entry from `s`
(memory `m1`, reached from `s` inside the runtime and the window). -/
theorem siteNew (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) (hPre : PreS R L bud s)
    (m1 : Memory) (hF1 : MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))
    (hinvG : R.inv bud L (s.regs 28).toNat (view R.rt L m1)) :
    ∀ S : State, S.mem = m1 → S.regs 28 = s.regs 28 → S.sp.toNat + 48 = s.sp.toNat →
        (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = (bufN) →
        newSite R L bud S ∧ 0 < typSize S.mem (S.regs 0).toNat := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩ := hPre
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  janus_eval_nat hB : bufType
  rw [hP] at hpin hokG hokP hnew0
  rw [hB] at hbin
  janus_data hd [hw4]
{hd}
{hob}
  intro S hm hg hsp h30a h30b h0
{key2b}
'''
open('.sw/ss_blk.txt','w').write(blk)

# insert blk before correctness (before its set_option lines)
si=ci
while L[si-1].startswith('set_option'): si-=1
t='\n'.join(L[:si])+'\n'+blk+'\n'+'\n'.join(L[si:])
open(path,'w').write(t)
defs='''theorem P_bv : (BitVec.ofNat 64 P).toNat = poolN := by unfold P; decide
theorem P_bv' : (BitVec.ofNat 64 P).toNat = poolAddr := by rw [hP]; unfold P; decide
theorem bT_bv : (BitVec.ofNat 64 bT).toNat = bufN := by unfold bT; decide
theorem pT_bv : (BitVec.ofNat 64 pT).toNat = ptrType := by rw [hPT]; unfold pT; decide

/-- The call state at `sync.(*Pool).Get`'s entry: `ScratchSum`'s frame (48 below), the pool in `X0`. -/
def wsG : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get"),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem wsG_pre : getSite R [] 0x400 wsG :=
  siteGet R [] 0x400 s0 pre wsG (MemFrame.refl _ _) (by simp [wsG, s0]) (by simp [wsG, s0, sp0])
    (by simp [wsG, ret]) (by simp [wsG, ret]) (by simp [wsG]; exact P_bv)

/-- The call state at `runtime.newobject`'s entry (`scratch`'s descriptor in `X0`). -/
def wsN : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 bT else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"),
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem wsN_pre : newSite R [] 0x400 wsN :=
  (siteNew R [] 0x400 s0 pre mem0 (MemFrame.refl _ _) inv0 wsN rfl (by simp [wsN, s0]) (by simp [wsN, s0, sp0])
    (by simp [wsN, ret]) (by simp [wsN, ret]) (by simp [wsN]; exact bT_bv)).1

/-! ### The `Put` call state: the buffer `[HEAP, HEAP+32)` is live, the bump pointer at `HEAP+32` -/

def memP : Memory := mem0.writeLE BUMP 8 (HEAP + 32)

theorem invP : R.inv 0x400 [(HEAP, HEAP + 32)] (s0.regs 28).toNat (view R.rt [(HEAP, HEAP + 32)] memP) := by
  show toyInv tys 0x400 [(HEAP, HEAP + 32)] (s0.regs 28).toNat (view (toyRt tys) [(HEAP, HEAP + 32)] memP)
  have hb : Outside BUMP 8 [(HEAP, HEAP + 32)] := by
    simp only [outside_cons, outside_nil, and_true, BUMP, HEAP]; decide
  refine ⟨HEAP + 32, ?_, by simp [HEAP], by simp [HEAP], by simp [HEAP, HEND, HSIZE], ?_, fun i hi hi' => ?_, ?_, ?_, ?_,
    fun t ht => absurd ht (by simp [tys])⟩
  · rw [readLE_view (inRanges_bump tys) hb, memP, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simp [HEAP])
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [HEAP]
  · have ho : Outside i 1 [(HEAP, HEAP + 32)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    rw [readLE_view (inRanges_heap (n := 1) (by simp only [HEAP] at *; omega) (by omega)) ho, memP,
      Memory.readLE_writeLE_of_disjoint mem0 (a := BUMP) (n := 8) (b := i) (k := 1) (HEAP + 32) (by simp only [BUMP, HEAP] at *; omega), Memory.readLE_one]
    show (bytes0 i).toNat = 0
    simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]; rfl
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Memory.accessible_writeLE]; decide

/-- The call state at `sync.(*Pool).Put`'s entry: the pooled buffer `HEAP` (the allocator's only
object) in `X2`. -/
def wsP : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 1 then BitVec.ofNat 64 pT
      else if i = 2 then BitVec.ofNat 64 HEAP else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put"),
    flags := ⟨false, false, false, false⟩, mem := memP }

theorem wsP_pre : putSite R [(HEAP, HEAP + 32)] 0x400 [(HEAP, HEAP + 32)] wsP := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩ := pre
  have h := putPre R [] 0x400 HEAP (Extracted.program.contractAddr "sync.(*Pool).Put") s0 wsP hg1 hg2 hg3 ha4 hw4
    hal hb4 hgo hwrt hokP
    (by
      show MemFrame mem0 memP _
      exact (MemFrame.refl _ _).writeLE_inRanges _ ((inRanges_bump tys).append_left _))
    (by simp [wsP, s0]) (by simp [wsP, s0, sp0]) (by simp [wsP, ret]) (by simp [wsP, ret])
    (by simp [wsP]; exact P_bv') (by simp [wsP]; exact pT_bv) (by simp [wsP, HEAP])
    ⟨by simp [HEAP], by simp [HEAP], by simp [HEAP], by simp only [wsP, memP, Memory.accessible_writeLE]; decide, rfl⟩
    (by
      rw [s0_sp]
      simp only [List.nil_append, liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, HEAP, sp0]; decide)
    (by exact invP)
  exact h
'''
c1='(∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧\n      getSite R L b s_c)'
c2='(∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧\n      newSite R L b s_c)'
c3='(∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧\n      putSite R L b rs s_c)'
run="Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (3#64 ^^^ 5#64).toNat ∧\n      ∃ d b', (b' = bud ∨ b' = bud - 32) ∧\n        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (d, d + 32)]) ∧\n        LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 28).toNat (view R.rt L s'.mem)"
tt=open(path).read()
old=''':= by
  refine ⟨implAt, R, ret, s0, [], 0x400, ?_, ?_, ?_, hret, setup, ⟨rfl, pre⟩⟩
  · rw [aG, hPT]; exact hget
  · rw [aP, hPT]; exact hput
  · rw [aN]; exact hnew'''
assert old in tt
tt=tt.replace(old,''':=
  ⟨implAt, R, ret, s0, [], 0x400, (by rw [aG, hPT]; exact hget), (by rw [aP, hPT]; exact hput),
    (by rw [aN]; exact hnew), hret, setup, ⟨rfl, pre⟩⟩''')
open(path,'w').write(tt)
patch(path,defs,[(c1,'⟨[], 0x400, wsG, rfl, wsG_pre⟩'),(c2,'⟨[], 0x400, wsN, rfl, wsN_pre⟩'),(c3,'⟨[(HEAP, HEAP + 32)], 0x400, [(HEAP, HEAP + 32)], wsP, rfl, wsP_pre⟩')],runconj=run)

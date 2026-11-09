import sys,re; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs-amd64/ScratchSum/Proof.lean'
t=open(path).read()
L=t.split('\n')
def idx(pfx,start=0,end=None): return next(i for i in range(start,end or len(L)) if L[i].startswith(pfx))
ci=idx('theorem correctness')
def ded(ls,n): return [l[n:] if l.startswith(' '*n) else l for l in ls]
# prelude
pi=idx('  janus_eval_nat hP : poolAddr',ci); pe=idx("  have hgo' := hgo",ci)
prel=L[pi:pe]
# split prelude: drop hdesc/hbW for Get
dsi=next(i for i,l in enumerate(prel) if l.startswith('  have hdesc'))
prel_get='\n'.join(prel[:dsi]); prel_new='\n'.join(prel)
k1=idx('  have key1 :',ci); k1e=next(i for i in range(k1,len(L)) if L[i].rstrip().endswith(':= by') and 'intro' in L[i+1])
j1=idx('  janus64_run until',k1e)
key1body=ded(L[k1e+2:j1],2)
key1b='\n'.join(key1body).replace("rw [hf.readLE","rw [h0, hf.readLE")
h1=idx('    have hbw',ci); h1e=idx('    janus64_run until [Extracted.program.contractAddr "runtime.newobject"]',h1)
mid='\n'.join(ded(L[h1:h1e],2))
k2=idx('    have key2 :',ci); k2e=next(i for i in range(k2,len(L)) if L[i].rstrip().endswith(':= by') and 'intro' in L[i+1])
k2end=idx('    refine Reaches.call (Summary.withExit (hnew.pos',k2e)
key2b='\n'.join(ded(L[k2e+2:k2end],4)).replace("  rw [hround]\n","  unfold newSite\n  rw [hround]\n")
ps=idx('      (fun s => B = BufObj',ci); pe2=next(i for i in range(ps,len(L)) if L[i].rstrip().endswith('32 ≤ bud)'))
pretxt='\n'.join(L[ps:pe2+1]).replace('(fun s => B = BufObj ∧ ','').rstrip()[:-1].strip()
pat="⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,\n    hnew0, hinv, hbud⟩"
blk=f'''/-- The pre of `correctness` without the shape equation. -/
@[reducible] def PreS (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) : Prop :=
  {pretxt}

/-- The precondition of `sync.(*Pool).Get` at its call state `S`. -/
@[reducible] def getSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  CallOK64 S 4096 1 ∧ StackRoom64 S 4096 1 ∧ S.mem.readLE ((S.regs 0).toNat + newOffset) 8 = 0 ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L b 0 (S.regs 14).toNat S.mem
      (liveWin64 S 4096 1)

/-- The precondition of `runtime.newobject` at its call state `S`. -/
@[reducible] def newSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  NewobjectPre64 4096 S ∧ StackRoom64 S 4096 1 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L b (newobjectRound64 S)
      (S.regs 14).toNat S.mem (liveWin64 S 4096 1)

/-- The precondition of `sync.(*Pool).Put` at its call state `S`. -/
@[reducible] def putSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (S : State) : Prop :=
  CallOK64 S 4096 3 ∧ StackRoom64 S 4096 3 ∧ (S.regs 3).toNat = ptrType ∧ BufObj S.mem (S.regs 1).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Put") [(S.regs 0).toNat] L b 0 (S.regs 14).toNat S.mem
      (liveWin64 S 4096 3)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `Get`, for every state `S` that is the call's entry from `s`. -/
theorem siteGet (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) (hPre : PreS R L bud s) :
    ∀ S : State, MemFrame s.mem S.mem [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] →
      S.regs 14 = s.regs 14 → (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = (poolN) →
      S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 → getSite R L bud S := by
  obtain {pat} := hPre
{prel_get}
  intro S hf hg' hsp h0 hra
{key1b}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The call-site precondition of `newobject`, for every state `S` that is the call's entry from `s`
(memory `m1`, reached from `s` inside the runtime and the window, plus the return address). -/
theorem siteNew (R : RtInv) (L : List (Nat × Nat)) (bud : Nat) (s : State) (hPre : PreS R L bud s)
    (m1 : Arm64.Memory) (hF1 : MemFrame s.mem m1 (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))
    (hinvG : R.inv bud L (s.regs 14).toNat (view R.rt L m1)) :
    ∀ S : State, S.mem = m1.writeLE ((s.regs 4).toNat - 40) 8 (janus_eval% (Extracted.entry + 71)) →
        S.regs 14 = s.regs 14 → (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = (bufN) →
        newSite R L bud S ∧ 0 < typSize S.mem (S.regs 0).toNat := by
  obtain {pat} := hPre
{prel_new}
{mid}
  intro S hm hg' hsp h0
{key2b}
'''
open('.sw/ss64_blk.txt','w').write(blk)
si=ci
while L[si-1].startswith('set_option'): si-=1
t='\n'.join(L[:si])+'\n'+blk+'\n'+'\n'.join(L[si:])
open(path,'w').write(t)

defs='''theorem P_bv : (BitVec.ofNat 64 P).toNat = poolN := by unfold P; decide
theorem P_bv' : (BitVec.ofNat 64 P).toNat = poolAddr := by rw [hP]; unfold P; decide
theorem bT_bv : (BitVec.ofNat 64 bT).toNat = bufN := by unfold bT; decide
theorem pT_bv : (BitVec.ofNat 64 pT).toNat = ptrType := by rw [hPT]; unfold pT; decide

theorem stk_frame (v : Nat) : MemFrame s0.mem (mem0.writeLE ((s0.regs 4).toNat - 40) 8 v)
    [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24)] := by
  rw [s0_sp]
  exact (MemFrame.refl _ _).writeLE v (List.mem_singleton_self _) (by simp only [sp0]; omega) (by simp only [sp0]; omega)

theorem stk_ra (m : Arm64.Memory) (v : Nat) (hv : v < 2 ^ 47) (S : State) (h4 : S.regs 4 = s0.regs 4 - 40#64)
    (hm : S.mem = m.writeLE ((s0.regs 4).toNat - 40) 8 v) : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 := by
  have : (S.regs 4).toNat = (s0.regs 4).toNat - 40 := by
    rw [h4, BitVec.toNat_sub]; simp [s0, sp0]
  rw [hm, this, Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  exact hv

/-- The call state at `sync.(*Pool).Get`'s entry: `ScratchSum`'s frame (40 below, return address written),
the pool in `RAX`. -/
def wsG : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 4 then s0.regs 4 - 40#64
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get"),
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0.writeLE ((s0.regs 4).toNat - 40) 8 ret }

theorem wsG_pre : getSite R [] 0x400 wsG :=
  siteGet R [] 0x400 s0 pre wsG (stk_frame _) (by simp [wsG, s0]) (by simp [wsG, s0, sp0])
    (by simp [wsG]; exact P_bv) (stk_ra _ _ (by simp [ret]) wsG rfl rfl)

/-- The call state at `runtime.newobject`'s entry (`scratch`'s descriptor in `RAX`). -/
def wsN : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 bT else if i = 4 then s0.regs 4 - 40#64
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"),
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0.writeLE ((s0.regs 4).toNat - 40) 8 (janus_eval% (Extracted.entry + 71)) }

theorem wsN_pre : newSite R [] 0x400 wsN :=
  (siteNew R [] 0x400 s0 pre mem0 (MemFrame.refl _ _) inv0 wsN rfl (by simp [wsN, s0]) (by simp [wsN, s0, sp0])
    (by simp [wsN]; exact bT_bv)).1

/-! ### The `Put` call state: the buffer `[HEAP, HEAP+32)` is live, the bump pointer at `HEAP+32` -/

def memP : Arm64.Memory := mem0.writeLE BUMP 8 (HEAP + 32)

theorem invP : R.inv 0x400 [(HEAP, HEAP + 32)] (s0.regs 14).toNat (view R.rt [(HEAP, HEAP + 32)] memP) := by
  show toyInv tys 0x400 [(HEAP, HEAP + 32)] (s0.regs 14).toNat (view (toyRt tys) [(HEAP, HEAP + 32)] memP)
  have hb : Outside BUMP 8 [(HEAP, HEAP + 32)] := by
    simp only [outside_cons, outside_nil, and_true, BUMP, HEAP]; decide
  refine ⟨HEAP + 32, ?_, by simp [HEAP], by simp [HEAP], by simp [HEAP, HEND, HSIZE], ?_, fun i hi hi' => ?_, ?_, ?_, ?_,
    fun t ht => absurd ht (by simp [tys])⟩
  · rw [readLE_view (inRanges_bump tys) hb, memP, Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simp [HEAP])
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [HEAP]
  · have ho : Outside i 1 [(HEAP, HEAP + 32)] := by
      simp only [outside_cons, outside_nil, and_true]; omega
    rw [readLE_view (inRanges_heap (n := 1) (by simp only [HEAP] at *; omega) (by omega)) ho, memP,
      Arm64.Memory.readLE_writeLE_of_disjoint mem0 (a := BUMP) (n := 8) (b := i) (k := 1) (HEAP + 32)
        (by simp only [BUMP, HEAP] at *; omega), Arm64.Memory.readLE_one]
    show (bytes0 i).toNat = 0
    simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
    rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]; rfl
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide
  · rw [view_accessible, memP, Arm64.Memory.accessible_writeLE]; decide

/-- The call state at `sync.(*Pool).Put`'s entry: the pooled buffer `HEAP` (the allocator's only
object) in `RCX`. -/
def wsP : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 3 then BitVec.ofNat 64 pT
      else if i = 1 then BitVec.ofNat 64 HEAP else if i = 4 then s0.regs 4 - 40#64
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put"),
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := memP.writeLE ((s0.regs 4).toNat - 40) 8 ret }

theorem wsP_pre : putSite R [(HEAP, HEAP + 32)] 0x400 [(HEAP, HEAP + 32)] wsP := by
  obtain ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩ := pre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb4 ha4 hw4 hal
  have hfr : MemFrame s0.mem wsP.mem (R.rt ++ [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24)]) := by
    show MemFrame mem0 (memP.writeLE _ 8 ret) _
    refine (((MemFrame.refl _ _).writeLE_inRanges _ ((inRanges_bump tys).append_left _))).writeLE_inRanges _ ?_
    exact ⟨((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24), List.mem_append_right _ (List.mem_singleton_self _),
      by rw [s0_sp]; simp only [sp0]; omega, by rw [s0_sp]; simp only [sp0]; omega⟩
  have hra := stk_ra memP ret (by simp [ret]) wsP rfl rfl
  exact putPre64 R [] 0x400 HEAP (Extracted.program.contractAddr "sync.(*Pool).Put") s0 wsP hnw2 hgr (by omega) ha4 hw4
    hal hb4 hgo hwrt hokP hfr (by simp [wsP, s0]) (by simp [wsP, s0, sp0]) hra
    (by simp [wsP]; exact P_bv') (by simp [wsP]; exact pT_bv) (by simp [wsP, HEAP])
    ⟨by simp [HEAP], by simp [HEAP], by simp [HEAP], by simp only [wsP, memP, Arm64.Memory.accessible_writeLE]; decide, rfl⟩
    (by
      rw [s0_sp]
      simp only [List.nil_append, liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, HEAP, sp0]; decide)
    (by
      have hf : MemFrame memP (memP.writeLE ((s0.regs 4).toNat - 40) 8 ret)
          [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24)] :=
        (MemFrame.refl memP _).writeLE ret (List.mem_singleton_self _) (by rw [s0_sp]; simp only [sp0]; omega)
          (by rw [s0_sp]; simp only [sp0]; omega)
      exact RtInv.inv_frame hf hwrt invP)
'''
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
A='Janus.Amd64.State'
c1=f'(∃ (L : List (Nat × Nat)) (b : Nat) (s_c : {A}), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧\n      getSite R L b s_c)'
c2=f'(∃ (L : List (Nat × Nat)) (b : Nat) (s_c : {A}), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧\n      newSite R L b s_c)'
c3=f'(∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : {A}), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧\n      putSite R L b rs s_c)'
run="Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (3#64 ^^^ 5#64).toNat ∧\n      ∃ d b', (b' = bud ∨ b' = bud - 32) ∧\n        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), (d, d + 32)]) ∧\n        LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 14).toNat (view R.rt L s'.mem)"
patch(path,defs,[(c1,'⟨[], 0x400, wsG, rfl, wsG_pre⟩'),(c2,'⟨[], 0x400, wsN, rfl, wsN_pre⟩'),(c3,'⟨[(HEAP, HEAP + 32)], 0x400, [(HEAP, HEAP + 32)], wsP, rfl, wsP_pre⟩')],runconj=run)

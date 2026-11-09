import sys; sys.path.insert(0,'scripts')
path='examples/proofs-amd64/StackGrow/Proof.lean'
t=open(path).read()
wrap='''/-! ## Call-site preconditions (for the witness) -/

/-- The precondition of `sync.(*Pool).Get` at its call state `S`. -/
@[reducible] def getSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  CallOK64 S 4096 1 ∧ StackRoom64 S 4096 1 ∧ S.mem.readLE ((S.regs 0).toNat + newOffset) 8 = 0 ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L b 0 (S.regs 14).toNat S.mem
      (liveWin64 S 4096 1)

/-- The precondition of `sync.(*Pool).Put` at its call state `S`. -/
@[reducible] def putSite (R : RtInv) (B : Nat) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (S : State) :
    Prop :=
  CallOK64 S 4096 3 ∧ StackRoom64 S 4096 3 ∧ (S.regs 3).toNat = ptrType ∧ SliceObj B S.mem (S.regs 1).toNat rs ∧
    (∀ r ∈ rs, r ∈ L) ∧
    LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Put") [(S.regs 0).toNat] L b 0 (S.regs 14).toNat S.mem
      (liveWin64 S 4096 3)

/-- The precondition of `runtime.newobject` at its call state `S`. -/
@[reducible] def newSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  NewobjectPre64 4096 S ∧ StackRoom64 S 4096 1 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L b (newobjectRound64 S)
      (S.regs 14).toNat S.mem (liveWin64 S 4096 1)

/-- The precondition of `runtime.growslice` at its call state `S`. -/
@[reducible] def grSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  GrowslicePre64 4096 S ∧ StackRoom64 S 4096 5 ∧
    LiveAt R (Extracted.program.contractAddr "runtime.growslice") (growsliceArgs64 S) L b (growsliceRound64 S)
      (S.regs 14).toNat S.mem (liveWin64 S 4096 5)

/-- The precondition of `runtime.memclrNoHeapPointers` at its call state `S`. -/
@[reducible] def memSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  MemPre64 4096 2 S ∧
    LiveMemAt64 R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
      [(S.regs 0).toNat, (S.regs 3).toNat] L b S (liveWin64 S 4096 2) ∧
    LiveDest64 R L S 4096 2 (S.regs 0).toNat (S.regs 3).toNat

/-- The precondition of `runtime.gcWriteBarrier2` at its call state `S`. -/
@[reducible] def wbSite (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S : State) : Prop :=
  CallOK64 S 4096 0 ∧ R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b L (S.regs 14).toNat (view R.rt L S.mem) ∧
    LiveSep L [((S.regs 4).toNat - 4096, (S.regs 4).toNat + 8)] ∧
    LiveSep [((S.regs 4).toNat - 4096, (S.regs 4).toNat + 8)] R.rt

'''
mk='/-! ## Non-vacuity: every hypothesis of `correctness` holds together'
assert t.count(mk)==1, t.count(mk)
t=t.replace(mk,wrap+mk)
defs=open('scripts/archive/jx2_sg64_defs.lean').read()
nvk='/-- All hypotheses of `correctness` hold together. -/\ntheorem nonvacuous'
assert t.count(nvk)==1
t=t.replace(nvk,defs+'\n'+nvk)
S='Janus.Amd64.State'
A='(∃ (L : List (Nat × Nat)) (b : Nat) (s_c : '+S+'), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "%s") ∧\n      %s R L b s_c)'
cs=[A%("sync.(*Pool).Get","getSite"),A%("runtime.newobject","newSite"),A%("runtime.growslice","grSite"),A%("runtime.memclrNoHeapPointers","memSite"),A%("runtime.gcWriteBarrier2","wbSite"),
 '(∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : '+S+'), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧\n      putSite R B L b rs s_c)',
 "Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R B n L bud s s'"]
old="growCap8 n.toNat c ≤ B))) := by\n  obtain"
assert t.count(old)==1
t=t.replace(old,"growCap8 n.toNat c ≤ B))) ∧\n    "+" ∧\n    ".join(cs)+" := by\n  obtain")
old2="⟨a17, a18, a19, a20, a21, a22, a23, a24⟩⟩⟩\n"
assert t.count(old2)==1
t=t.replace(old2,"⟨a17, a18, a19, a20, a21, a22, a23, a24⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩\n")
old3="  · rw [aW]; exact hwb\n"
assert t.count(old3)==1
t=t.replace(old3,old3+"""  · exact ⟨[], 0x400, wsG, rfl, wsG_pre⟩
  · exact ⟨[], 0x400, wsN, rfl, wsN_pre⟩
  · exact ⟨[], 0x400, wsR, rfl, wsR_pre⟩
  · exact ⟨[], 0x400, wsM, rfl, wsM_pre⟩
  · exact ⟨[], 0x400, wsW, rfl, wsW_pre⟩
  · exact ⟨[(HEAP, HEAP + 24)], 0x400, [(HEAP, HEAP + 24)], wsU, rfl, wsU_pre⟩
  · exact returnsPost
""")
open(path,'w').write(t)

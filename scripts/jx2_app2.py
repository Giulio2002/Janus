import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
arm='''/-- The call state at `runtime.growslice`'s entry (`growslice(nil, 1, 0, 1, pt)`, callee `SP` 112 below). -/
def wsCall : State :=
  { regs := (wstate (args [0, 1, 0, 1, PT])).regs, sp := BitVec.ofNat 64 (wsp - 112),
    pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩, mem := wmemD }

@[reducible] def rpSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : State) : Prop :=
  RtPre rt 4096 H growsliceSpec s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : rpSite rtA HA wsCall := by
  have ha : argWords wsCall growsliceSpec.nargs = [0, 1, 0, 1, PT] := by decide
  have hw : wmemD.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide,
    Memory.accessible_mono _ hw (by decide) (by decide)⟩, ?_, ?_, trivial, ?_⟩
  · rw [ha]
    show ElemOK wsCall.mem PT ∧ 1 ≤ 1 ∧ 1 - 1 ≤ 0 ∧ 0 < 1 ∧ 1 * typSize wsCall.mem PT < 2 ^ 46 ∧
      Readable wsCall.mem 0 ((1 - 1) * typSize wsCall.mem PT)
    rw [← ptType_eq]
    refine ⟨⟨⟨by decide, by decide⟩, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_⟩
    simp [Readable]
  · rw [ha]; intro r hr
    simp only [growsliceSpec, arg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show Outside PT 16 _
      rw [← ptType_eq]; simp only [calleeStack, outside_cons, outside_nil, wsCall]; decide
    · show Outside 0 ((1 - 1) * typSize wsCall.mem PT) _
      simp only [Nat.sub_self, Nat.zero_mul, calleeStack64, outside_cons, outside_nil, wsCall]; decide
  · exact ready_intro rfl ⟨ha, by decide, by decide, by decide⟩
'''
open('/tmp/dummy','w').write(arm)

if sys.argv[1:]==['arm']:
    patch('examples/proofs/AppendPoint.lean',arm,[('(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧\n      rpSite rt H s_c)','⟨wsCall, rfl, wsCall_pre⟩')],runconj=runconj_auto('examples/proofs/AppendPoint.lean',{k:'(0 : BitVec 64)' for k in 'ptr len cap x y z'.split()}),retproof='correctness implAt rtA HA 0 0 0 0 0 0 model ret hret s0 setup pre')
    

amd='''/-- The call state at `runtime.growslice`'s entry (`growslice(nil, 1, 0, 1, pt)`, callee `RSP` 104 below). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 3 then 1 else if i = 7 then 1 else if i = 6 then BitVec.ofNat 64 PT
      else if i = 4 then BitVec.ofNat 64 (wsp - 104) else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

@[reducible] def rpSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  RtPre64 rt 4096 H growsliceSpec s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : rpSite rtA HA wsCall := by
  have ha : argWords64 wsCall growsliceSpec.nargs = [0, 1, 0, 1, PT] := by decide
  have hw : mem0.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  refine ⟨⟨by decide, by decide, by decide, by decide,
    Arm64.Memory.accessible_mono _ hw (by decide) (by decide)⟩, ?_, ?_, trivial, ?_⟩
  · rw [ha]
    show ElemOK wsCall.mem PT ∧ 1 ≤ 1 ∧ 1 - 1 ≤ 0 ∧ 0 < 1 ∧ 1 * typSize wsCall.mem PT < 2 ^ 46 ∧
      Readable wsCall.mem 0 ((1 - 1) * typSize wsCall.mem PT)
    refine ⟨⟨⟨by decide, by decide⟩, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_⟩
    simp [Readable]
  · rw [ha]; intro r hr
    simp only [growsliceSpec, arg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show Outside PT 16 _
      simp only [calleeStack64, outside_cons, outside_nil, wsCall]; decide
    · show Outside 0 ((1 - 1) * typSize wsCall.mem PT) _
      simp only [Nat.sub_self, Nat.zero_mul, calleeStack64, outside_cons, outside_nil, wsCall]; decide
  · exact ready_intro rfl ⟨ha, by decide, by decide, by decide⟩
'''
if sys.argv[1:]==['amd']:
  patch('examples/proofs-amd64/AppendPoint/Proof.lean',amd,[('(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧\n      rpSite rt H s_c)','⟨wsCall, rfl, wsCall_pre⟩')],runconj=runconj_auto('examples/proofs-amd64/AppendPoint/Proof.lean',{k:'(0 : BitVec 64)' for k in 'ptr len cap x y z'.split()}),retproof='correctness implAt rtA HA 0 0 0 0 0 0 model ret hret s0 setup pre')

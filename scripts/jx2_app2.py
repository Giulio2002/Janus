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
      simp [outside_zero]
  · exact ready_intro rfl ⟨ha, by decide, by decide, by decide⟩
'''
open('/tmp/dummy','w').write(arm)

patch('examples/proofs/AppendPoint.lean',arm,[('(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧\n      rpSite rt H s_c)','⟨wsCall, rfl, wsCall_pre⟩')],runconj=runconj_auto('examples/proofs/AppendPoint.lean',{k:'(0 : BitVec 64)' for k in 'ptr len cap x y z'.split()}),retproof='correctness implAt rtA HA 0 0 0 0 0 0 model ret hret s0 setup pre')

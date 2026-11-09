import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
arm='''def cAddr : Nat := Extracted.program.contractAddr "runtime.growslice"
def tyA : Nat := janus_eval% u64Type

/-- The call state at `runtime.growslice`'s entry (`growslice(nil, 1, 0, 1, uint64)`, callee `SP` 96 below). -/
def wsCall : State :=
  { regs := fun i => if i = 1 then 1 else if i = 3 then 1 else if i = 4 then BitVec.ofNat 64 tyA
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 96), pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := s0.mem }

@[reducible] def grSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : State) : Prop :=
  GrowslicePre 4096 s_c ∧ Ready H rt (growsliceArgs s_c) s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : grSite rt H wsCall := by
  have h := hH
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => ⟨by decide, by decide⟩⟩, ?_⟩
  exact h
'''
patch('examples/proofs/AppendOne.lean',arm,[('(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧\n      grSite rt H s_c)','⟨wsCall, rfl, wsCall_pre⟩')])
amd='''def cAddr : Nat := Extracted.program.contractAddr "runtime.growslice"
def tyA : Nat := janus_eval% u64Type

/-- The call state at `runtime.growslice`'s entry (`growslice(nil, 1, 0, 1, uint64)`, callee `RSP` 80 below). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 3 then 1 else if i = 7 then 1 else if i = 6 then BitVec.ofNat 64 tyA
      else if i = 4 then BitVec.ofNat 64 (sp0 - 80) else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }

@[reducible] def grSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : Janus.Amd64.State) : Prop :=
  GrowslicePre64 4096 s_c ∧ Contracts.Ready64 H rt (growsliceArgs64 s_c) s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : grSite rt H wsCall := by
  have h := hH
  have hpt : u64Type = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => ⟨by decide, by decide⟩⟩, ?_⟩
  exact h
'''
patch('examples/proofs-amd64/AppendOne/Proof.lean',amd,[('(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧\n      grSite rt H s_c)','⟨wsCall, rfl, wsCall_pre⟩')])

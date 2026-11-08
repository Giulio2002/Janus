import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
isa=sys.argv[1]; arm=isa=='arm64'
if arm:
    path='examples/proofs/MinStr.lean'
    defs='''def cAddr : Nat := Extracted.program.contractAddr "runtime.cmpstring"

/-- The call state at `runtime.cmpstring`'s entry (`cmpstring("", "")`). -/
def wsCall : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := s0.mem }

theorem wsCall_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 wsCall :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, Or.inl rfl, Or.inl rfl⟩
'''
    c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧\n      Janus.Contracts.Cmpstring.CmpstringPre 16 s_c)'
else:
    path='examples/proofs-amd64/MinStr/Proof.lean'
    defs='''def cAddr : Nat := Extracted.program.contractAddr "runtime.cmpstring"

/-- The call state at `runtime.cmpstring`'s entry (`cmpstring("", "")`). -/
def wsCall : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 (sp0 - 8) else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := s0.mem }

theorem wsCall_pre : Janus.Contracts.Cmpstring.CmpstringPre64 16 wsCall :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, Or.inl rfl, Or.inl rfl⟩
'''
    c='(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧\n      Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c)'
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')])

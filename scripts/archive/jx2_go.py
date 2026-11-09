import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs/DeferOrder.lean'
defs='''/-- The call state at `runtime.gopanic`'s entry: `DeferOrder`'s frame (SP 128 below the entry's)
with the three open-coded defers pending, `X30` inside `DeferOrder`. -/
def wmG : Memory := witMem (tabWords T0 ++ [(wsp - 89, 7), (wsp - 80, func3A), (wsp - 72, pA),
  (wsp - 64, func2A), (wsp - 56, pA), (wsp - 48, func1A), (wsp - 40, pA),
  (wsp - 32, wsp - 48), (wsp - 24, wsp - 64), (wsp - 16, wsp - 80)])

def wsG : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 (Extracted.entry + 0xdc)
      else if i = 29 then BitVec.ofNat 64 (wsp - 136) else if i = 0 then 1#64 else 0,
    sp := BitVec.ofNat 64 (wsp - 128), pc := BitVec.ofNat 64 gA,
    flags := ⟨false, false, false, false⟩, mem := wmG }

theorem env_G : Env0 T0 wmG := by
  unfold Env0
  have hnd : ndef wmG = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem wsG_find : FuncInfo.find T0 (wsG.regs 30).toNat = some fi := by decide

theorem defers_G : defers0 wmG = [] := by
  have hnd : ndef wmG = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem wsG_pre : GopanicPre PW fi wsG := by
  refine ⟨⟨env_G, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmG
    rw [room0_eq]; decide
  · intro _; refine ⟨by decide, ?_⟩
    simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · sorry
'''
c='(∃ (s_c : State) (fi : FuncInfo), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") ∧\n      FuncInfo.find Extracted.funcs (s_c.regs 30).toNat = some fi ∧ GopanicPre P fi s_c)'
patch(path,defs,[(c,'⟨wsG, fi, rfl, wsG_find, wsG_pre⟩')],subs={'PW':'P','implW':'impl','U0':'U'})

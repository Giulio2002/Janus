import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs/DeferTwice.lean'
defs='''/-- The call state at `runtime.deferproc`'s entry. -/
def wsCall : State := PanicSat.sstate dpA wm 0 0

@[reducible] def dpSite (P : PanicRuntime) (s_c : State) : Prop :=
  PanicPre P 1 s_c ∧ 0 < P.room s_c.mem (gOf s_c)

theorem wsCall_pre : dpSite PW wsCall :=
  ⟨PanicSat.sstate_pre 1 (by decide) dpA 0 0 env_w (by decide) (by decide) (by decide),
    by show 0 < room0 wm; rw [room0_eq]; decide⟩

/-- The call state at `runtime.deferreturn`'s entry. -/
def wsRet : State := PanicSat.sstate drA wm 0 0

theorem defers_w : defers0 wm = [] := by
  have hnd : ndef wm = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem saved_w : saved0 wm = none := by rw [saved0_eq]; decide

theorem wsRet_pre : DeferreturnPre PW wsRet := by
  refine ⟨PanicSat.sstate_pre 0 (by decide) drA 0 0 env_w (by decide) (by decide) (by decide), ?_⟩
  show FrameOK (P0 T0 RPa) wm _ _
  have hm : wsRet.mem = wm := rfl
  simp [hm, retFrame, frameItems, recItems, P0_defers, P0_saved, PanicSat.sstate, defers_w, saved_w, gOf, FrameOK]
'''
c='(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") ∧\n      dpSite P s_c)'
c2='(∃ s_r : State, s_r.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") ∧\n      DeferreturnPre P s_r)'
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩'),(c2,'⟨wsRet, rfl, wsRet_pre⟩')],subs={'PW':'P','implW':'impl'})

import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs-amd64/DeferTwice/Proof.lean'
S='Janus.Contracts.PanicSatAmd64'
defs=f'''/-- The call state at `runtime.deferproc`'s entry. -/
def wsCall : Janus.Amd64.State := {S}.sstate dpA wm 0 0

@[reducible] def dpSite (P : Spec.PanicRuntime) (s_c : Janus.Amd64.State) : Prop :=
  PanicPre P 1 s_c ∧ 0 < P.room s_c.mem (gOf s_c)

theorem wsCall_pre : dpSite PW wsCall :=
  ⟨{S}.sstate_pre 1 (by decide) dpA 0 0 env_w (by decide) (by decide) (by decide) (by decide),
    by show 0 < room0 wm; rw [room0_eq]; decide⟩

/-- The call state at `runtime.deferreturn`'s entry. -/
def wsRet : Janus.Amd64.State := {S}.sstate drA wm 0 0

theorem defers_w : defers0 wm = [] := by
  have hnd : ndef wm = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem saved_w : saved0 wm = none := by rw [saved0_eq]; decide

theorem wsRet_pre : DeferreturnPre PW wsRet := by
  refine ⟨{S}.sstate_pre 0 (by decide) drA 0 0 env_w (by decide) (by decide) (by decide) (by decide), ?_⟩
  show FrameOK (P0 T0 RPa) wm _ _
  have hm : wsRet.mem = wm := rfl
  simp [hm, retFrame, Panic.frameItems, Panic.recItems, P0_defers, P0_saved, {S}.sstate, defers_w, saved_w,
    gOf, FrameOK, Panic.FrameOK]
'''
c='(∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") ∧\n      dpSite P s_c)'
c2='(∃ s_r : Janus.Amd64.State, s_r.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferreturn") ∧\n      DeferreturnPre P s_r)'
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩'),(c2,'⟨wsRet, rfl, wsRet_pre⟩')],subs={'PW':'P','implW':'impl'})

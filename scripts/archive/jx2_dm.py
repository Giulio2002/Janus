import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
from jx2gp import gr_defs, dr_defs
isa=sys.argv[1]; arm=isa=='arm64'
path='examples/proofs/DeferMix.lean' if arm else 'examples/proofs-amd64/DeferMix/Proof.lean'
S='State' if arm else 'Janus.Amd64.State'
SS='PanicSat' if arm else 'Janus.Contracts.PanicSatAmd64'
FI='FuncInfo' if arm else 'Spec.FuncInfo'
PR='PanicRuntime' if arm else 'Spec.PanicRuntime'
M='Memory' if arm else 'Janus.Arm64.Memory'
pc='s_c.pc' if arm else 's_c.rip'
W='0x48000' if arm else '0x4ff00'
F=96 if arm else 88
rsp=F if arm else F+8
lr='loc_DeferMix_60' if arm else 'loc_DeferMix_69'
res='0x44' if arm else '0x49'
n='(by decide) (by decide) (by decide)'+('' if arm else ' (by decide)')
pp = f"⟨env_w, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩" if arm else f"⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, rfl, rfl, by decide, ?_⟩"
if arm:
    regs=f"if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ({lr}) else if i = 29 then BitVec.ofNat 64 ({W} - {F} - 8) else if i = 0 then 1#64 else 0"
    st=f"{{ regs := fun i => {regs},\n    sp := BitVec.ofNat 64 ({W} - {F}), pc := BitVec.ofNat 64 gA,\n    flags := ⟨false, false, false, false⟩, mem := wmG }}"
    mem="wm"; fsp="wsG.sp.toNat"; find=f"FuncInfo.find T0 (wsG.regs 30).toNat = some wfi"
    findc=f"FuncInfo.find Extracted.funcs (s_c.regs 30).toNat = some fi"
    pfo='frameOf'; unf='Panic.FrameOK'; ex=''
else:
    st=f"{{ regs := fun i => if i = 4 then BitVec.ofNat 64 ({W} - {rsp}) else if i = 14 then BitVec.ofNat 64 wg else if i = 0 then 1#64 else 0,\n    rip := BitVec.ofNat 64 gA, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := wmG }}"
    fsp="fspOf wsG"; find="Spec.FuncInfo.find T0 (wsG.mem.readLE (wsG.regs 4).toNat 8) = some wfi"
    findc="Spec.FuncInfo.find Extracted.funcs (s_c.mem.readLE (s_c.regs 4).toNat 8) = some fi"
    pfo='Panic.frameOf'; unf='FrameOK Panic.FrameOK'; ex='unfold frameOf'
if arm: memdef="def wmG : Memory := wm\n"
else: memdef=f"""def wmG : Janus.Arm64.Memory :=
  ⟨(witMemD (tabWords T0 ++ [(wsp, ret), ({W} - {rsp}, {lr})]) Extracted.data).bytes,
    (witMemD (tabWords T0 ++ [(wsp, ret), ({W} - {rsp}, {lr})]) Extracted.data).regions ++ [⟨accA, 8, true⟩]⟩
"""
d=f"""/-- The call state at `runtime.deferprocStack`'s entry (the record at the stack word `0x41000`). -/
def wsDs : {S} := {SS}.sstate dsA wm 0x41000 0

@[reducible] def dsSite (P : {PR}) (s_c : {S}) : Prop :=
  PanicPre P 1 s_c ∧ 0 < P.room s_c.mem (gOf s_c) ∧ (s_c.regs 0).toNat + 48 ≤ 2 ^ 48 ∧
    s_c.mem.accessible (s_c.regs 0).toNat 48 true = true ∧ Outside (s_c.regs 0).toNat 48 P.priv

theorem wsDs_pre : dsSite PW wsDs :=
  ⟨{SS}.sstate_pre 1 (by decide) dsA 0x41000 0 env_w {n},
    by show 0 < room0 wm; rw [room0_eq]; decide, by decide, by decide,
    by simp only [P0_priv, outside_cons, outside_nil, and_true]; decide⟩

/-- The call state at `runtime.deferproc`'s entry. -/
def wsCall : {S} := {SS}.sstate dpA wm 0 0

@[reducible] def dpSite (P : {PR}) (s_c : {S}) : Prop :=
  PanicPre P 1 s_c ∧ 0 < P.room s_c.mem (gOf s_c)

theorem wsCall_pre : dpSite PW wsCall :=
  ⟨{SS}.sstate_pre 1 (by decide) dpA 0 0 env_w {n},
    by show 0 < room0 wm; rw [room0_eq]; decide⟩

def wfi : {FI} := {FI}.named Extracted.funcs "example.com/basic.DeferMix"

/-- The call state at `runtime.gopanic`'s entry: `DeferMix`'s own frame (no open-coded defers), return address inside it. -/
{memdef}
def wsG : {S} :=
  {st}

theorem wsG_find : {find} := by decide

theorem defers_G : defers0 wmG = [] := by
  have hnd : ndef wmG = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem env_G : Env0 T0 wmG := by
  unfold Env0
  have hnd : ndef wmG = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem wsG_pre : GopanicPre PW wfi wsG := by
  refine ⟨{pp.replace('env_w','env_G')}, by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmG
    rw [room0_eq]; decide
  · intro h
    have hod : wfi.openDefer = none := by rfl
    rw [hod] at h; exact absurd h (by decide)
  · have hs : {fsp} = {W} - {F} := by decide
    have hr : PW.defers wmG (gOf wsG) = [] := defers_G
    have f_frame : wfi.frame = {F} := by rfl
    have f_od : wfi.openDefer = none := by rfl
    have f_res : wfi.resume = Extracted.entry + {res} := by rfl
    have hbd : wfi.bound ({W} - {F}) = {W} := by
      unfold {FI}.bound; rw [f_frame]; try rfl
    have hF : {pfo} wfi ({W} - {F}) wmG = ⟨{W} - {F}, {W}, Extracted.entry + {res}, none⟩ := by
      unfold {pfo}; rw [hbd, f_res, f_od]
    show FrameOK PW wmG (frameOf wfi ({fsp}) wmG) (frameItems wmG (frameOf wfi ({fsp}) wmG) (PW.defers wmG (gOf wsG)))
    rw [hs, hr]
    {ex}
    rw [hF]
    unfold {unf}
    simp [frameItems, recItems]
"""
d2,c2,p2=dr_defs(isa,wm='wm')
c0=f'(∃ s_c : {S}, {pc} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocStack") ∧\n      dsSite P s_c)'
c1=f'(∃ s_c : {S}, {pc} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferproc") ∧\n      dpSite P s_c)'
cg=f'(∃ (s_c : {S}) (fi : {FI}), {pc} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") ∧\n      {findc} ∧ GopanicPre P fi s_c)'
patch(path,d+"\n"+d2,[(c0,'⟨wsDs, rfl, wsDs_pre⟩'),(c1,'⟨wsCall, rfl, wsCall_pre⟩'),(cg,'⟨wsG, wfi, rfl, wsG_find, wsG_pre⟩'),(c2,p2)],subs={'PW':'P','implW':'impl','U0':'U','U1':'U'})

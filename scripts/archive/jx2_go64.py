import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
path='examples/proofs-amd64/DeferOrder/Proof.lean'
W='0x4ff00'
defs=f'''def fi : Spec.FuncInfo := Spec.FuncInfo.named Extracted.funcs "example.com/basic.DeferOrder"

/-- The call state at `runtime.gopanic`'s entry: `DeferOrder`'s frame (`RSP` 120 below the entry's, the
return address inside `DeferOrder` at `[RSP]`) with the three open-coded defers pending. -/
def wmG : Janus.Arm64.Memory := witMem (tabWords T0 ++ [(wsp, ret), (wsp - 120, loc_DeferOrder_236),
  (wsp - 89, 7), (wsp - 80, func3A), (wsp - 72, pA),
  (wsp - 64, func2A), (wsp - 56, pA), (wsp - 48, func1A), (wsp - 40, pA),
  (wsp - 32, wsp - 48), (wsp - 24, wsp - 64), (wsp - 16, wsp - 80)])

def wsG : Janus.Amd64.State :=
  {{ regs := fun i => if i = 4 then BitVec.ofNat 64 (wsp - 120) else if i = 14 then BitVec.ofNat 64 wg
      else if i = 0 then 1#64 else 0,
    rip := BitVec.ofNat 64 gA, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := wmG }}

theorem env_G : Env0 T0 wmG := by
  unfold Env0
  have hnd : ndef wmG = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem wsG_find : Spec.FuncInfo.find T0 (wsG.mem.readLE (wsG.regs 4).toNat 8) = some fi := by decide

theorem defers_G : defers0 wmG = [] := by
  have hnd : ndef wmG = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem wsG_pre : GopanicPre PW fi wsG := by
  refine ⟨⟨env_G, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, rfl, rfl, by decide, ?_⟩,
    by decide, ?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmG
    rw [room0_eq]; decide
  · intro _; refine ⟨by decide, ?_⟩
    simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · have hw : wsp = {W} := rfl
    have hs : fspOf wsG = {W} - 112 := by decide
    have hr : PW.defers wmG (gOf wsG) = [] := defers_G
    have f_frame : fi.frame = 112 := by rfl
    have f_od : fi.openDefer = some (81, 24) := by rfl
    have f_res : fi.resume = Extracted.entry + 0xed := by rfl
    have hbA : fi.bitsAt ({W} - 112) = {W} - 89 := by
      unfold Spec.FuncInfo.bitsAt Spec.FuncInfo.varp; rw [f_frame, f_od]; try rfl
    have hsA : fi.slotsAt ({W} - 112) = {W} - 32 := by
      unfold Spec.FuncInfo.slotsAt Spec.FuncInfo.varp; rw [f_frame, f_od]; try rfl
    have hbd : fi.bound ({W} - 112) = {W} := by
      unfold Spec.FuncInfo.bound; rw [f_frame]; try rfl
    have hbit : wmG.readLE ({W} - 89) 1 = 7 := by rw [← hw]; decide
    have hF : Panic.frameOf fi ({W} - 112) wmG = ⟨{W} - 112, {W}, Extracted.entry + 0xed, some ({W} - 89, {W} - 32)⟩ := by
      unfold Panic.frameOf; rw [hbA, hsA, hbd, f_res, f_od]
      simp only [hbit]; try rfl
    show FrameOK PW wmG (frameOf fi (fspOf wsG) wmG) (frameItems wmG (frameOf fi (fspOf wsG) wmG) (PW.defers wmG (gOf wsG)))
    rw [hs, hr]
    unfold frameOf
    rw [hF]
    have hI : frameItems wmG ⟨{W} - 112, {W}, Extracted.entry + 0xed, some ({W} - 89, {W} - 32)⟩ [] =
        [{{ fn := {W} - 80, bits := some 3, chain := [] }}, {{ fn := {W} - 64, bits := some 1, chain := [] }},
         {{ fn := {W} - 48, bits := some 0, chain := [] }}] := by
      unfold frameItems openItems recItems
      simp only [hbit]
      decide
    unfold FrameOK Panic.FrameOK
    rw [hI]
    simp only [hbit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, P0_priv, outside_cons,
      outside_nil, and_true]
    decide
'''
c='(∃ (s_c : Janus.Amd64.State) (fi : Spec.FuncInfo), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") ∧\n      Spec.FuncInfo.find Extracted.funcs (s_c.mem.readLE (s_c.regs 4).toNat 8) = some fi ∧ GopanicPre P fi s_c)'
patch(path,defs,[(c,'⟨wsG, fi, rfl, wsG_find, wsG_pre⟩')],subs={'PW':'P','implW':'impl','U1':'U'})

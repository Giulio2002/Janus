import sys; sys.path.insert(0,'scripts')
from jx2gen import patch
from jx2gp import dr_defs
isa=sys.argv[1]; arm=isa=='arm64'
path='examples/proofs/RangeDefer.lean' if arm else 'examples/proofs-amd64/RangeDefer/Proof.lean'
S='State' if arm else 'Janus.Amd64.State'
SS='PanicSat' if arm else 'Janus.Contracts.PanicSatAmd64'
PR='PanicRuntime' if arm else 'Spec.PanicRuntime'
M='Memory' if arm else 'Janus.Arm64.Memory'
pc='s_c.pc' if arm else 's_c.rip'
n='(by decide) (by decide) (by decide)'+('' if arm else ' (by decide)')
tokreg=2 if arm else 1
xfer = """theorem pre_xfer {P : PanicRuntime} {n : Nat} {s t : State} (h : PanicPre P n s) (h28 : t.regs 28 = s.regs 28)
    (h30 : t.regs 30 = s.regs 30) (h29 : t.regs 29 = s.regs 29) (hsp : t.sp = s.sp) (hm : t.mem = s.mem) :
    PanicPre P n t := by
  obtain ⟨he, ⟨g1, g2, g3⟩, hc, ho⟩ := h
  refine ⟨by rw [hm]; exact he, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa [regG, h28] using g1
  · simpa [regG, h28, hm] using g2
  · simpa [stackguard0, regG, h28, hsp, hm] using g3
  · simpa [CallOK, h30, h29, hsp, hm] using hc
  · simpa [hsp, hm] using ho
""" if arm else ""
wsdef = (f"{{ {SS}.sstate paA wmT 0 0 with regs := fun i => if i = {tokreg} then 5 else ({SS}.sstate paA wmT 0 0).regs i }}" if arm else f"{SS}.sstate paA wmT 0 5")
prf = f"    have h := {SS}.sstate_pre 2 (by decide) paA 0 0 env_T {n}\n    exact pre_xfer h rfl rfl rfl rfl rfl\n" if arm else f"    exact {SS}.sstate_pre 2 (by decide) paA 0 5 env_T {n}\n"
d=xfer+f"""/-- The call state at `runtime.deferrangefunc`'s entry. -/
def wsRf : {S} := {SS}.sstate rfA wm 0 0

@[reducible] def rfSite (P : {PR}) (s_c : {S}) : Prop :=
  PanicPre P 0 s_c ∧ 0 < P.room s_c.mem (gOf s_c)

theorem wsRf_pre : rfSite PW wsRf :=
  ⟨{SS}.sstate_pre 0 (by decide) rfA 0 0 env_w {n},
    by show 0 < room0 wm; rw [room0_eq]; decide⟩

/-- The witness memory with one range-over-func `_defer` record (token `5`) on the chain. -/
def wmT : {M} :=
  ⟨(witMemD (tabWords T0 ++ [(B + 8, 1), (B + 0x208, 5)]) Extracted.data).bytes,
    (witMemD (tabWords T0 ++ [(B + 8, 1), (B + 0x208, 5)]) Extracted.data).regions ++ [⟨accA, 8, true⟩]⟩

theorem env_T : Env0 T0 wmT := by
  unfold Env0
  have hnd : ndef wmT = 1 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · rw [hnd] at hi
    have : i = 0 := by omega
    subst this
    exact ⟨by decide, fun h => by exfalso; revert h; decide⟩
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

/-- The call state at `runtime.deferprocat`'s entry (`fn` 0, the token `5`). -/
def wsPa : {S} := {wsdef}

@[reducible] def paSite (P : {PR}) (s_c : {S}) : Prop :=
  PanicPre P 2 s_c ∧ 0 < P.room s_c.mem (gOf s_c) ∧
    ∃ r rest, P.defers s_c.mem (gOf s_c) = r :: rest ∧ r.token = some (s_c.regs {tokreg}).toNat

theorem wsPa_pre : paSite PW wsPa := by
  refine ⟨?_, ?_, ?_⟩
  · {prf.strip()}
  · show 0 < room0 wmT
    rw [room0_eq]; decide
  · refine ⟨{{ sp := 0, fns := [], token := some 5 }}, [], ?_, rfl⟩
    show defers0 wmT = _
    rw [defers0_eq]; decide
"""
d2,c2,p2=dr_defs(isa,wm='wm')
c0=f'(∃ s_c : {S}, {pc} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferrangefunc") ∧\n      rfSite P s_c)'
c1=f'(∃ s_c : {S}, {pc} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.deferprocat") ∧\n      paSite P s_c)'
patch(path,d+"\n"+d2,[(c0,'⟨wsRf, rfl, wsRf_pre⟩'),(c1,'⟨wsPa, rfl, wsPa_pre⟩'),(c2,p2)],subs={'PW':'P','implW':'impl','U0':'U','U1':'U'})

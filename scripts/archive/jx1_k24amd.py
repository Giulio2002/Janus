#!/usr/bin/env python3
"""amd64 K24 call-site upgrade: python3 scripts/archive/jx1_k24amd.py Lookup|Insert"""
import sys
which=sys.argv[1]
p=f'examples/proofs-amd64/{which}K24/Proof.lean'
t=open(p).read()
i=t.index('/-- All hypotheses of `correctness` are satisfiable together')
if which=='Lookup':
    M='MK'; Mt='MK'
    site_pre='''  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ KeyRegular (rtView M.priv s_c.mem) (s_c.regs 0).toNat 24 ∧
    IsMap M s_c.mem (s_c.regs 3).toNat f ∧ KeyIn s_c M.depth 3 (s_c.regs 1).toNat 24'''
    sig='(M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8)))'
    name='Access1GSite'; app='MK AMap.empty'; sname='mapaccess1'
    regs='''if i = 0 then BitVec.ofNat 64 mapType else if i = 3 then mv else if i = 1 then kp'''
    goalstmt='Access1GSite MK AMap.empty wsCall'
    refine='''  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, ?_,
    (isMap_of_ne (by decide)).2 ⟨rfl, rfl, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩'''
    priv='MK.priv'; simpm='MK, privK'; extra=''
else:
    sig='(M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (H : RtReady) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8)))'
    site_pre='''  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ KeyRegular (rtView M.priv s_c.mem) (s_c.regs 0).toNat 24 ∧
    (s_c.regs 3).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 3).toNat f ∧ KeyIn s_c M.depth 3 (s_c.regs 1).toNat 24 ∧
    Ready64 H M.priv [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat,
      s_c.mem.readLE (s_c.regs 1).toNat 24] s_c'''
    name='AssignGSite'; sname='mapassign'
    regs='''if i = 0 then BitVec.ofNat 64 mapType else if i = 3 then mv else if i = 1 then kp'''
    goalstmt='AssignGSite (MCW ck24) HAssign AMap.empty wsCall'
    refine='''  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, ?_, ?_,
    ⟨?_, ?_, ?_, Or.inl ⟨?_, rfl⟩⟩, ⟨?_, ?_, ?_⟩, ?_⟩'''
    priv='(MCW ck24).priv'; simpm='MCW, privW, HAssign, Ready64'
site=f'''/-- The precondition of `{name[:-4]}`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def {name} {sig}
    (s_c : Janus.Amd64.State) : Prop :=
{site_pre}

/-- The call state of the `{sname}` contract (U-WITNESS-CALLSITE): like `s0` at the callee's entry, the map type in `RAX`. -/
def wsCall : Janus.Amd64.State :=
  {{ regs := fun i => {regs}
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 cAddr, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmemK }}

set_option maxRecDepth 100000 in
theorem wsCall_pre : {goalstmt} := by
  janus_eval_nat hT : mapType
  have hR : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → (rtView {priv} mmemK).readLE a n = mmemK.readLE a n :=
    fun a n h1 h2 => readLE_rtView ((inPriv0 h1 h2).append_left _)
  have hW : (rtView {priv} mmemK).readLE (mapType + 48) 8 = KT24 := by
    rw [readLE_rtView ⟨(mapType + 48, mapType + 56), by simp [{'MK, privK' if which=='Lookup' else 'MCW, privW'}], Nat.le_refl _, Nat.le_refl _⟩]
    simp only [mmemK, KT24, hT]; decide
{refine}
  all_goals first
    | (show KeyRegular (rtView {priv} mmemK) (BitVec.ofNat 64 mapType).toNat 24
       rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hT]; decide)]
       unfold KeyRegular keyType tySize isRegularMemory tyTFlag; rw [hW, hR _ _ (by decide) (by decide)]
       try rw [hR _ _ (by decide) (by decide)]
       simp only [mmemK, KT24, hT]; decide)
    | (simp only [wsCall, mv, kp, {simpm}, priv0, calleeStack, Janus.Spec.Disjoint, ZEnv, mmemK, hT,
        outside_cons, outside_nil, outside_append, and_true, regG, regSP, stackguard0Offset, KeyIn,
        Janus.Arm64.Memory.accessible, Janus.Arm64.Memory.readLE] <;> decide)

'''
t=t[:i]+site+t[i:]
r=t.index('/-- So the guarantee is reached')
e=t.index('end Witness')
rb=t[r:e]; t=t[:r]+t[e:]
i=t.index('/-- All hypotheses of `correctness`')
t=t[:i]+rb.rstrip()+'\n\n'+t[i:]
if which=='Lookup':
    old="""    m.toNat ≠ 0 ∧ pre M m kp f s :=
  ⟨implAt, MK, ret, s0, mv, kp, AMap.empty, MK_laws, model, hret, setup, by decide, pre0⟩"""
    new="""    m.toNat ≠ 0 ∧ pre M m kp f s ∧
    (∃ (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapaccess1") ∧ Access1GSite M f s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ s'.regs 0 = (f (keyAt s.mem kp.toNat 24)).getD 0 :=
  ⟨implAt, MK, ret, s0, mv, kp, AMap.empty, MK_laws, model, hret, setup, by decide, pre0,
    ⟨AMap.empty, wsCall, rfl, wsCall_pre⟩,
    correctness implAt MK MK_laws model mv kp AMap.empty ret hret s0 setup pre0⟩"""
else:
    old="""    pre M H m kp f s :=
  ⟨implAt, MCW _, HAssign, ret, s0, mv, kp, v, AMap.empty, MCW_laws _, model, hret, setup, pre0⟩"""
    new="""    pre M H m kp f s ∧
    (∃ (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapassign") ∧ AssignGSite M H f s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (M.Rep s'.mem m.toNat (f.set (keyAt s.mem kp.toNat 24) v) ∧ M.Env s'.mem (s.regs 14)) :=
  ⟨implAt, MCW _, HAssign, ret, s0, mv, kp, v, AMap.empty, MCW_laws _, model, hret, setup, pre0,
    ⟨AMap.empty, wsCall, rfl, wsCall_pre⟩,
    correctness implAt (MCW _) (MCW_laws _) HAssign model mv kp v AMap.empty ret hret s0 setup pre0⟩"""
assert old in t
t=t.replace(old,new)
open(p,'w').write(t)

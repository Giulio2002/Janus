import sys; sys.path.insert(0,'scripts')
from jx2gen import patch,runconj_auto
isa=sys.argv[1]
arm = isa=='arm64'
path='examples/proofs/CopyNodes.lean' if arm else 'examples/proofs-amd64/CopyNodes/Proof.lean'
St='State' if arm else 'Janus.Amd64.State'
if arm:
    wsc='''def wsCall : State :=
  { regs := (wstate (args [NT, 0, 0, 0, 0])).regs, sp := BitVec.ofNat 64 (wsp - 64),
    pc := BitVec.ofNat 64 cAddr, flags := ⟨false, false, false, false⟩, mem := wmemD }'''
    pre='RtPre'; argw='argWords'; cs='calleeStack'; MEM='Memory'
    cok='⟨by decide, by decide, by decide, by decide, by decide, by decide, Memory.accessible_mono _ hw (by decide) (by decide)⟩'
else:
    wsc='''def wsCall : Janus.Amd64.State :=
  { regs := (wstate (args [NT, 0, 0, 0, 0])).regs, rip := BitVec.ofNat 64 cAddr,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := mem0 }'''
    pre='RtPre64'; argw='argWords64'; cs='calleeStack64'; MEM='Arm64.Memory'
    cok='⟨by decide, by decide, by decide, by decide, Arm64.Memory.accessible_mono _ hw (by decide) (by decide)⟩'
defs=f'''/-- The call state at `runtime.typedslicecopy`'s entry (`typedslicecopy(node, 0, 0, 0, 0)`). -/
{wsc}

@[reducible] def rpSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : {St}) : Prop :=
  {pre} rt 4096 H typedslicecopySpec s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : rpSite rtW HA wsCall := by
  have ha : {argw} wsCall typedslicecopySpec.nargs = [NT, 0, 0, 0, 0] := by decide
  have hw : {'wmemD' if arm else 'mem0'}.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  refine ⟨{cok}, ?_, ?_, trivial, ?_⟩
  · rw [ha]
    show TypeOK wsCall.mem NT ∧ 0 < 2 ^ 63 ∧ 0 < 2 ^ 63 ∧ 0 + min 0 0 * typSize wsCall.mem NT ≤ 2 ^ 48 ∧
      (0 < min 0 0 * typSize wsCall.mem NT → wsCall.mem.accessible 0 (min 0 0 * typSize wsCall.mem NT) true = true) ∧
      Readable wsCall.mem 0 (min 0 0 * typSize wsCall.mem NT)
    refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, fun h => absurd h (by decide), ?_⟩
    simp [Readable]
  · rw [ha]; intro r hr
    simp only [typedslicecopySpec, arg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show Outside NT 16 _
      simp only [{cs}, outside_cons, outside_nil, wsCall]; decide
    · show Outside 0 (min 0 0 * typSize wsCall.mem NT) _
      simp only [Nat.min_self, Nat.zero_mul, {cs}, outside_cons, outside_nil, wsCall]; decide
  · exact ready_intro rfl ⟨ha, trivial⟩
'''
if not arm: defs=defs  # NT defined in file
pcf='pc' if arm else 'rip'
c=f'(∃ s_c : {St}, s_c.{pcf} = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typedslicecopy") ∧\n      rpSite rt H s_c)'
rc=runconj_auto(path,{k:'(0 : BitVec 64)' for k in 'ptr len cap x y z'.split()}) if False else None
import re
txt=open(path).read()
m=re.search(r"theorem correctness.*?\(H : RtReady\)((?:\s*\([^()]*: BitVec 64\))+)",txt,re.S)
ps=[]
for g in re.findall(r"\(([^()]*): BitVec 64\)",m.group(1)): ps+=g.split()
rc=runconj_auto(path,{k:'(0 : BitVec 64)' for k in ps})
patch(path,defs,[(c,'⟨wsCall, rfl, wsCall_pre⟩')],runconj=rc,retproof='correctness implAt rtW HA '+' '.join('0' for _ in ps)+' model ret hret s0 setup pre')

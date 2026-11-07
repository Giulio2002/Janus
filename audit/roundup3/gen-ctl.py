#!/usr/bin/env python3
"""Generate the witness-bearing control rows (audit/roundup3/ctl/*.lean) from the Add-based control rows of
audit/roundup3/rows (N01-N06, N12) and V15 (/srv/janus-rt-n11/audit/roundn11/icall2): each row's main theorem plus a Witness namespace of the
frozen shape (hypotheses, pre, call-site state, Returns run) instantiated at the stock writer of Janus.Contracts.ICallSat.
Usage: gen-ctl.py ROWS_DIR OUT_DIR."""
import re, sys, os
rows, out = sys.argv[1], sys.argv[2]
# row -> (values for fn fn2 k w n a, hypothesis list [(name,text)], nargs, stack, above) with values substituted as Nat literals
BIND = "(impl : List Segment) (fn fn2 k w n a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)"
P = {
 'N01_ctl_stack_plus_w': dict(k=16, w=32, n=0, a=0, nargs=4, stack='k', above='48', hyps=['8 ≤ k', 'k + 16 ≤ w']),
 'N02_ctl_stack_lt_w': dict(k=16, w=17, n=0, a=0, nargs=4, stack='k', above='48', hyps=['8 ≤ k', 'k < w']),
 'N03_ctl_above_w': dict(k=0, w=56, n=0, a=48, nargs=4, stack='16', above='a', hyps=['48 ≤ a', 'a + 8 ≤ w']),
 'N04_ctl_shared_w': dict(k=16, w=64, n=0, a=48, nargs=4, stack='k', above='a', hyps=['8 ≤ k', '48 ≤ a', 'k + 16 ≤ w', 'a < w']),
 'N05_ctl_c_max': dict(k=16, w=16 + 140737488355327, n=0, a=0, nargs=4, stack='k', above='48', hyps=['8 ≤ k', 'k + 140737488355327 ≤ w']),
 'N06_ctl_nargs_w': dict(k=0, w=7, n=4, a=520, nargs='n', stack='16', above='a', hyps=['1 ≤ n', '520 ≤ a', 'n + 3 ≤ w']),
 'N12_post_w': dict(k=16, w=32, n=0, a=0, nargs=4, stack='k', above='48', hyps=['8 ≤ k', 'k + 16 ≤ w'], post_extra=' ∧ w = w'),
}
def lit(e, v):  # expression over k w n a -> its literal value
    return str(eval(e, {}, {x: v[x] for x in 'kwna'})) if re.search('[kwna]', e) else e
os.makedirs(out, exist_ok=True)
for name, p in P.items():
    src = open(f'{rows}/{name}.lean').read()
    head = src[:src.index('theorem correctness')]
    tm = src[src.index('theorem correctness'):src.index('end Proof')]
    nargs, stack, above = (lit(str(p[x]), p) for x in ('nargs', 'stack', 'above'))
    post_extra = p.get('post_extra', '')
    hyps_sub = ' ∧ '.join(f'({h})' for h in p['hyps'])
    hnames = [f'h{i}' for i in range(len(p['hyps']))]
    args = f"impl A0 0 {p['k']} {p['w']} {p['n']} {p['a']} rt0 R0 3 4"
    hdecl = ' '.join(f'(by decide)' for _ in p['hyps'])
    hx = ' ∧ '.join(f'({h})' for h in p['hyps'])  # statement-level hypotheses (variables)
    post = f"(s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64{post_extra}"
    W = f'''
namespace Witness
open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0 R0)

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  {{ regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }}

theorem hc : ICallContract (Extracted.program.link impl) A0 {nargs} {stack} {above} rt0 (fun _ => []) R0 (fun _ => True) :=
  Summary.of_codeIn (codeIn_link Extracted.program _ (by decide))
    (Janus.Contracts.ICallSat.impl_okP (nargs := {nargs}) (stack := {stack}) (above := {above}) (P := fun _ => True) (fun _ _ => True) (fun _ => trivial))

def wsCall : State := Janus.Contracts.ICallSat.wstate

theorem wsCall_pre : ICallPre {nargs} {stack} {above} rt0 (fun _ => True) wsCall := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, by decide, ?_, trivial⟩
  show Janus.Outside 0x17f8 ({above} + 8) rt0
  simp [rt0]

theorem hret : RetAddr (Extracted.program.link impl) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧ (s'.regs 0).toNat = ((3 : BitVec 64).toNat + (4 : BitVec 64).toNat) % 2 ^ 64{post_extra} :=
  correctness impl A0 0 {p['k']} {p['w']} {p['n']} {p['a']} rt0 R0 3 4 {hdecl} hc ret hret s0 setup trivial

theorem nonvacuous : ∃ {BIND.replace('(impl : List Segment) ', '(impl : List Segment) ').replace('(R : Res) ', '(R : Res) (ret : Nat) (s : State) ')},
    {hx} ∧
    ICallContract (Extracted.program.link impl) fn {'n' if p['nargs']=='n' else '4'} {p['stack']} {p['above']} rt (fun _ => []) R (fun _ => True) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s ∧ True ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre {'n' if p['nargs']=='n' else '4'} {p['stack']} {p['above']} rt (fun _ => True) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ {post} :=
  ⟨impl, A0, 0, {p['k']}, {p['w']}, {p['n']}, {p['a']}, rt0, R0, ret, s0, 3, 4, {'⟨' + ', '.join(['by decide']*len(p['hyps'])) + '⟩' if len(p['hyps'])>1 else 'by decide'}, hc, hret, setup, trivial, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness
'''
    # the hypotheses in the main theorem are separate binders (hk hw ...): the witness has them as a conjunction `h1 ∧ h2 ∧ ...`
    open(f'{out}/{name}.lean', 'w').write(head.replace('Expected: Verified', 'Expected: Verified (witness-bearing control)') + tm + W + '\nend Proof\n')

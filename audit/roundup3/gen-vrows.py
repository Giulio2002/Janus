#!/usr/bin/env python3
"""Generate audit/roundup3/vrows/*.lean, the verify-level rows of run-verify-rows.sh (all statements about `Add`):
  PINn_*  the six pins UP3 removed from JanusTests/ICallAudit.lean (statement only; rejected at verify level for want of a witness)
  ATT_*   attacker witnesses: the contract holds vacuously (size pinned unsatisfiable by the pre), the witness omits the call-site state
          (the frozen U-WITNESS-CALLSITE must reject it with 'does not exhibit a call-site state')
  KA1     the known-accepted limitation (R empty only at the arguments of a call no witness run takes): ACCEPTED, with a full witness
Usage: gen-vrows.py OUT_DIR"""
import sys, os
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
HEAD = '''import Extracted

/-! {title}
Expected-verdict: {verdict}
Expected-reason: {reason}
The proof is `Add`'s; the hypotheses are never used. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall Janus.Contracts

namespace Proof

'''
def stmt(binders, hyps, nargs, stack, above, pre, post="(s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64", P='fun _ => True', R='R'):
    hs = ''.join(f'\n    ({n} : {t})' for n, t in hyps)
    return f'''theorem correctness {binders}{hs}
    (hc : ICallContract (Extracted.program.link impl) fn {nargs} {stack} {above} rt (fun _ => []) {R} ({P})) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => {pre})
      (fun _ s' => {post}) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
'''
B = "(impl : List Segment) (fn k w a : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)"
PINS = [  # name, hyps, stack, above, pre
 ('PIN1_k_eq_7', [], 'k', '48', 'k = 7'),
 ('PIN2_7_eq_k', [], 'k', '48', '7 = k'),
 ('PIN3_w_lt_8', [('hw', 'k ≤ w')], 'k', '48', 'w < 8'),
 ('PIN4_w_lt_20', [('hk', '8 ≤ k'), ('hw', 'k + 16 ≤ w')], 'k', '48', 'w < 20'),
 ('PIN5_let_w2_lt_8', [('hw', 'k ≤ w')], 'k', '48', '(let w2 := w; w2 < 8)'),
 ('PIN6_a_eq_48', [('ha', '48 ≤ a')], '16', 'a', 'a = 48'),
]
for n, hyps, stack, above, pre in PINS:
    t = HEAD.format(title=f'Verify-level row {n} (a pin UP3 removed from ICallAudit.lean): statement-only, no witness', verdict='rejected', reason='no verified Witness|Witness') 
    open(f'{out}/{n}.lean', 'w').write(t + stmt(B, hyps, 4, stack, above, pre) + '\nend Proof\n')

# attacker witnesses (k pinned to 7 by the pre: CallOK needs 8 <= k, so the contract holds by `exfalso`)
ATT = [
 ('ATT_N11_k_eq_7', [], 'k = 7', 7, 0),
 ('ATT_N10_w_lt_8', [('hw', 'k ≤ w')], 'w < 8', 7, 7),
 ('ATT_N18_let_w2_lt_8', [('hw', 'k ≤ w')], '(let w2 := w; w2 < 8)', 7, 7),
]
for n, hyps, pre, kv, wv in ATT:
    hx = ''.join(f'({h}) ∧ ' for _, h in hyps)
    decs = ''.join('by decide, ' for _ in hyps)
    rfls = ' ∧ '.join(['x'])  # placeholder
    W = f'''
namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  {{ regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }}

theorem hc7 : ICallContract (Extracted.program.link ([] : List Segment)) 0 4 7 48 [] (fun _ => [])
    (fun _ _ _ _ _ _ _ => True) (fun _ => True) := by
  intro s _ h
  exfalso
  have := h.1.2.2.2.2.1
  omega

theorem hret : RetAddr (Extracted.program.link ([] : List Segment)) ret := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link ([] : List Segment)).withExit ret) Extracted.entry [3, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem returns : Returns ((Extracted.program.link ([] : List Segment)).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 0).toNat = ((3 : BitVec 64).toNat + (4 : BitVec 64).toNat) % 2 ^ 64 :=
  correctness [] 0 {kv} {wv} 0 [] (fun _ _ _ _ _ _ _ => True) 3 4 {decs}hc7 ret hret s0 setup (by decide)

theorem nonvacuous : ∃ (impl : List Segment) (fn k w a : Nat) (rt : List (Nat × Nat)) (R : Res) (ret : Nat) (s : State) (x y : BitVec 64),
    {hx}ICallContract (Extracted.program.link impl) fn 4 k 48 rt (fun _ => []) R (fun _ => True) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x, y] s ∧ {pre} ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  ⟨[], 0, {kv}, {wv}, 0, [], fun _ _ _ _ _ _ _ => True, ret, s0, 3, 4, {decs}hc7, hret, setup, by decide, returns⟩

end Witness
'''
    t = HEAD.format(title=f'Verify-level attacker witness {n}: the pre pins the contract size to an unsatisfiable value (the contract holds vacuously); the witness proves it by exfalso and OMITS the call-site state',
                    verdict='rejected', reason='does not exhibit a call-site state')
    open(f'{out}/{n}.lean', 'w').write(t + stmt(B, hyps, 4, 'k', '48', pre) + W + '\nend Proof\n')

# KA1: R empty only at the arguments the caller would pass: accepted, witness at different arguments (P restricts the callee's arguments)
KA = HEAD.format(title='KA1 (known-accepted limitation): the Ensures pre pins `¬ R` at SPECIFIC argument values (1, 2, 3, 4), a call no witness run takes. ACCEPTED: the witness exhibits a call-site state at other arguments (P: X0 = 9)',
                 verdict='Verified', reason='known-accepted (docs/SOUNDNESS.md "UP3: known limitation")')
KA += '''def Pk : State → Prop := fun sc => sc.regs 0 = 9

theorem correctness (impl : List Segment) (fn : Nat) (rt : List (Nat × Nat)) (R : Res) (x y : BitVec 64)
    (hc : ICallContract (Extracted.program.link impl) fn 4 16 48 rt (fun _ => []) R (fun sc => sc.regs 0 = 9)) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => ∀ n e1 e2, ¬ R 1 2 3 4 n e1 e2)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Witness
open Janus.Contracts.EqHashModel (codeIn_link Summary.of_codeIn)
open Janus.Contracts.ICallSat (impl A0 rt0)

def RK : Res := fun a _ c _ n e1 e2 => a = 9 ∧ n = c ∧ e1 = 0 ∧ e2 = 0

def ret : Nat := 0x1000
def sp0 : Nat := 0x200000
def g0 : Nat := 0x300000

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 64, 104, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hc : ICallContract (Extracted.program.link impl) A0 4 16 48 rt0 (fun _ => []) RK (fun sc => sc.regs 0 = 9) := by
  have h := Janus.Contracts.ICallSat.impl_okP (nargs := 4) (stack := 16) (above := 48)
    (P := fun sc => sc.regs 0 = 9) (fun _ _ => True) (fun _ => trivial)
  sorry

end Witness
'''
# the KA1 witness body is written by hand below once the stock writer's R is adapted; see run-verify-rows.sh (row skipped if absent)
open(f'{out}/_KA1_draft.lean.txt', 'w').write(KA)

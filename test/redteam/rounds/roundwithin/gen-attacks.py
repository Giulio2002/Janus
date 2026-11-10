#!/usr/bin/env python3
"""Generates the attack files of the instruction-count-bound round (attacks/*.lean) from the shapes below, so that every
row shares the same Max/LoadField witness prelude. Run from anywhere; the files are tracked, this script documents them."""
import os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "attacks")
os.makedirs(D, exist_ok=True)

# ---------------------------------------------------------------- arm64 (artifacts/Max, artifacts/LoadField)
A_HEAD = """import Extracted

/-! {why} -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof
"""
A_POST = "(fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y)"
A_REAL = """
/-- the true bound: used by the attacks to obtain a kernel-checked statement of the weaker shape. -/
theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega
""" % A_POST
A_WIT = """
def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000
def wbytes (a : Nat) : Byte := 0
def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩
def s0 : State :=
  { regs := fun i => if i = 0 then (3) else if i = 1 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩
"""
A_CORR = """
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True) %s := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega
""" % A_POST
A_NV = """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if y.toNat < x.toNat then x else y)) :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, correctness (3) (5) ret hret s0 setup trivial⟩
"""
def a(name, why, body):
    open(os.path.join(D, name + ".lean"), "w").write(A_HEAD.format(why=why) + body + "\nend Proof\n")

a("W1_unsat_pre", "Expected-reason: has no kernel-checked non-vacuity witness. A bound (0 instructions!) proved vacuously from a precondition no state meets.", """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.1.symm.trans hp.2) (by decide)
""")
a("W1b_unsat_pre_witness_drops_pre", "Expected-reason: the witness does not exhibit the precondition. The same vacuous bound, with a witness that omits the unsatisfiable precondition.", A_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.1.symm.trans hp.2) (by decide)

namespace Witness
""" + A_WIT + """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧
    ReturnsWithin 4 (Extracted.program.withExit ret) s (fun s' => ABIReturn s s') :=
  ⟨ret, s0, (3), (5), hret, setup, (Proof.real (3) (5) ret hret s0 setup trivial).post_mono fun _ h => h.1⟩
end Witness
""")
a("W2_bound_depends_on_post", "Expected-reason: the instruction bound mentions the execution of the program. The budget is computed from the final state of a run.", A_REAL + """
/-- the "bound" reads the result of running the program: it depends on the post-state. -/
def lenOf (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat
  | _ => 0

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun s => lenOf s + 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s :=
  (real x y).mono_bound fun _ _ => Nat.le_add_left _ _
""" % A_POST)
a("W3_offbyone_within3", "Expected-reason: Lean rejected the proof (the bound is too small). Fuel off by one: `Max` needs 4 instructions on its longer path.", """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun _ => True) %s := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega
""" % A_POST)
a("W3b_offbyone_atleast4", "Expected-reason: Lean rejected the proof (the bound is too large). A lower bound of 4 where the shorter path executes 3.", """
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
""")
a("W5_untied_witness", "Expected-reason: no witness tied to `within`. Witness.nonvacuous is tied to `correctness`; the EnsuresWithin main has none of its own.", A_CORR + A_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s := real x y

namespace Witness
""" % A_POST + A_WIT + A_NV + "end Witness\n")
a("W5b_witness_has_no_run", "Expected-reason: the witness does not exhibit a RUN. Witness.within names the main `within` but states only a call state, no returning run.", A_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s := real x y

namespace Witness
""" % A_POST + A_WIT + """
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) :=
  ⟨ret, s0, (3), (5), hret, setup, trivial⟩
end Witness
""")
a("W5c_atleast_witness_no_return", "Expected-reason: the lower bound is not exhibited with a returning run. Witness.atLeast states RunsAtLeast but no Returns from the same state.", """
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Witness
""" + A_WIT + """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atLeast : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    RunsAtLeast 3 (Extracted.program.withExit ret) s :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, Proof.atLeast (3) (5) ret hret s0 setup trivial⟩
end Witness
""")
a("W6a_defwrapped_with_witness", "Expected-reason: the statement does not mention Extracted.program or Extracted.entry. A def-wrapped EnsuresWithin statement is rejected exactly like a def-wrapped Ensures, even with a tied witness.", A_REAL + """
def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s

theorem within (x y : BitVec 64) : Stmt x y := real x y

namespace Witness
""" % A_POST + A_WIT + """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    ReturnsWithin 4 (Extracted.program.withExit ret) s (fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if y.toNat < x.toNat then x else y)) :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, Proof.within (3) (5) ret hret s0 setup trivial⟩
end Witness
""")
a("W6c_defwrapped_untied", "Expected-reason: no witness tied to `within`. The statement is def-wrapped; wrapping does not exempt it from the witness rule.", A_REAL + """
def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s

theorem within (x y : BitVec 64) : Stmt x y := real x y
""" % A_POST)
a("W6d_defwrapped_bound_of_run", "Expected-reason: the instruction bound mentions the execution of the program, hidden in a def-wrapped statement.", A_REAL + """
def lenOf (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat
  | _ => 0
def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun s => lenOf s + 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s

theorem within (x y : BitVec 64) : Stmt x y := (real x y).mono_bound fun _ _ => Nat.le_add_left _ _
""" % A_POST)

a("W9_state_dependent_bound_control", "Control: a bound that is a function of the call state (it evaluates to 4) is accepted: U-BOUND-PURE does not reject a pure state-dependent bound.", A_CORR + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun s => (s.regs 1).toNat * 0 + 4) Extracted.program Extracted.entry [x, y] (fun _ => True) %s := by
  intro ret hret s hs _
  janus_intro hs
  simp only [Nat.mul_zero, Nat.zero_add]
  janus_run
  all_goals split <;> first | rfl | omega

namespace Witness
""" % A_POST + A_WIT + A_NV + """
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.regs 0 = if y.toNat < x.toNat then x else y)) :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, (Proof.within (3) (5) ret hret s0 setup trivial).returns⟩
end Witness
""")

# LoadField (arm64): the precondition admits only a faulting call (a nil receiver)
open(os.path.join(D, "W4_lower_bound_faulting_pre.lean"), "w").write("""import Extracted

/-! Expected-reason: the lower bound is not exhibited with a returning run. RunsAtLeast (here 0, and it would hold for every
bound up to the faulting instruction) is true of a state whose call faults; no call meeting this precondition returns. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem atLeast0 : RunsAtLeastOnCall (fun _ => 0) Extracted.program Extracted.entry [0#64]
    (fun s => s.mem.accessible 0 8 false = false) :=
  fun _ _ _ _ _ => rfl

namespace Witness
def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000
def wbytes (a : Nat) : Byte := 0
def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩
def s0 : State :=
  { regs := fun i => if i = 0 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atLeast0 : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    RunsAtLeast 0 (Extracted.program.withExit ret) s := by
  refine ⟨ret, s0, hret, setup, ?pre, rfl⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide
end Witness

end Proof
""")

# ---------------------------------------------------------------- amd64 (artifacts/amd64/Max, artifacts/amd64/LoadField)
M_HEAD = """import Janus
import Extracted

/-! {why} -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float
"""
M_PRE = "(fun s => StackWritable s 0 8)"
M_POST = "(fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y])"
M_TAC = """  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
"""
M_REAL = """
theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] %s %s := by
%s  all_goals simp [hbr]
""" % (M_PRE, M_POST, M_TAC)
M_WIT = """
open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 3#64
def y : BitVec 64 := 4#64
def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)
"""
M_CORR = """
theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 0 8)
      (fun r => r = [if y.toNat < x.toNat then x else y]) := by
%s  all_goals simp [hbr]
""" % M_TAC
M_NV = """
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [if y.toNat < x.toNat then x else y]) :=
  ⟨ret, s0, x, y, hret, setup, hpre, correctness x y ret hret s0 setup hpre⟩
"""
def m(name, why, body):
    open(os.path.join(D, "amd64_" + name + ".lean"), "w").write(M_HEAD.format(why=why) + body + "\nend Proof\n")

m("W1_unsat_pre", "Expected-reason: has no kernel-checked non-vacuity witness. A 0-instruction bound proved vacuously from an unsatisfiable precondition.", """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.2.1.symm.trans hp.2.2) (by decide)
""")
m("W1b_unsat_pre_witness_drops_pre", "Expected-reason: the witness does not exhibit the precondition.", M_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.2.1.symm.trans hp.2.2) (by decide)

namespace Witness
""" + M_WIT + """
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    ReturnsWithin 4 (Extracted.program.withExit ret) s (fun s' => ABIReturn s s') :=
  ⟨ret, s0, x, y, hret, setup, hpre, (Proof.real x y ret hret s0 setup hpre).post_mono fun _ h => h.1⟩
end Witness
""")
m("W2_bound_depends_on_post", "Expected-reason: the instruction bound mentions the execution of the program.", M_REAL + """
def lenOf (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat
  | _ => 0

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun s => lenOf s + 4) Extracted.program Extracted.entry [x, y] %s %s :=
  (real x y).mono_bound fun _ _ => Nat.le_add_left _ _
""" % (M_PRE, M_POST))
m("W3_offbyone_within3", "Expected-reason: Lean rejected the proof (the bound is too small).", """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 3) Extracted.program Extracted.entry [x, y] %s %s := by
%s  all_goals simp [hbr]
""" % (M_PRE, M_POST, M_TAC))
m("W3b_offbyone_atleast4", "Expected-reason: Lean rejected the proof (the bound is too large).", """
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 4) Extracted.program Extracted.entry [x, y] %s := by
%s""" % (M_PRE, M_TAC))
m("W5_untied_witness", "Expected-reason: no witness tied to `within`.", M_CORR + M_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] %s %s := real x y

namespace Witness
""" % (M_PRE, M_POST) + M_WIT + M_NV + "end Witness\n")
m("W5c_atleast_witness_no_return", "Expected-reason: the lower bound is not exhibited with a returning run.", """
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 3) Extracted.program Extracted.entry [x, y] %s := by
%s
namespace Witness
""" % (M_PRE, M_TAC) + M_WIT + """
theorem atLeast : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    RunsAtLeast 3 (Extracted.program.withExit ret) s :=
  ⟨ret, s0, x, y, hret, setup, hpre, Proof.atLeast x y ret hret s0 setup hpre⟩
end Witness
""")
m("W6a_defwrapped_with_witness", "Expected-reason: the statement does not mention Extracted.program or Extracted.entry (def-wrapped EnsuresWithin).", M_REAL + """
def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] %s %s

theorem within (x y : BitVec 64) : Stmt x y := real x y

namespace Witness
""" % (M_PRE, M_POST) + M_WIT + """
theorem within : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    ReturnsWithin 4 (Extracted.program.withExit ret) s (fun s' =>
    ABIReturn s s' ∧ (results 1 s') = [if y.toNat < x.toNat then x else y]) :=
  ⟨ret, s0, x, y, hret, setup, hpre, Proof.within x y ret hret s0 setup hpre⟩
end Witness
""")
m("W7_rsp_word_in_pre", "Expected-reason: the precondition constrains the memory word at the entry RSP (the [RSP]-word rule covers EnsuresWithin).", M_REAL + """
theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = 0) %s :=
  real x y |>.mono (fun _ h => h.1) (fun _ _ _ h => h)
""" % M_POST)
m("W6b_defwrapped_rsp_word", "Expected-reason: the precondition constrains the memory word at the entry RSP, inside a def-wrapped EnsuresWithin.", M_REAL + """
def Stmt (x y : BitVec 64) : Prop :=
  EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = 0) %s

theorem within (x y : BitVec 64) : Stmt x y :=
  real x y |>.mono (fun _ h => h.1) (fun _ _ _ h => h)
""" % M_POST)
m("W8_atleast_rsp_word", "Expected-reason: the precondition constrains the memory word at the entry RSP (RunsAtLeastOnCall's precondition is scanned too).", """
theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 3) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = 0) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, _⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
""")
m("W6e_pre_in_local_def", "Expected-reason: the precondition constrains the memory word at the entry RSP; the precondition is hidden in a proof-local definition inside a visible EnsuresWithin (the audit expands it).", M_REAL + """
def PreBad (s : State) : Prop := StackWritable s 0 8 ∧ s.mem.readLE (s.regs regSP).toNat 8 = 0

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] PreBad %s :=
  real x y |>.mono (fun _ h => h.1) (fun _ _ _ h => h)
""" % M_POST)

open(os.path.join(D, "amd64_W4_lower_bound_faulting_pre.lean"), "w").write("""import Janus
import Extracted

/-! Expected-reason: the lower bound is not exhibited with a returning run (a nil receiver faults at the first instruction; every call meeting the precondition faults). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem atLeast0 : RunsAtLeastOnCall (fun _ => 0) Extracted.program Extracted.entry [0#64]
    (fun s => s.mem.accessible 0 8 false = false) :=
  fun _ _ _ _ _ => rfl

namespace Witness
open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def s0 : State :=
  { regs := fun r_ => if r_ = 0 then 0#64 else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s : State => s.mem.accessible 0 8 false = false) s0 := by
  dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)
theorem atLeast0 : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    RunsAtLeast 0 (Extracted.program.withExit ret) s :=
  ⟨ret, s0, hret, setup, hpre, rfl⟩
end Witness

end Proof
""")
print(len(os.listdir(D)), "attack files")

import Extracted

/-!
# `Concat(a, b string) string` is `a + b` (arm64)

**Guarantee.** For every pair of strings `a = (ap, an)`, `b = (bp, bn)`, every list `rt` of
runtime-owned ranges, every readiness predicate `H` and **every** implementation of
`runtime.concatstring2` satisfying its contract (`RtContract … (concatstringSpec 2)`,
`Janus/Contracts/String.lean`), and every Go call state of `example.com/basic.Concat` in which
the stack-growth prologue falls through, the stack window `[SP-4176, SP+32)` is writable and
outside `rt`, both strings are readable and outside the window, and the runtime is ready for the
call `concatstring2(nil, a, b)` from Concat's frame: the call returns, obeys the ABI, and the
result `(X0, X1)` is a readable string holding exactly the bytes of `a` followed by those of `b`.

**What is assumed.** The contract (hypothesis `hc`); `concatstring2` itself (the allocation and
copies) is not executed. `Witness` shows the hypotheses are satisfiable together.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The precondition: stack, guard, the strings, readiness for the call. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4176 32 ∧ Outside (s.sp.toNat - 4176) 4208 rt ∧
    StrIn s.mem ap.toNat an.toNat ∧ StrIn s.mem bp.toNat bn.toNat ∧
    Outside ap.toNat an.toNat [(s.sp.toNat - 4176, s.sp.toNat + 32)] ∧
    Outside bp.toNat bn.toNat [(s.sp.toNat - 4176, s.sp.toNat + 32)] ∧
    H [0, ap.toNat, an.toNat, bp.toNat, bn.toNat] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ap an bp bn : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H (concatstringSpec 2)) :
    Ensures (Extracted.program.link impl) Extracted.entry [ap, an, bp, bn] (Pre rt H ap an bp bn)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat
        (strBytes s.mem ap.toNat an.toNat ++ strBytes s.mem bp.toNat bn.toNat)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hao, hbo, hH⟩
  janus_intro hs
  simp only [outside_cons, outside_nil, and_true] at hao hbo
  janus_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  all_goals assumption

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

Code at `runtime.concatstring2`'s address that meets the contract (`Sat.constCode 0 0 0`, for
the readiness `Sat.H0`: all operands empty), `Sat.rtW`, an admissible return address and the
call `Concat("", "")` from `Sat`'s witness memory: `correctness` applies (`nonvacuous`) and the
call returns the empty string (`returns`). -/

namespace Witness

open Janus.Contracts.Sat

def cAddr : Nat := Extracted.program.contractAddr "runtime.concatstring2"
def implAt : List Segment := [{ name := "model", base := cAddr, words := constCode 0 0 0 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) cAddr rtW 4096 H0 (concatstringSpec 2) := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  simp only [concatstringSpec] at ha
  simp [ha, strBytes]

def ret : Nat := wret
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0, 0] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre : Pre rtW H0 0 0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, ?_⟩,
    by simp only [rtW, outside_cons, outside_nil]; decide,
    ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, by simp only [outside_cons, outside_nil]; decide,
    by simp only [outside_cons, outside_nil]; decide, ?_⟩
  · have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Memory.accessible_mono _ hw (by decide) (by decide)
  · intro j; simp [arg, List.getD_eq_getElem?_getD]; rcases j with _ | _ | _ | _ | _ | j <;> simp

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.concatstring2")
      rt 4096 H (concatstringSpec 2) ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 0] s ∧
    Pre rt H 0 0 0 0 s :=
  ⟨implAt, rtW, H0, ret, s0, model, hret, setup, pre⟩

/-- So the guarantee is reached: `Concat("", "")` returns the empty string. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat
      (strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat ++ strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat) :=
  correctness implAt rtW H0 0 0 0 0 model ret hret s0 setup pre

end Witness

end Proof

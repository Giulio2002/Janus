import Extracted

/-!
# `FromBytes(b []byte) string` is `string(b)` (arm64)

**Guarantee.** For every slice `b = (p, n, c)`, every `rt`, every readiness predicate `H` and
**every** implementation of `runtime.slicebytetostring` satisfying its contract
(`RtContract … slicebytetostringSpec`, `Janus/Contracts/String.lean`), and every Go call state
of `example.com/basic.FromBytes` in which the stack-growth prologue falls through, the stack
window `[SP-4144, SP+24)` is writable and outside `rt`, the `n` bytes at `p` are readable and
outside the window, and the runtime is ready for the call `slicebytetostring(nil, p, n)`: the
call returns, obeys the ABI, and the result `(X0, X1)` is a readable string holding exactly the
`n` bytes of `b`.

**What is assumed.** The contract (hypothesis `hc`). `Witness` shows the hypotheses are
satisfiable together.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
namespace Proof

def Pre (rt : List (Nat × Nat)) (H : RtReady) (p n : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Outside (s.sp.toNat - 4144) 4168 rt ∧
    StrIn s.mem p.toNat n.toNat ∧ Outside p.toNat n.toNat [(s.sp.toNat - 4144, s.sp.toNat + 24)] ∧
    H [0, p.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (p n c : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring")
      rt 4096 H slicebytetostringSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, n, c] (Pre rt H p n)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (strBytes s.mem p.toNat n.toNat)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, ⟨hp1, hp2⟩, hpo, hH⟩
  janus_intro hs
  simp only [outside_cons, outside_nil, and_true] at hpo
  janus_run [false_implies, implies_true, List.not_mem_nil, forall_const] calls [hc]
  all_goals assumption
/-! ## Non-vacuity -/

namespace Witness

open Janus.Contracts.Sat

def cAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
def implAt : List Segment := [{ name := "model", base := cAddr, words := constCode 0 0 0 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) cAddr rtW 4096 H0 slicebytetostringSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, H0, arg, List.getD_eq_getElem?_getD, slicebytetostringSpec] at ha
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  simp [ha, strBytes]

def ret : Nat := wret
theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0, 0, 0] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases i with _ | _ | _ | i <;> simp [s0] at h ⊢ <;> omega⟩

theorem pre : Pre rtW H0 0 0 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, ?_⟩,
    by simp only [rtW, outside_cons, outside_nil]; decide, ⟨by decide, by simp⟩,
    by simp only [outside_cons, outside_nil]; decide, ?_⟩
  · have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
    exact Memory.accessible_mono _ hw (by decide) (by decide)
  · intro j; simp [arg, List.getD_eq_getElem?_getD]; rcases j with _ | _ | _ | j <;> simp

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.slicebytetostring")
      rt 4096 H slicebytetostringSpec ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0] s ∧ Pre rt H 0 0 s :=
  ⟨implAt, rtW, H0, ret, s0, model, hret, setup, pre⟩

/-- The witness call returns, with the conclusion of `correctness`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat
      (strBytes s0.mem (0 : BitVec 64).toNat (0 : BitVec 64).toNat) :=
  correctness implAt rtW H0 0 0 0 model ret hret s0 setup pre

end Witness

end Proof

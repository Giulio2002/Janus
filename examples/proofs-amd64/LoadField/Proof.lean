import Janus
import Extracted

/-! `example.com/basic.LoadField(c)` on amd64: a nil receiver dereference (`MOVQ 0(AX), AX` with
`AX = 0`) faults, which Go turns into a nil-pointer panic via `sigpanic`. Example 5 of
docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) :
    EnsuresGo Extracted.program Extracted.entry [0#64]
      (fun s => s.mem.accessible 0 8 false = false)
      (fun _ => goClass P)
      (fun _ _ => True)
      (fun _ v _ => v = P.err Spec.ErrKind.mem) := by
  intro ret hret s hs hna
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hrip : s.rip = BitVec.ofNat 64 Extracted.entry := hs.rip
  have hripn : s.rip.toNat = Extracted.entry := by rw [hrip, BitVec.toNat_ofNat]; rfl
  have hfetch : (Extracted.program.withExit ret).fetch s.rip.toNat = some [0x48, 0x8b, 0x00, 0xc3] := by
    rw [hripn]; rfl
  have hstep : Amd64.step [0x48, 0x8b, 0x00, 0xc3] s = .error (.outsideAllocation 0 8) := by
    rw [step_of_decode (by decide : decode [0x48, 0x8b, 0x00, 0xc3]
        = some (.mov 64 (.reg 0) (.loc (.mem ⟨some 0, none, 0, 0, false, false⟩)), 3)) s]
    simp only [exec, readSrc, readLoc, ea, eaOff, h0, Bool.false_eq_true, if_false,
      reduceCtorEq, BitVec.zero_add, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reduceDiv]
    rw [show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl, load, if_neg (by rw [hna]; decide)]
  refine GoReturns.fault (Janus.Amd64.Program.Steps.refl s) ⟨?_, ?_, [0x48, 0x8b, 0x00, 0xc3], hfetch, hstep⟩
    (goClass_nil P s (by decide)) rfl
  · rw [hripn, Janus.Amd64.Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := [0x48, 0x8b, 0x00, 0xc3]) (by rfl)
  · rw [hripn]; rfl

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The panic runtime: the model with an empty funcs table. -/
def PW : Spec.PanicRuntime := Janus.Contracts.PanicModel.P0 [] Janus.Contracts.PanicSatAmd64.RPa


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

theorem hyps : True := by decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (P : Janus.Spec.PanicRuntime) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    GoReturns (Extracted.program.withExit ret) (goClass P) s fun o =>
    match o with
    | .returned s' => ABIReturn s s' ∧ (True)
    | .panicked v s' => v = P.err Spec.ErrKind.mem
    | .goexited _ => False :=
  ⟨ret, s0, PW, hret, setup, hpre, correctness PW ret hret s0 setup hpre⟩

end Witness

end Proof

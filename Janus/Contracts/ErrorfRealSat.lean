import Janus.Contracts.ErrorfRealLive
import Janus.Contracts.ErrorfRealWitC
import Janus.Contracts.ErrorfSat

/-!
# The `fmt.errorf` live contract is satisfiable for the real format (arm64)

`ErrorfLive` for the format `"%w: have %d, want %d bytes"` of the `uint256` library, with a message of any length
(up to `B`) and any `int` operands, together with a call state that satisfies the whole precondition. The contract
is `ErrorfRealLive.errorf_live_at`: the position-independent stub of `ErrorfRealImpl`, placed here at `A0`; the call
state is the one of `ErrorfRealWitC` (`fmt.Errorf("%w: have %d, want %d bytes", ErrBad, 3, 32)`).
-/

namespace Janus.Contracts.ErrorfRealSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Errorf Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.ErrorfMem
  Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealRt Janus.Contracts.ErrorfRealLive
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfRealCode (code)
open Janus.Contracts.ErrorfSat (tErr iErr tInt iWrap)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ## A call state that satisfies the whole precondition -/

open Janus.Contracts.ErrorfRealWitC

def rstate : State := { wst [rFP, 26, rSP, 3, 3] with mem := rmem }

theorem rcall : CallOK rstate 4096 5 := by
  obtain ⟨a, b, c, d, e, f, g⟩ := wcallOK (fun i => BitVec.ofNat 64 ([rFP, 26, rSP, 3, 3].getD i 0)) 5 (by omega)
  refine ⟨a, b, c, d, e, f, ?_⟩
  have := rframe.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true
  have e' : rstate.sp.toNat = wsp := wspn
  show rmem.accessible _ _ true = true
  rw [e', this]
  have g' := g
  rw [wmem_eq, wsp_eq, wspn] at g'
  exact g'

theorem rguard : StackRoom rstate 4096 5 := by
  obtain ⟨⟨a, b, c⟩, d⟩ := wguard (fun i => BitVec.ofNat 64 ([rFP, 26, rSP, 3, 3].getD i 0)) 5 (by omega)
  refine ⟨⟨a, ?_, ?_⟩, d⟩
  · show rmem.accessible _ _ false = true
    rw [rframe.accessible]; exact b
  · have e28 : (rstate.regs 28).toNat = wg := wgn
    show rmem.readLE _ 8 + 4096 < _
    rw [rframe.readLE _ _ (by
      show Outside ((rstate.regs 28).toNat + 16) 8 [(CB, CB + 0x200), (CELL, CELL + 16)]
      rw [e28]; simp [wg, CB, CELL, outside_cons, outside_nil])]; exact c

set_option maxRecDepth 100000 in
theorem rreadsOut : ReadsOutside (errorfReads rmem rFP 26 rSP) (calleeStack rstate 4096 5) := by
  rw [rreads]
  simp only [ReadsOutside, List.mem_cons, List.not_mem_nil, or_false]
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [calleeStack, rstate, wst, wstate, wsp, rFP, rSP, rE, rTXT, rQ1, rQ2, CB, outside_cons, outside_nil]

theorem rwin : LiveSep (calleeStack rstate 4096 5) (errRt tys0) := by
  have h := wwin (fun i => BitVec.ofNat 64 ([rFP, 26, rSP, 3, 3].getD i 0)) 5 (by omega)
  intro r hr
  have h1 := h r hr
  simp only [errRt, outside_append]
  refine ⟨h1, ?_⟩
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp [rstate, wst, wstate, wsp, CELL, outside_cons, outside_nil]

theorem toy_fetched : FetchedAt (toy.link [errorfSeg A0]) A0 :=
  fetchedAt_link toy A0 (fun j _ => rfl) (fun j _ => rfl) (fun j hj => by simp [toy, A0])

theorem real_satisfiable : ∃ (R : RtInv) (tErr iErr tInt iWrap Fl Fm B : Nat) (impl : List Segment),
    ErrorfLive (toy.link impl) A0 4096 R tErr iErr tInt iWrap Fl Fm B ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.pc = BitVec.ofNat 64 A0 ∧
      CallOK s 4096 5 ∧ StackRoom s 4096 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat
        (s.regs 3).toNat (s.regs 4).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (calleeStack s 4096 5) ∧
      ReadsSafe R L (errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat, (s.regs 4).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (s.regs 28).toNat s.mem
        (calleeStack s 4096 5) :=
  ⟨errR tys0 iErr iWrap (fun _ _ => True), tErr, iErr, tInt, iWrap, 26, fmtNum, 4294967296, [errorfSeg A0],
    errorf_live_at _ A0 tys0 tysOK0 tErr tInt iErr iWrap (by decide) (by decide) (by decide) toy_fetched,
    rstate, [], 0x400, rfl, rcall, rguard, rargs, rreadsOut, rsafe,
    ⟨trivial, rinv (rstate.regs 28).toNat, by show errorfCost rmem rFP 26 rSP ≤ 0x400; rw [rcost]; decide, by simp, rwin⟩⟩

end Janus.Contracts.ErrorfRealSat

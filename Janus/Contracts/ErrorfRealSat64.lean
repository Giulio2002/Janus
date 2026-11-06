import Janus.Contracts.ErrorfRealLive64
import Janus.Contracts.ErrorfRealWitC
import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.ErrorfSat

/-!
# The `fmt.errorf` live contract is satisfiable for the real format (amd64)

The amd64 counterpart of `ErrorfRealSat`: `ErrorfLive` for `"%w: have %d, want %d bytes"` (any text, any `int` operands)
from the position-independent stub of `ErrorfRealImpl64` placed at `A0` (`ErrorfRealLive64.errorf_live_at64`), and a call
state satisfying the whole precondition (the one of `ErrorfRealWitC`, shared with arm64).
-/

namespace Janus.Contracts.ErrorfRealSat64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.Toy Janus.Contracts.LiveSat
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.ErrorfMem Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealRt
  Janus.Contracts.ErrorfRealLive64
open Janus.Contracts.AllocSatAmd64 (toy A0)
open Janus.Contracts.ErrorfSat (tErr iErr tInt iWrap)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ## A call state that satisfies the whole precondition -/

open Janus.Contracts.ErrorfRealWitC

def rstate64 : State := { LiveSatAmd64.wst [rFP, 26, rSP, 3, 3] with mem := rmem }

theorem rcall64 : CallOK64 rstate64 4096 5 := by
  obtain ⟨a, b, c, d, e⟩ := wcallOK64 [rFP, 26, rSP, 3, 3] 5 (by omega)
  have e4 : (rstate64.regs 4).toNat = LiveSat.wsp := LiveSat.wspn
  refine ⟨?_, b, c, d, ?_⟩
  · show rmem.readLE (rstate64.regs 4).toNat 8 < _
    rw [e4, rframe.readLE _ _ (by simp [LiveSat.wsp, CB, CELL, outside_cons, outside_nil])]
    have a' := a
    rw [LiveSatAmd64.wmem_eq, LiveSatAmd64.w4, LiveSat.wspn] at a'
    exact a'
  · show rmem.accessible ((rstate64.regs 4).toNat - 4096) _ true = true
    rw [e4, rframe.accessible]
    have e' := e
    rw [LiveSatAmd64.wmem_eq, LiveSatAmd64.w4, LiveSat.wspn] at e'
    exact e'

theorem rret64 : RetLow rstate64 := by
  show rmem.readLE (rstate64.regs 4).toNat 8 < 2 ^ 46
  have e4 : (rstate64.regs 4).toNat = LiveSat.wsp := LiveSat.wspn
  rw [e4, rframe.readLE _ _ (by simp [LiveSat.wsp, CB, CELL, outside_cons, outside_nil])]
  show LiveSat.wmem.readLE LiveSat.wsp 8 < 2 ^ 46
  decide

theorem rguard64 : StackRoom64 rstate64 4096 5 := by
  obtain ⟨⟨a, b, c⟩, d⟩ := wguard64 [rFP, 26, rSP, 3, 3] 5 (by omega)
  refine ⟨⟨a, ?_, ?_⟩, d⟩
  · show rmem.accessible _ _ false = true
    rw [rframe.accessible]; exact b
  · have e14 : (rstate64.regs 14).toNat = LiveSat.wg := LiveSat.wgn
    show rmem.readLE _ 8 + 4096 < _
    rw [rframe.readLE _ _ (by
      show Outside ((rstate64.regs 14).toNat + 16) 8 [(CB, CB + 0x200), (CELL, CELL + 16)]
      rw [e14]; simp [LiveSat.wg, CB, CELL, outside_cons, outside_nil])]; exact c

set_option maxRecDepth 100000 in
theorem rreadsOut64 : ReadsOutside (errorfReads rmem rFP 26 rSP) (liveWin64 rstate64 4096 5) := by
  rw [rreads]
  simp only [ReadsOutside, List.mem_cons, List.not_mem_nil, or_false]
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [liveWin64, calleeStack64, rstate64, LiveSatAmd64.wst, LiveSat.wsp, rFP, rSP, rE, rTXT, rQ1, rQ2, CB, CELL,
      outside_cons, outside_nil]

theorem rwin64 : LiveSep (liveWin64 rstate64 4096 5) (errRt tys0) := by
  have h := wwin64 [rFP, 26, rSP, 3, 3] 5 (by omega)
  intro r hr
  have h1 := h r hr
  simp only [errRt, outside_append]
  refine ⟨h1, ?_⟩
  simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl <;>
    simp [rstate64, LiveSatAmd64.wst, LiveSat.wsp, CELL, outside_cons, outside_nil]

theorem toy_fetched64 : FetchedAt64 (toy.link [errorfSeg64 A0]) A0 :=
  fetchedAt_link64 toy A0 (fun off _ => rfl) (fun off _ => rfl) (fun off ho => by
    have := Janus.Contracts.RelocAmd64.seqStarts_lt _ _ _ _ ho
    simp [toy, A0])

theorem real_satisfiable64 : ∃ (R : RtInv) (tErr iErr tInt iWrap Fl Fm B : Nat) (impl : List Janus.Amd64.Segment),
    ErrorfLive (toy.link impl) A0 4096 R tErr iErr tInt iWrap Fl Fm B ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.rip = BitVec.ofNat 64 A0 ∧
      CallOK64 s 4096 5 ∧ RetLow s ∧ StackRoom64 s 4096 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat
        (s.regs 7).toNat (s.regs 6).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (liveWin64 s 4096 5) ∧
      ReadsSafe R L (errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat, (s.regs 6).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (s.regs 14).toNat s.mem
        (liveWin64 s 4096 5) :=
  ⟨errR tys0 iErr iWrap (fun _ _ => True), tErr, iErr, tInt, iWrap, 26, fmtNum, 4294967296, [errorfSeg64 A0],
    errorf_live_at64 _ A0 tys0 tysOK0 tErr tInt iErr iWrap (by decide) (by decide) (by decide) toy_fetched64,
    rstate64, [], 0x400, rfl, rcall64, rret64, rguard64, rargs, rreadsOut64, rsafe,
    ⟨trivial, rinv (rstate64.regs 14).toNat, by show errorfCost rmem rFP 26 rSP ≤ 0x400; rw [rcost]; decide, by simp,
    rwin64⟩⟩

end Janus.Contracts.ErrorfRealSat64

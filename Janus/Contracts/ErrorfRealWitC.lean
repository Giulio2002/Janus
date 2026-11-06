import Janus.Contracts.ErrorfRealPostC
import Janus.Contracts.ErrorfRealRt
import Janus.Contracts.ErrorfSat

/-!
# The call state of the real-format `fmt.errorf` witnesses (ISA-independent memory)

One call of `fmt.errorf("%w: have %d, want %d bytes", ErrBad, 3, 32)` where `ErrBad` is an errorString with the
text `"bad length"`: the format, the `[]any`, the errorString header and text, and the two `int` words, in the
writable buffer `CB` of the witness memory (`LiveSat.wmem`).
-/

namespace Janus.Contracts.ErrorfRealWitC

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfMem
  Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealStages Janus.Contracts.ErrorfRealRt Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)
open Janus.Contracts.ErrorfSat (tErr iErr tInt iWrap ewframe)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rFP : Nat := CB
def rSP : Nat := CB + 0x20
def rE : Nat := CB + 0x60
def rTXT : Nat := CB + 0x80
def rQ1 : Nat := CB + 0xA0
def rQ2 : Nat := CB + 0xA8
def txtNum : Nat := 493273389536941829284194

def rmem : Memory :=
  (((((((((((((wmem.writeLE CELL 8 iErr).writeLE (CELL + 8) 8 iWrap).writeLE rFP 26 fmtNum).writeLE rSP 8 tErr).writeLE (rSP + 8) 8 rE).writeLE (rSP + 16) 8 tInt).writeLE
    (rSP + 24) 8 rQ1).writeLE (rSP + 32) 8 tInt).writeLE (rSP + 40) 8 rQ2).writeLE rE 8 rTXT).writeLE (rE + 8) 8 10).writeLE
    rTXT 10 txtNum).writeLE rQ1 8 3).writeLE rQ2 8 32


theorem rframe : MemFrame wmem rmem [(CB, CB + 0x200), (CELL, CELL + 16)] := by
  have hr : (CB, CB + 0x200) ∈ [(CB, CB + 0x200), (CELL, CELL + 16)] := by simp
  have hc : (CELL, CELL + 16) ∈ [(CB, CB + 0x200), (CELL, CELL + 16)] := by simp
  unfold rmem rFP rSP rE rTXT rQ1 rQ2
  refine (MemFrame.refl wmem _).writeLE _ hc (by simp [CELL]) (by simp [CELL]) |>.writeLE _ hc (by simp [CELL]) (by simp [CELL]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB]) |>.writeLE _ hr (by simp [CB]) (by simp [CB])

theorem rread_fmt : rmem.readLE rFP 26 = fmtNum := by decide

theorem rmsg : msgOf rmem rFP 26 rSP =
    strBytes rmem (rmem.readLE (rmem.readLE (rSP + 8) 8) 8) (rmem.readLE (rmem.readLE (rSP + 8) 8 + 8) 8) ++
      ([58, 32, 104, 97, 118, 101, 32] ++ decBytes (toSigned (rmem.readLE (rmem.readLE (rSP + 24) 8) 8)) ++
        [44, 32, 119, 97, 110, 116, 32] ++ decBytes (toSigned (rmem.readLE (rmem.readLE (rSP + 40) 8) 8)) ++
        [32, 98, 121, 116, 101, 115]) := msgOf_real rmem rFP 26 rSP rfl rread_fmt

theorem rvals : rmem.readLE (rSP + 8) 8 = rE ∧ rmem.readLE rE 8 = rTXT ∧ rmem.readLE (rE + 8) 8 = 10 ∧
    rmem.readLE (rSP + 24) 8 = rQ1 ∧ rmem.readLE (rSP + 40) 8 = rQ2 ∧ rmem.readLE rQ1 8 = 3 ∧ rmem.readLE rQ2 8 = 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem rmsgLen : (msgOf rmem rFP 26 rSP).length = 33 := by
  rw [rmsg]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rvals
  rw [h1, h2, h3, h4, h5, h6, h7]
  have e1 : toSigned 3 = 3 := by decide
  have e2 : toSigned 32 = 32 := by decide
  rw [e1, e2]
  have d1 : decBytes 3 = [51] := by
    unfold decBytes; rw [if_neg (by decide)]; show natBytes 3 = [51]; rw [natBytes_lt (by decide)]
  have d2 : decBytes 32 = [51, 50] := by
    unfold decBytes; rw [if_neg (by decide)]; show natBytes 32 = [51, 50]
    rw [natBytes_ge (by decide), natBytes_lt (by decide)]; rfl
  rw [d1, d2]
  simp [strBytes]

theorem rargs : ArgsOK (Env.mk tErr iErr tInt iWrap) 26 fmtNum 4294967296 rmem rFP 26 rSP 3 3 := by
  have hs := segsOf_real rmem rFP 26 rfl rread_fmt
  have hn : nDec (segsOf rmem rFP 26) = 2 := by rw [hs]; decide
  have hfm := fmt_strBytes rmem rFP rread_fmt
  refine ⟨rfl, rread_fmt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfm, fmt_segs]; rfl
  · rw [hn]
  · decide
  · unfold Readable; decide
  · unfold Readable; decide
  · decide
  · decide
  · unfold Readable; decide
  · unfold Readable; decide
  · rw [hn]; intro j hj
    refine ⟨?_, ?_, ?_⟩
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> (unfold Readable; decide)
  · rw [rmsgLen]; decide
  · decide

theorem rcost : errorfCost rmem rFP 26 rSP = 114 := by
  unfold errorfCost; rw [rmsgLen]; decide

theorem rreads : errorfReads rmem rFP 26 rSP = [(rFP, 26), (rSP, 48), (rE, 16), (rTXT, 10), (rQ1, 8), (rQ2, 8)] := by
  have hs := segsOf_real rmem rFP 26 rfl rread_fmt
  have hn : nDec (segsOf rmem rFP 26) = 2 := by rw [hs]; decide
  unfold errorfReads
  rw [hn]
  decide

theorem rsafe : ReadsSafe (errR tys0 iErr iWrap (fun _ _ => True)) [] (errorfReads rmem rFP 26 rSP) := by
  rw [rreads]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inr (Or.inl (by
    simp only [errR, errRt, toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE,
      BUMP, WBUF, tyA, tyB, tyC, rFP, rSP, rE, rTXT, rQ1, rQ2, CB, CELL]
    omega))

theorem view_writeLE_CB (m : Memory) (a n v : Nat) (h1 : CB ≤ a) (h2 : a + n ≤ CB + 0x200) :
    view (toyRt tys0) [] (m.writeLE a n v) = view (toyRt tys0) [] m := by
  apply view_writeLE_out
  simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE, BUMP, WBUF,
    tyA, tyB, tyC, CB] at h1 h2 ⊢
  omega

theorem view_writeLE_cell (m : Memory) (a n v : Nat) (h1 : CELL ≤ a) (h2 : a + n ≤ CELL + 16) :
    view (toyRt tys0) [] (m.writeLE a n v) = view (toyRt tys0) [] m := by
  apply view_writeLE_out
  simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE, BUMP, WBUF,
    tyA, tyB, tyC, CELL] at h1 h2 ⊢
  omega

theorem rinv (g : Nat) : errInv tys0 iErr iWrap 0x400 [] g (view (errRt tys0) [] rmem) := by
  have h := wmem_inv g
  have e : view (toyRt tys0) [] rmem = view (toyRt tys0) [] wmem := by
    unfold rmem rFP rSP rE rTXT rQ1 rQ2
    simp (disch := (simp only [CB, CELL]; omega)) only [view_writeLE_CB, view_writeLE_cell]
  refine ⟨by rw [view_toy_err, e]; exact h, ?_, ?_, ?_⟩
  · rw [readLE_view (inRanges_cell tys0 (Nat.le_refl _) (by omega)) (by simp [outside_nil])]; decide
  · rw [readLE_view (inRanges_cell tys0 (by omega) (by omega)) (by simp [outside_nil])]; decide
  · rw [view_accessible]; decide

end Janus.Contracts.ErrorfRealWitC

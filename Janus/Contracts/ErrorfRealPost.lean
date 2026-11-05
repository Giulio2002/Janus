import Janus.Contracts.ErrorfRealFinal
import Janus.Contracts.ErrorfSat
import Janus.Contracts.ErrorfRealStageDefs

/-!
# The postcondition of `fmt.errorf` for the memory the real-format stub leaves (ISA-independent)

`real_errorfPost`: `ErrorfPost` holds for `finalMem` (the object, the message, the frame of the live set
and the toy runtime's invariant), given the facts the stubs establish.
-/

namespace Janus.Contracts.ErrorfRealPost

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfMem
  Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealStages Janus.Contracts.ErrorfRealFinal Janus.Contracts.Toy
  Janus.Contracts.LiveSat
open Janus.Contracts.ErrorfSat (tErr iErr tInt iWrap)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem real_errorfPost (ok : Nat → List Nat → Prop) (m0 : Memory) (fp fl sp : Nat) (win L : List (Nat × Nat))
    (b g iw d sp0 l1 n1 l2 n2 a1 a2 p Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + atot Lm ≤ 536870912) (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) (he : e < 2 ^ 64)
    (hmsgOf : msgOf m0 fp fl sp = msgList (strBytes m0 tp tl) n1 n2 a1 a2)
    (hop : operandD m0 sp 0 = e) (hiw : iw = 0x4444) (hd : d = p)
    (hinv' : toyInv tys0 (b - (2 * Lm + 48)) (L ++ [(p, p + (2 * Lm + 48))]) g
      (view (toyRt tys0) (L ++ [(p, p + (2 * Lm + 48))]) (m0.writeLE 4194304 8 (p + atot Lm))))
    (hap : ApartAll p (2 * Lm + 48) L)
    (hacc' : (m0.writeLE 4194304 8 (p + atot Lm)).accessible p (2 * Lm + 48) true = true)
    (hWs : LiveSep win (toyRt tys0)) (hLp : ∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p)
    (hrtW : ∀ a, inRs (toyRt tys0) a = true → a < sp0 - 4096 ∨ sp0 - 8 ≤ a) :
    ErrorfPost (Env.mk tErr iErr tInt iWrap) (toyR tys0 ok) m0 fp fl sp win L b g iw d
      (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p (atot Lm) Lm e tp tl) := by
  subst hiw
  subst d
  have hTl : (strBytes m0 tp tl).length = tl := by simp [strBytes]
  have hmsgLen : (msgOf m0 fp fl sp).length = Lm := by
    rw [hmsgOf, msgList_length _ tl l1 l2 n1 n2 a1 a2 hTl hn1 hn2 hlen1 hlen2]; omega
  have hl1p : 1 ≤ l1 := by rw [← hlen1]; exact natBytes_length_pos a1
  have hl2p : 1 ≤ l2 := by rw [← hlen2]; exact natBytes_length_pos a2
  have hA : 2 * Lm + 48 ≤ atot Lm := by unfold atot; omega
  have hpA' : p + atot Lm ≤ 536870912 := hpA
  have hfields := final_fields m0 sp0 l1 n1 l2 n2 a1 a2 p (atot Lm) Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm
    hscrB hscrH hT he
  have hmsg := final_msg m0 sp0 l1 n1 l2 n2 a1 a2 p (atot Lm) Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm
    hscrB hscrH hT
  have hview := final_view (toyRt tys0) L m0 sp0 l1 n1 l2 n2 a1 a2 p (atot Lm) Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA
    hA hLm hscrB hscrH hT hrtW
  have hcost : errorfCost m0 fp fl sp = 2 * Lm + 48 := by
    unfold errorfCost; rw [hmsgLen, if_neg (by omega)]; simp only [wrapBytes]; omega
  have hrt : InRanges p 32 (toyRt tys0) := inRanges_heap (by simp [HEAP]; omega) (by simp [HEND, HEAP, HSIZE]; omega)
  have hwin : ∀ n, n ≤ 2 * Lm + 48 → InRanges p n (toyRt tys0) := fun n hn =>
    inRanges_heap (n := n) (by simp [HEAP]; omega) (by simp [HEND, HEAP, HSIZE]; omega)
  unfold ErrorfPost
  rw [hcost]
  refine ⟨by decide, by simp only [wrapBytes]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finalMem_accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE] at hacc'
    simp only [wrapBytes]
    exact Memory.accessible_mono _ hacc' (Nat.le_refl _) (by omega)
  · rw [hmsgLen]; exact hfields.2.1
  · rw [hfields.1, hmsgLen, hmsg, hmsgOf]
  · rw [hfields.1, hmsgLen]
    refine ⟨by omega, fun h => ?_⟩
    rw [finalMem_accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE] at hacc'
    exact Memory.accessible_sub _ hacc' (Or.inl rfl) (by omega) (by omega)
  · exact hfields.2.2.1
  · rw [hop]; exact hfields.2.2.2
  · simp only [freshFrom_cons, freshFrom_nil, and_true, Nat.add_sub_cancel_left]
    intro r hr
    exact Apart.mono (hap r hr) (by simp only [wrapBytes]; omega) (Nat.le_refl _)
  · exact hrt
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have hA32 := apart_win hrt hWs
    exact outside_of_forall fun r' hr' => by
      have := hA32 r' hr'; unfold Apart at this; simp only [Nat.add_sub_cancel_left, wrapBytes]; omega
  · rw [hfields.1, hmsgLen]
    intro r hr
    simp only [range0, if_neg (show Lm ≠ 0 by omega), List.mem_singleton] at hr
    subst hr
    have hA32 := apart_win (hwin (32 + Lm) (by omega)) hWs
    exact outside_of_forall fun r' hr' => by
      have := hA32 r' hr'; unfold Apart at this; simp only [Nat.add_sub_cancel_left]; omega
  · rw [hfields.1, hmsgLen]
    show toyInv tys0 (b - (2 * Lm + 48)) (liveAfter L p Lm) g (view (toyRt tys0) (liveAfter L p Lm) _)
    rw [hview]
    have hpn : (m0.writeLE 4194304 8 (p + atot Lm)).readLE 4194304 8 = p + atot Lm := by
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      apply Nat.mod_eq_of_lt
      have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [this]; omega
    refine toyInv_swap (p + atot Lm) hpn ?_ ?_ tysOK0 hinv'
    · intro r hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have := hLp r hr; omega
      · simp [HEAP]; omega
    · intro r hr
      simp only [liveAfter, List.mem_append, List.mem_cons, range0] at hr
      by_cases h0 : Lm = 0
      · omega
      · simp only [if_neg h0, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with hr | rfl | rfl
        · have := hLp r hr; omega
        · simp [HEAP]; omega
        · simp [HEAP]; omega

end Janus.Contracts.ErrorfRealPost

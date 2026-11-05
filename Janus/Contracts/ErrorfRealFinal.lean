import Janus.Contracts.ErrorfRealStageDefs
import Janus.Contracts.ErrorfRealFmt

/-!
# The memory the real-format `fmt.errorf` stub leaves (ISA-independent)

The stub (arm64 `ErrorfRealSat`, amd64 `ErrorfRealSatAmd64`) turns the two operands into decimal strings in
stack scratch, allocates, writes the object, and copies text, literals and digits into the message block.
`finalMem` is the memory it leaves, as a chain of stores; the lemmas of this file read the message and the
object off it.
-/

namespace Janus.Contracts.ErrorfRealFinal

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.ErrorfMem
  Janus.Contracts.ErrorfRealFmt Janus.Contracts.ErrorfRealStages

/-- The scratch memory after both decimal conversions (before the allocation). -/
def scratchMem (m0 : Memory) (sp0 l1 n1 l2 a1 a2 : Nat) : Memory :=
  putBytes ((putBytes m0 (sp0 - 16 - l1) (natBytes a1)).writeLE (sp0 - 16 - l1 - 1) 1 (48 - 3 * n1))
    (sp0 - 48 - l2) (natBytes a2)

/-- The memory after the allocation part (`allocMem` on the scratch memory). -/
def midMem (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e : Nat) : Memory :=
  allocMem (scratchMem m0 sp0 l1 n1 l2 a1 a2) (sp0 - 48 - l2) n2 p A Lm e

/-- The memory the stub leaves. -/
def finalMem (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) : Memory :=
  let M := midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e
  let m3 := putBytes M (p + 32) (strBytes M tp tl)
  let d1 := p + 32 + tl
  let st1 := sp0 - 16 - l1 - n1
  let len1 := sp0 - 16 - st1
  let M1 := putBytes m3 d1 [58, 32, 104, 97, 118, 101, 32]
  let m4 := putBytes M1 (d1 + 7) (strBytes M1 st1 len1)
  let d2 := d1 + 7 + len1
  let st2 := sp0 - 48 - l2 - n2
  let len2 := sp0 - 48 - st2
  let M2 := putBytes m4 d2 [44, 32, 119, 97, 110, 116, 32]
  let m5 := putBytes M2 (d2 + 7) (strBytes M2 st2 len2)
  putBytes m5 (d2 + 7 + len2) [32, 98, 121, 116, 101, 115]

set_option maxRecDepth 100000

/-- Where the text lies, as the stub needs it: outside the `BUMP` cell, outside the heap block it writes,
outside the scratch window. -/
def TextOK (sp0 p tp tl : Nat) : Prop :=
  tl = 0 ∨ ((tp + tl ≤ 4194304 ∨ 4194312 ≤ tp) ∧ (tp + tl ≤ p ∨ 536870912 ≤ tp) ∧
    (tp + tl ≤ sp0 - 4096 ∨ sp0 - 8 ≤ tp))

theorem mid_text (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + 32 ≤ 536870912) (hT : TextOK sp0 p tp tl) :
    strBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) tp tl = strBytes m0 tp tl := by
  by_cases h0 : tl = 0
  · subst h0; simp [strBytes]
  have hT' : (tp + tl ≤ 4194304 ∨ 4194312 ≤ tp) ∧ (tp + tl ≤ p ∨ 536870912 ≤ tp) ∧
      (tp + tl ≤ sp0 - 4096 ∨ sp0 - 8 ≤ tp) := by rcases hT with h | h; exact absurd h h0; exact h
  unfold midMem allocMem scratchMem
  simp (disch := omega) only [strBytes_writeLE_out, strBytes_putBytes_out, hlen1, hlen2]

theorem mid_s1 (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + 32 ≤ 536870912) (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0)
    (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0) :
    strBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (sp0 - 16 - l1 - n1) (sp0 - 16 - (sp0 - 16 - l1 - n1)) =
      (if n1 = 1 then [45] else []) ++ natBytes a1 := by
  have hb := natBytes_lt256 a1
  have hl1p : 1 ≤ l1 := by rw [← hlen1]; exact natBytes_length_pos a1
  unfold midMem allocMem scratchMem
  simp (disch := omega) only [strBytes_writeLE_out, strBytes_putBytes_out, hlen1, hlen2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
  · have e1 : sp0 - 16 - (sp0 - 16 - l1 - 0) = l1 := by omega
    rw [e1, show sp0 - 16 - l1 - 0 = sp0 - 16 - l1 by omega]
    simp (disch := omega) only [strBytes_writeLE_out]
    have := strBytes_putBytes m0 (sp0 - 16 - l1) (natBytes a1) hb
    rw [hlen1] at this
    simpa using this
  · have e1 : sp0 - 16 - (sp0 - 16 - l1 - 1) = l1 + 1 := by omega
    rw [e1, strBytes_succ]
    have e2 : sp0 - 16 - l1 - 1 + 1 = sp0 - 16 - l1 := by omega
    rw [e2]
    simp (disch := omega) only [strBytes_writeLE_out]
    have := strBytes_putBytes m0 (sp0 - 16 - l1) (natBytes a1) hb
    rw [hlen1] at this
    rw [this, Janus.Arm64.Memory.bytes_writeLE (m := (putBytes m0 (sp0 - 16 - l1) (natBytes a1)))]
    simp

theorem mid_s2 (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + 32 ≤ 536870912) (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0)
    (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0) :
    strBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (sp0 - 48 - l2 - n2) (sp0 - 48 - (sp0 - 48 - l2 - n2)) =
      (if n2 = 1 then [45] else []) ++ natBytes a2 := by
  have hb := natBytes_lt256 a2
  have hl2p : 1 ≤ l2 := by rw [← hlen2]; exact natBytes_length_pos a2
  unfold midMem allocMem scratchMem
  simp (disch := omega) only [strBytes_writeLE_out]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl
  · have e1 : sp0 - 48 - (sp0 - 48 - l2 - 0) = l2 := by omega
    rw [e1, show sp0 - 48 - l2 - 0 = sp0 - 48 - l2 by omega]
    simp (disch := omega) only [strBytes_writeLE_out]
    have := strBytes_putBytes ((putBytes m0 (sp0 - 16 - l1) (natBytes a1)).writeLE (sp0 - 16 - l1 - 1) 1 (48 - 3 * n1))
      (sp0 - 48 - l2) (natBytes a2) hb
    rw [hlen2] at this
    simpa using this
  · have e1 : sp0 - 48 - (sp0 - 48 - l2 - 1) = l2 + 1 := by omega
    rw [e1, strBytes_succ]
    have e2 : sp0 - 48 - l2 - 1 + 1 = sp0 - 48 - l2 := by omega
    rw [e2]
    simp (disch := omega) only [strBytes_writeLE_out]
    have := strBytes_putBytes ((putBytes m0 (sp0 - 16 - l1) (natBytes a1)).writeLE (sp0 - 16 - l1 - 1) 1 (48 - 3 * n1))
      (sp0 - 48 - l2) (natBytes a2) hb
    rw [hlen2] at this
    rw [this, Janus.Arm64.Memory.bytes_writeLE (m := (putBytes ((putBytes m0 (sp0 - 16 - l1) (natBytes a1)).writeLE (sp0 - 16 - l1 - 1) 1 (48 - 3 * n1)) (sp0 - 48 - l2) (natBytes a2)))]
    simp

/-- The message the stub builds: the text, `": have "`, number 1, `", want "`, number 2, `" bytes"`. -/
def msgList (T : List Nat) (n1 n2 a1 a2 : Nat) : List Nat :=
  T ++ [58, 32, 104, 97, 118, 101, 32] ++ ((if n1 = 1 then [45] else []) ++ natBytes a1) ++
    [44, 32, 119, 97, 110, 116, 32] ++ ((if n2 = 1 then [45] else []) ++ natBytes a2) ++ [32, 98, 121, 116, 101, 115]

theorem final_eq (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + A ≤ 536870912) (hA : 2 * Lm + 48 ≤ A) (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) :
    finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl =
      putBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (p + 32) (msgList (strBytes m0 tp tl) n1 n2 a1 a2) := by
  have hpA' : p + 32 ≤ 536870912 := by omega
  have hl1p : 1 ≤ l1 := by rw [← hlen1]; exact natBytes_length_pos a1
  have hl2p : 1 ≤ l2 := by rw [← hlen2]; exact natBytes_length_pos a2
  have hTx := mid_text m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA' hT
  have hS1 := mid_s1 m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA' hscrB hscrH
  have hS2 := mid_s2 m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA' hscrB hscrH
  have hTlen : (strBytes m0 tp tl).length = tl := by simp [strBytes]
  have hD1len : ((if n1 = 1 then [45] else []) ++ natBytes a1).length = sp0 - 16 - (sp0 - 16 - l1 - n1) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl <;> simp [hlen1] <;> omega
  have hD2len : ((if n2 = 1 then [45] else []) ++ natBytes a2).length = sp0 - 48 - (sp0 - 48 - l2 - n2) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl <;> simp [hlen2] <;> omega
  simp only [finalMem]
  rw [hTx]
  have hM1 : strBytes (putBytes (putBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (p + 32) (strBytes m0 tp tl))
      (p + 32 + tl) [58, 32, 104, 97, 118, 101, 32]) (sp0 - 16 - l1 - n1) (sp0 - 16 - (sp0 - 16 - l1 - n1)) =
      (if n1 = 1 then [45] else []) ++ natBytes a1 := by
    rw [← hS1]
    simp (disch := (simp only [List.length_cons, List.length_nil, hTlen]; omega)) only [strBytes_putBytes_out]
  rw [hM1]
  have hM2 : strBytes (putBytes (putBytes (putBytes (putBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (p + 32)
      (strBytes m0 tp tl)) (p + 32 + tl) [58, 32, 104, 97, 118, 101, 32]) (p + 32 + tl + 7)
      ((if n1 = 1 then [45] else []) ++ natBytes a1)) (p + 32 + tl + 7 + (sp0 - 16 - (sp0 - 16 - l1 - n1)))
      [44, 32, 119, 97, 110, 116, 32]) (sp0 - 48 - l2 - n2) (sp0 - 48 - (sp0 - 48 - l2 - n2)) =
      (if n2 = 1 then [45] else []) ++ natBytes a2 := by
    rw [← hS2]
    simp (disch := (simp only [List.length_cons, List.length_nil, hTlen, hD1len]; omega)) only [strBytes_putBytes_out]
  rw [hM2]
  unfold msgList
  generalize midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e = M at *
  generalize strBytes m0 tp tl = T at *
  generalize (if n1 = 1 then [45] else []) ++ natBytes a1 = D1 at *
  generalize (if n2 = 1 then [45] else []) ++ natBytes a2 = D2 at *
  have e1 : p + 32 + tl = p + 32 + T.length := by rw [hTlen]
  have e2 : p + 32 + T.length + 7 = p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32]).length := by simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have e3 : p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32]).length + (sp0 - 16 - (sp0 - 16 - l1 - n1)) =
      p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32] ++ D1).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hD1len]; omega
  have e4 : p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32] ++ D1).length + 7 =
      p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32] ++ D1 ++ [44, 32, 119, 97, 110, 116, 32]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have e5 : p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32] ++ D1 ++ [44, 32, 119, 97, 110, 116, 32]).length +
      (sp0 - 48 - (sp0 - 48 - l2 - n2)) =
      p + 32 + (T ++ [58, 32, 104, 97, 118, 101, 32] ++ D1 ++ [44, 32, 119, 97, 110, 116, 32] ++ D2).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hD2len]; omega
  rw [e1, ← putBytes_append, e2, ← putBytes_append, e3, ← putBytes_append, e4, ← putBytes_append,
    e5, ← putBytes_append]

/-- The live set after the call: the caller's `L`, the `wrapError` object and the message bytes. -/
def liveAfter (L : List (Nat × Nat)) (p Lm : Nat) : List (Nat × Nat) := L ++ ((p, p + 32) :: range0 (p + 32) Lm)

theorem final_view (rt L : List (Nat × Nat)) (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat)
    (hsp : 4096 ≤ sp0) (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + A ≤ 536870912) (hA : 2 * Lm + 48 ≤ A)
    (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) (hrt : ∀ a, inRs rt a = true → a < sp0 - 4096 ∨ sp0 - 8 ≤ a) :
    view rt (liveAfter L p Lm) (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl) =
      view rt (liveAfter L p Lm) (m0.writeLE 4194304 8 (p + A)) := by
  rw [final_eq m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm hscrB hscrH hT]
  unfold view
  congr 1
  · funext a
    by_cases h : (inRs rt a && !inRs (liveAfter L p Lm) a) = true
    · rw [if_pos h, if_pos h]
      have hr : inRs rt a = true := by simp only [Bool.and_eq_true] at h; exact h.1
      have hl : inRs (liveAfter L p Lm) a = false := by simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2
      have hw := hrt a hr
      have hobj : ¬ (p ≤ a ∧ a < p + 32) := fun hh =>
        absurd hl (by rw [Bool.not_eq_false]; exact inRs_of_inRanges (a := p) (n := 32) ⟨(p, p + 32), by simp [liveAfter], Nat.le_refl _, Nat.le_refl _⟩ hh.1 (by omega))
      have hmsg : ¬ (p + 32 ≤ a ∧ a < p + 32 + Lm) := fun hh =>
        absurd hl (by
          rw [Bool.not_eq_false]
          exact inRs_of_inRanges (a := p + 32) (n := Lm) ⟨(p + 32, p + 32 + Lm), by simp [liveAfter, range0]; omega, Nat.le_refl _, Nat.le_refl _⟩ hh.1 hh.2)
      unfold midMem allocMem scratchMem
      have hLm' : (msgList (strBytes m0 tp tl) n1 n2 a1 a2).length = Lm := by
        unfold msgList
        simp only [List.length_append, List.length_cons, List.length_nil, hlen1, hlen2]
        have : (strBytes m0 tp tl).length = tl := by simp [strBytes]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl <;> simp <;> omega
      rw [putBytes_bytes_out _ _ _ _ (by rw [hLm']; omega)]
      by_cases hB : 4194304 ≤ a ∧ a < 4194312
      · have hB' : 4194304 ≤ a ∧ a < 4194304 + 8 := hB
        simp (disch := omega) only [Janus.Arm64.Memory.bytes_writeLE_outside, putBytes_bytes_out, hlen1, hlen2]
        rw [Janus.Arm64.Memory.bytes_writeLE (m := _), Janus.Arm64.Memory.bytes_writeLE (m := m0), if_pos hB', if_pos hB']
      · simp (disch := omega) only [Janus.Arm64.Memory.bytes_writeLE_outside, putBytes_bytes_out, hlen1, hlen2]
    · rw [if_neg h, if_neg h]
  · simp [midMem, allocMem, scratchMem]

theorem final_fields (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + A ≤ 536870912) (hA : 2 * Lm + 48 ≤ A) (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) (he : e < 2 ^ 64) :
    (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl).readLE p 8 = p + 32 ∧
    (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl).readLE (p + 8) 8 = Lm ∧
    (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl).readLE (p + 16) 8 = 8738 ∧
    (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl).readLE (p + 24) 8 = e := by
  have hLm' : (msgList (strBytes m0 tp tl) n1 n2 a1 a2).length = Lm := by
    unfold msgList
    simp only [List.length_append, List.length_cons, List.length_nil, hlen1, hlen2]
    have : (strBytes m0 tp tl).length = tl := by simp [strBytes]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl <;> simp <;> omega
  have hF := final_eq m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm hscrB hscrH hT
  have hmod : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hF] <;>
    rw [readLE_putBytes_out _ _ _ _ _ (by rw [hLm']; omega)] <;> unfold midMem allocMem <;>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, hmod]
  all_goals first | omega | skip

theorem lit_lt256 (l : List Nat) (h : ∀ b ∈ l, b < 256) : ∀ b ∈ l, b < 256 := h

theorem msgList_lt256 (T : List Nat) (hT : ∀ b ∈ T, b < 256) (n1 n2 a1 a2 : Nat) : ∀ b ∈ msgList T n1 n2 a1 a2, b < 256 := by
  have h1 := natBytes_lt256 a1
  have h2 := natBytes_lt256 a2
  have hI1 : ∀ c ∈ (if n1 = 1 then [45] else ([] : List Nat)) ++ natBytes a1, c < 256 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · split at hc
      · simp at hc; omega
      · simp at hc
    · exact h1 c hc
  have hI2 : ∀ c ∈ (if n2 = 1 then [45] else ([] : List Nat)) ++ natBytes a2, c < 256 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · split at hc
      · simp at hc; omega
      · simp at hc
    · exact h2 c hc
  have hL1 : ∀ c ∈ ([58, 32, 104, 97, 118, 101, 32] : List Nat), c < 256 := by decide
  have hL2 : ∀ c ∈ ([44, 32, 119, 97, 110, 116, 32] : List Nat), c < 256 := by decide
  have hL3 : ∀ c ∈ ([32, 98, 121, 116, 101, 115] : List Nat), c < 256 := by decide
  intro b hb
  unfold msgList at hb
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact hT b hb
          · exact hL1 b hb
        · exact hI1 b hb
      · exact hL2 b hb
    · exact hI2 b hb
  · exact hL3 b hb

theorem strBytes_lt256 (m : Memory) (p n : Nat) : ∀ b ∈ strBytes m p n, b < 256 := by
  intro b hb
  simp only [strBytes, List.mem_map, List.mem_range] at hb
  obtain ⟨i, -, rfl⟩ := hb
  have := (m.bytes (p + i)).isLt
  omega

theorem final_msg (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + A ≤ 536870912) (hA : 2 * Lm + 48 ≤ A) (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) :
    strBytes (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl) (p + 32) Lm =
      msgList (strBytes m0 tp tl) n1 n2 a1 a2 := by
  have hLm' : (msgList (strBytes m0 tp tl) n1 n2 a1 a2).length = Lm := by
    unfold msgList
    simp only [List.length_append, List.length_cons, List.length_nil, hlen1, hlen2]
    have : (strBytes m0 tp tl).length = tl := by simp [strBytes]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl <;> simp <;> omega
  rw [final_eq m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm hscrB hscrH hT]
  have := strBytes_putBytes (midMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e) (p + 32)
    (msgList (strBytes m0 tp tl) n1 n2 a1 a2) (msgList_lt256 _ (strBytes_lt256 m0 tp tl) n1 n2 a1 a2)
  rw [hLm'] at this
  exact this

theorem final_frame (m0 : Memory) (sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl : Nat) (hsp : 4096 ≤ sp0)
    (hl1 : l1 ≤ 19) (hl2 : l2 ≤ 19) (hn1 : n1 ≤ 1) (hn2 : n2 ≤ 1)
    (hlen1 : (natBytes a1).length = l1) (hlen2 : (natBytes a2).length = l2)
    (hp : 268435456 ≤ p) (hpA : p + A ≤ 536870912) (hA : 2 * Lm + 48 ≤ A) (hLm : Lm = tl + (l1 + n1) + (l2 + n2) + 20)
    (hscrB : sp0 ≤ 4194304 ∨ 4194312 + 4096 ≤ sp0) (hscrH : sp0 ≤ 268435456 ∨ 536870912 + 4096 ≤ sp0)
    (hT : TextOK sp0 p tp tl) :
    MemFrame m0 (finalMem m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl)
      [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)] := by
  have hLm' : (msgList (strBytes m0 tp tl) n1 n2 a1 a2).length = Lm := by
    unfold msgList
    simp only [List.length_append, List.length_cons, List.length_nil, hlen1, hlen2]
    have : (strBytes m0 tp tl).length = tl := by simp [strBytes]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn2 with rfl | rfl <;> simp <;> omega
  rw [final_eq m0 sp0 l1 n1 l2 n2 a1 a2 p A Lm e tp tl hsp hl1 hl2 hn1 hn2 hlen1 hlen2 hp hpA hA hLm hscrB hscrH hT]
  have hl1p : 1 ≤ l1 := by rw [← hlen1]; exact natBytes_length_pos a1
  have hl2p : 1 ≤ l2 := by rw [← hlen2]; exact natBytes_length_pos a2
  have hs : ∀ a n, Outside a n [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)] →
      Outside a n [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)] ∧
      Outside a n [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)] := fun a n h => ⟨h, h⟩
  have f0 : MemFrame m0 m0 [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)] := MemFrame.refl _ _
  have f1 := f0.trans (putBytes_frame m0 (rs := [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)]) (sp0 - 16 - l1) (natBytes a1)
    (Or.inr ⟨(sp0 - 4096, sp0 - 8), by simp, by omega, by omega⟩)) hs
  have f2 := f1.writeLE_inRanges (a := sp0 - 16 - l1 - 1) (k := 1) (48 - 3 * n1) ⟨(sp0 - 4096, sp0 - 8), by simp, by omega, by omega⟩
  have f3 := f2.trans (putBytes_frame _ (rs := [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)]) (sp0 - 48 - l2) (natBytes a2)
    (Or.inr ⟨(sp0 - 4096, sp0 - 8), by simp, by omega, by omega⟩)) hs
  have f4 := f3.writeLE_inRanges (a := sp0 - 48 - l2 - 1) (k := 1) (48 - 3 * n2) ⟨(sp0 - 4096, sp0 - 8), by simp, by omega, by omega⟩
  have f5 := f4.writeLE_inRanges (a := 4194304) (k := 8) (p + A) ⟨(4194304, 4194312), by simp, by omega, by omega⟩
  have f6 := f5.writeLE_inRanges (a := p) (k := 8) (p + 32) ⟨(p, p + A), by simp, by omega, by omega⟩
  have f7 := f6.writeLE_inRanges (a := p + 8) (k := 8) Lm ⟨(p, p + A), by simp, by omega, by omega⟩
  have f8 := f7.writeLE_inRanges (a := p + 16) (k := 8) 8738 ⟨(p, p + A), by simp, by omega, by omega⟩
  have f9 := f8.writeLE_inRanges (a := p + 24) (k := 8) e ⟨(p, p + A), by simp, by omega, by omega⟩
  unfold midMem allocMem scratchMem
  exact f9.trans (putBytes_frame _ (rs := [(sp0 - 4096, sp0 - 8), (4194304, 4194312), (p, p + A)]) (p + 32)
    (msgList (strBytes m0 tp tl) n1 n2 a1 a2) (by
      by_cases h : msgList (strBytes m0 tp tl) n1 n2 a1 a2 = []
      · exact Or.inl h
      · exact Or.inr ⟨(p, p + A), by simp, by omega, by rw [hLm']; omega⟩)) hs

end Janus.Contracts.ErrorfRealFinal

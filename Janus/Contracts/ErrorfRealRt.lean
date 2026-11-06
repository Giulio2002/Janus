import Janus.Contracts.LiveToy

/-!
# The runtime of the real-format `fmt.errorf` witnesses (ISA-independent)

`fmt.errorf` needs two machine constants that are *addresses in the binary*: the itab of `*errors.errorString` as an
`error` (stored in the `err` field of the `wrapError`) and the itab of `*fmt.wrapError` (the result's itab word). A stub
whose code embeds them would have to be re-proven for every consumer. So the witness runtime keeps them where a runtime
keeps its own data, in two words of **runtime-owned memory**: the cell `CELL` (`iErr` at `CELL`, `iWrap` at `CELL + 8`),
readable and writable, part of `R.rt` and fixed by the runtime invariant. The stub loads them (`ldr`), so the same words
of code serve every consumer, wherever the program places them (`RelocArm64`).

`errR tys iE iW ok` is the toy bump-allocator runtime `toyR tys ok` with that cell. Nothing is trusted: the invariant is an
ordinary conjunction (the toy's, on the toy's own part of the view, and the cell), and the kernel checks everything built
on it. The cell holds the constants that the audit pins to the extraction (`iErr`, `iWrap` of `ErrorfLive`).
-/

namespace Janus.Contracts.ErrorfRealRt

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy

/-- The constants cell: `iErr` at `CELL`, `iWrap` at `CELL + 8` (inside the page of the bump cell, after the barrier buffer). -/
def CELL : Nat := 0x400180

def errRt (tys : Tys) : List (Nat × Nat) := toyRt tys ++ [(CELL, CELL + 16)]

/-- The toy's invariant on the toy's part of the view, and the cell. -/
def errInv (tys : Tys) (iE iW : Nat) (b : Nat) (L : List (Nat × Nat)) (g : Nat) (v : Memory) : Prop :=
  toyInv tys b L g (view (toyRt tys) [] v) ∧ v.readLE CELL 8 = iE ∧ v.readLE (CELL + 8) 8 = iW ∧
    v.accessible CELL 16 true = true

theorem inRanges_cell (tys : Tys) {a n : Nat} (h1 : CELL ≤ a) (h2 : a + n ≤ CELL + 16) : InRanges a n (errRt tys) :=
  ⟨(CELL, CELL + 16), by simp [errRt], h1, h2⟩

theorem inRs_toy_err (tys : Tys) (a : Nat) (h : inRs (toyRt tys) a = true) : inRs (errRt tys) a = true := by
  unfold inRs errRt at *
  rw [List.any_append]; simp [h]

/-- The toy's part of an error-runtime view is the toy's view. -/
theorem view_toy_err (tys : Tys) (L : List (Nat × Nat)) (m : Memory) :
    view (toyRt tys) [] (view (errRt tys) L m) = view (toyRt tys) L m := by
  simp only [view, Memory.mk.injEq, and_true]
  funext a
  by_cases h : inRs (toyRt tys) a = true
  · have e : inRs ([] : List (Nat × Nat)) a = false := rfl
    simp only [h, inRs_toy_err tys a h, e, Bool.not_false, Bool.and_true, Bool.true_and, if_true]
  · have e : inRs ([] : List (Nat × Nat)) a = false := rfl
    have h' : inRs (toyRt tys) a = false := by simpa using h
    simp [h', e]

theorem errInv.ext (tys : Tys) (iE iW : Nat) (b : Nat) (L : List (Nat × Nat)) (g : Nat) (v v' : Memory)
    (hb : ∀ a, v'.bytes a = v.bytes a) (ha : ∀ a n w, v'.accessible a n w = v.accessible a n w)
    (h : errInv tys iE iW b L g v) : errInv tys iE iW b L g v' := by
  have hr : ∀ a n, v'.readLE a n = v.readLE a n := fun a n => Memory.readLE_congr fun i _ => hb _
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨toyInv.ext tys b L g _ _ ?_ ?_ h1, by rw [hr]; exact h2, by rw [hr]; exact h3, by rw [ha]; exact h4⟩
  · intro a; simp only [view]; rw [hb]
  · intro a n w; simp only [view_accessible]; exact ha a n w

/-- The error runtime: the toy's, with the constants cell. -/
def errR (tys : Tys) (iE iW : Nat) (ok : Nat → List Nat → Prop) : RtInv :=
  ⟨errInv tys iE iW, ok, errRt tys, errInv.ext tys iE iW⟩

/-- The toy's invariant holds for the view of the error runtime when `errInv` does. -/
theorem errInv.toy {tys : Tys} {iE iW b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (h : errInv tys iE iW b L g (view (errRt tys) L m)) : toyInv tys b L g (view (toyRt tys) L m) := by
  rw [← view_toy_err]; exact h.1

/-- Conversely, from the toy's invariant and the cell facts. -/
theorem errInv.of_toy {tys : Tys} {iE iW b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (h : toyInv tys b L g (view (toyRt tys) L m)) (hCL : Outside CELL 16 L)
    (h2 : m.readLE CELL 8 = iE) (h3 : m.readLE (CELL + 8) 8 = iW) (h4 : m.accessible CELL 16 true = true) :
    errInv tys iE iW b L g (view (errRt tys) L m) := by
  refine ⟨by rw [view_toy_err]; exact h, ?_, ?_, by rw [view_accessible]; exact h4⟩
  · rw [readLE_view ⟨(CELL, CELL + 16), by simp [errRt], Nat.le_refl _, by omega⟩ (Outside.of_sub hCL (Nat.le_refl _) (by omega))]
    exact h2
  · rw [readLE_view ⟨(CELL, CELL + 16), by simp [errRt], by omega, by omega⟩ (Outside.of_sub hCL (by omega) (by omega))]
    exact h3

end Janus.Contracts.ErrorfRealRt

import Janus.Contracts.ErrorfRealImpl

/-!
# `ErrorfLive` at a program's own contract address (arm64)

`ErrorfRealImpl.real_impl` proves the contract for the stub at `E0 = 2^48`. A consumer's witness needs it for
`P.link impl` at `P.contractAddr "fmt.errorf"`, with the extraction's `tErr`, `iErr`, `tInt`, `iWrap`. The stub is
position independent and constant independent (it reads the two itab words from the runtime's cell), so
`RelocArm64.summary_transport` moves the proof: `errorf_live_at`.

The consumer states the stub's segment `errorfSeg a` in `impl` (`impl = [errorfSeg (contractAddr "fmt.errorf")]`) and
discharges `FetchedAt` by evaluation (`decide`/`rfl` on the extracted, closed program).
-/

namespace Janus.Contracts.ErrorfRealLive

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.Toy
  Janus.Contracts.ErrorfRealRt Janus.Contracts.RelocArm64
open Janus.Contracts.ErrorfRealCode (code E0)

/-- The stub placed at `a`. -/
def errorfSeg (a : Nat) : Segment := ⟨"live-stub.fmt.errorf", a, code⟩

/-- The program `p` fetches the stub's words at `a` (not a stub, not the exit address). -/
def FetchedAt (p : Program) (a : Nat) : Prop :=
  ∀ j w, code[j]? = some w → p.fetch (a + 4 * j) = some w ∧ p.stubAt (a + 4 * j) = none ∧ a + 4 * j ≠ p.exitAddr

theorem code_len : code.length = 126 := by decide +kernel

theorem fetchIn_append_none (l2 : List Segment) (pc : Nat) :
    ∀ (l1 : List Segment), Program.fetchIn l1 pc = none → Program.fetchIn (l1 ++ l2) pc = Program.fetchIn l2 pc := by
  intro l1
  induction l1 with
  | nil => intro _; rfl
  | cons seg rest ih =>
    intro h
    simp only [List.cons_append, Program.fetchIn] at h ⊢
    split
    · rename_i hc
      rw [if_pos hc] at h
      split at h
      · simp at h
      · rename_i hw
        exact ih h
    · rename_i hc
      rw [if_neg hc] at h
      exact ih h

theorem fetchIn_seg (a j w : Nat) (hw : code[j]? = some w) : Program.fetchIn [errorfSeg a] (a + 4 * j) = some w := by
  simp only [Program.fetchIn, errorfSeg]
  have e : (a + 4 * j - a) / 4 = j := by omega
  have hc : a ≤ a + 4 * j ∧ (a + 4 * j - a) % 4 = 0 := ⟨by omega, by omega⟩
  simp [e, hw, hc]

/-- `p` linked with the stub at `a` fetches the stub's words there, if `p` has no code, stub or exit address in them. -/
theorem fetchedAt_link (p : Program) (a : Nat) (hn : ∀ j, j < 126 → p.fetch (a + 4 * j) = none)
    (hs : ∀ j, j < 126 → p.stubAt (a + 4 * j) = none) (hx : ∀ j, j < 126 → a + 4 * j ≠ p.exitAddr) :
    FetchedAt (p.link [errorfSeg a]) a := by
  intro j w hw
  have hj : j < 126 := by
    have := (List.getElem?_eq_some_iff.mp hw).1
    simpa [code_len] using this
  refine ⟨?_, ?_, hx j hj⟩
  · simp only [Program.fetch, Program.link]
    rw [fetchIn_append_none _ _ _ (hn j hj)]
    exact fetchIn_seg a j w hw
  · simpa using hs j hj

theorem code_ok : CodeOK E0 code = true := by decide +kernel

/-- **`ErrorfLive` for the real format at any placement.** `tys`: the toy runtime's type descriptors (any well-formed
list; `[]` for a consumer), `tErr`, `tInt`, `iE`, `iW`: the extraction's constants (`iE`, `iW` are what the runtime cell
holds). -/
theorem errorf_live_at (p : Program) (a : Nat) (tys : Tys) (hty : TysOK tys) (tErr tInt iE iW : Nat)
    (hiE : iE < 2 ^ 64) (hiW : iW < 2 ^ 64) (hfit : a + 4 * 126 < 2 ^ 64) (hf : FetchedAt p a) :
    ErrorfLive p a 4096 (errR tys iE iW (fun _ _ => True)) tErr iE tInt iW 26 ErrorfRealFmt.fmtNum 4294967296 := by
  intro L b
  have h := ErrorfRealImpl.real_impl tys hty tErr tInt iE iW hiE hiW (fun _ _ => True) L b
  refine summary_transport E0 a code p _ _ (by rw [code_len]; decide) code_ok (by rw [code_len]; decide)
    (by rw [code_len]; exact hfit) (fun j w hw => hf j w hw) ?_ (fun s q h => h) (fun s s' q h => h) h
  intro t ht
  have := ht.1.2.1
  have h30 := ht.1.1
  show (t.regs 30).toNat < E0
  have : (t.regs 30).toNat < 2 ^ 48 := ht.1.2.1
  simp only [E0]; omega

end Janus.Contracts.ErrorfRealLive

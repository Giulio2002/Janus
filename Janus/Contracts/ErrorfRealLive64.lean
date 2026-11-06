import Janus.Contracts.ErrorfRealImpl64

/-!
# `ErrorfLive` at a program's own contract address (amd64)

`ErrorfRealImpl64.real_impl64` proves the contract for the stub at `E0 = 2^46`. `errorf_live_at64` moves it to
`P.link impl` at `P.contractAddr "fmt.errorf"` with the extraction's own constants, by
`RelocAmd64.summary_transport64` (the stub is position independent and reads its two itab words from the runtime's
cell). It needs the contract's `RetLow` (the saved return address is below `2^46 = E0`, so the final `jmp r15` leaves the
stub).
-/

namespace Janus.Contracts.ErrorfRealLive64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64
  Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.RelocAmd64
open Janus.Contracts.ErrorfRealCode64 (code64 E0)

/-- The stub placed at `a`. -/
def errorfSeg64 (a : Nat) : Amd64.Segment := ⟨"live-stub.fmt.errorf", a, code64⟩

/-- The program `p` fetches the stub's instructions at `a`. -/
def FetchedAt64 (p : Amd64.Program) (a : Nat) : Prop :=
  ∀ off ∈ stSet code64, p.fetch (a + off) = some (win code64 off) ∧ p.stubAt (a + off) = none ∧
    a + off ≠ p.exitAddr

theorem code_ok64 : CodeOK64 code64 = true := by decide +kernel

theorem code_len64 : code64.length = 486 := by decide +kernel

theorem fetchIn_append_none64 (l2 : List Amd64.Segment) (pc : Nat) :
    ∀ (l1 : List Amd64.Segment), Amd64.Program.fetchIn l1 pc = none →
      Amd64.Program.fetchIn (l1 ++ l2) pc = Amd64.Program.fetchIn l2 pc := by
  intro l1
  induction l1 with
  | nil => intro _; rfl
  | cons seg rest ih =>
    intro h
    simp only [List.cons_append, Amd64.Program.fetchIn] at h ⊢
    split
    · rename_i hc; rw [if_pos hc] at h; simp at h
    · rename_i hc; rw [if_neg hc] at h; exact ih h

theorem fetchIn_seg64 (a off : Nat) (h : off < code64.length) :
    Amd64.Program.fetchIn [errorfSeg64 a] (a + off) = some (win code64 off) := by
  simp only [Amd64.Program.fetchIn, errorfSeg64]
  have hc : a ≤ a + off ∧ a + off < a + code64.length := ⟨by omega, by omega⟩
  have e : a + off - a = off := by omega
  simp [hc, e, win]

theorem fetchedAt_link64 (p : Amd64.Program) (a : Nat)
    (hn : ∀ off ∈ stSet code64, p.fetch (a + off) = none)
    (hs : ∀ off ∈ stSet code64, p.stubAt (a + off) = none)
    (hx : ∀ off ∈ stSet code64, a + off ≠ p.exitAddr) :
    FetchedAt64 (p.link [errorfSeg64 a]) a := by
  intro off ho
  have hlt : off < code64.length := seqStarts_lt code64 _ _ _ ho
  refine ⟨?_, ?_, hx off ho⟩
  · simp only [Amd64.Program.fetch, Amd64.Program.link]
    rw [fetchIn_append_none64 _ _ _ (hn off ho)]
    exact fetchIn_seg64 a off hlt
  · simpa using hs off ho

/-- **`ErrorfLive` for the real format at any placement (amd64).** -/
theorem errorf_live_at64 (p : Amd64.Program) (a : Nat) (tys : Tys) (hty : TysOK tys) (tErr tInt iE iW : Nat)
    (hiE : iE < 2 ^ 64) (hiW : iW < 2 ^ 64) (hfit : a + 486 ≤ 2 ^ 47) (hf : FetchedAt64 p a) :
    ErrorfLive p a 4096 (errR tys iE iW (fun _ _ => True)) tErr iE tInt iW 26 ErrorfRealFmt.fmtNum 4294967296 := by
  intro L b
  have h := ErrorfRealImpl64.real_impl64 tys hty tErr tInt iE iW hiE hiW (fun _ _ => True) L b
  refine summary_transport64 E0 a code64 p _ _ (by rw [code_len64]; decide) code_ok64 (by rw [code_len64]; decide)
    (by rw [code_len64]; exact hfit) hf ?_ (fun s q h => h) (fun s s' q h => h) h
  intro t ht
  have := ht.2.1
  show t.mem.readLE (t.regs 4).toNat 8 < E0
  simp only [ErrorfAmd64.RetLow] at this
  simp only [E0]; omega

end Janus.Contracts.ErrorfRealLive64

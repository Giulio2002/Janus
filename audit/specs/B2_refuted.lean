import Janus
/-! B2 after fix F4: the `BR X0` program with `X0 = 0` does **not** satisfy `Ensures`. For the
admissible return address `ret = 0x2000` (and any call state) the branch lands on `pc = 0`,
where there is no code: the run faults with `noCode 0`, so it never returns.
Run: cd /srv/janus && lake env lean audit/specs/B2_refuted.lean (prints the axioms). -/
open Janus Janus.Arm64 Janus.GoABI

def brSeg : Segment := ⟨"f", 0x1000, [0xd61f0000]⟩
def brProg : Program := ⟨[brSeg], [], 0, []⟩

theorem br_zero_not_ensures : ¬ Ensures brProg 0x1000 [0] (fun _ => True) (fun _ _ => True) := by
  intro h
  have hret : RetAddr brProg 0x2000 := RetAddr.of_check (by decide)
  let s := setup (brProg.withExit 0x2000) 0x1000 [0] default
  have hs : CallSetup (brProg.withExit 0x2000) 0x1000 [0] s := setup_callSetup _ (by decide)
  have hf : Faults (brProg.withExit 0x2000) s := by
    have hst : Arm64.step 0xd61f0000 s = .ok { s with pc := 0 } := by
      rw [Arm64.step_of_decode (i := .br 0) (by decide)]
      rfl
    have h1 : Program.Steps (brProg.withExit 0x2000) s 1 { s with pc := 0 } :=
      .single (by decide) (by decide) (by decide) hst
    exact ⟨1 + 1, .noCode 0, by rw [Program.run_steps h1]; rfl, by decide⟩
  exact (h.returns hret hs trivial).not_faults hf
#print axioms br_zero_not_ensures

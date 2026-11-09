import Janus
/-! ATTACK B2 (design hazard): the return sentinel `exitAddr = 0` is an ordinary 64-bit value, so
any *computed* branch to 0 counted as a return. Synthetic program: `BR X0` (0xd61f0000). With
`X0 = 0` the old `Ensures` (fixed `exitAddr`) was provable; on hardware `BR` to address 0 is a
SIGSEGV (page 0 is never mapped on Linux).

After fix F4, `Ensures` quantifies over every admissible return address `ret` (`RetAddr`) and
runs `brProg.withExit ret`. The old proof no longer works: this file must FAIL to compile
(the branch reaches `pc = 0`, which is not `ret` for `ret ≠ 0`). `B2_refuted.lean` proves the
negation.
Run: cd /srv/janus && lake env lean audit/specs/B2_exit_sentinel.lean -/
open Janus Janus.Arm64 Janus.GoABI

def brSeg : Segment := ⟨"f", 0x1000, [0xd61f0000]⟩
def brProg : Program := { segments := [brSeg], stubs := [], exitAddr := 0 }

theorem br_zero_returns : Ensures brProg 0x1000 [0] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs _
  have hpc : s.pc.toNat = 0x1000 := hs.pc_toNat (by decide)
  have hx0 : s.regs 0 = 0 := hs.reg (i := 0) (by simp)
  refine ⟨2, { s with pc := 0 }, ?_, ⟨rfl, rfl, rfl, rfl⟩, trivial⟩
  have hst : Arm64.step 0xd61f0000 s = .ok { s with pc := 0 } := by
    rw [Arm64.step_of_decode (i := .br 0) (by decide)]
    simp [Arm64.exec, Arm64.branchReg, State.readZR, hx0]
  rw [Program.run_succ_step (by rw [hpc]; exact (hret.ne_of_fetch (pc := 0x1000) rfl)) (by rw [hpc]; rfl) (by rw [hpc]; rfl) hst]
  rfl

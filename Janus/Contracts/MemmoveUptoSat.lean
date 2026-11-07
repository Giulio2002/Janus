import Janus.Contracts.LiveSat
import Janus.Contracts.LiveStubMemmoveUpto

/-!
# The variable-size `memmove` stub is a witness for `MemmoveLive` (arm64, U-MEMMOVE-UPTO)

`LiveStub.memmoveUptoSeg` placed at `A0` of a program with no other code meets `MemmoveLive` for a runtime that serves
the requests `[q, p, k]`, `1 ≤ k ≤ 32` (and the call state of the fixed-size witness, `k = 8`, satisfies the precondition), so
a theorem assuming `R.ok memmove [q, p, k]` for several sizes `k` is not vacuous.
-/

namespace Janus.Contracts.MemmoveUptoSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

def okUp : Nat → List Nat → Prop := fun a args => a = A0 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32

set_option maxHeartbeats 16000000 in
theorem upto_impl : MemmoveLive (toy.link (at0 (memmoveUptoCode 32))) A0 4096 (toyR tys0 okUp) := by
  rw [link_at0]
  janus_live_memmove_upto 32 (fun _ h => h.2)

theorem memmoveUpto_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemmoveLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 3 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
      Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
      LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat := by
  refine ⟨at0 (memmoveUptoCode 32), toyR tys0 okUp, upto_impl, [], 0x400, wst [CB, CB + 0x100, 8], rfl,
    wguardE _ 3 (by omega), ⟨⟨rfl, ⟨CB, CB + 0x100, 8, rfl, by decide, by decide⟩⟩, wmem_inv 0, by simp, wwin _ 3 (by omega)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩

end Janus.Contracts.MemmoveUptoSat

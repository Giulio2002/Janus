import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.LiveStubMemmoveUptoAmd64

/-!
# The variable-size `memmove` stub is a witness for `MemmoveLive64` (amd64, U-MEMMOVE-UPTO)

The amd64 twin of `MemmoveUptoSat.lean`: `memmoveUptoSeg64` at `A0` meets `MemmoveLive64` for a runtime serving `[q, p, k]`,
`1 ≤ k ≤ 32`, and the fixed-size witness's call state (`k = 8`) satisfies the precondition.
-/

namespace Janus.Contracts.MemmoveUptoSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0)

def okUp : Nat → List Nat → Prop := fun a args => a = A0 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32

set_option maxHeartbeats 16000000 in
theorem upto_impl : MemmoveLive64 (toy.link (at0 (memmoveUptoCode64 32))) A0 4096 (toyR tys0 okUp) := by
  rw [link_at0]
  janus64_live_memmove_upto 32 (fun _ h => h.2)

theorem memmoveUpto64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MemmoveLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 3 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3) ∧
      MemAmd64.Input s 4096 3 (s.regs 3).toNat (s.regs 1).toNat ∧
      LiveDest64 R L s 4096 3 (s.regs 0).toNat (s.regs 1).toNat := by
  have h0 : ((LiveSatAmd64.wst [CB, CB + 0x100, 8]).regs 0).toNat = CB := wr0 _ (by decide)
  have h3 : ((LiveSatAmd64.wst [CB, CB + 0x100, 8]).regs 3).toNat = CB + 0x100 := wr3 _ (by decide)
  have h1 : ((LiveSatAmd64.wst [CB, CB + 0x100, 8]).regs 1).toNat = 8 := wr1 _ (by decide)
  refine ⟨at0 (memmoveUptoCode64 32), toyR tys0 okUp, upto_impl, [], 0x400, LiveSatAmd64.wst [CB, CB + 0x100, 8], rfl,
    wguardE64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, ⟨CB, CB + 0x100, 8, rfl, by decide, by decide⟩⟩, wmem_inv 0, by simp,
      wwin64 _ 3 (by omega)⟩,
    ⟨by rw [h3, h1]; decide, by rw [h3, h1, LiveSatAmd64.wmem_eq]; decide, by rw [h3]; exact cb_out_inputwin _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by rw [h0, h1]; decide, by rw [h0, h1, LiveSatAmd64.wmem_eq]; decide, by rw [h0]; exact cb_out_win64 _ 3 (by omega) _ _ (by decide),
      Or.inr (by rw [h0]; exact cb_out_rt _ _ (by decide)), by rw [h0]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩

end Janus.Contracts.MemmoveUptoSatAmd64

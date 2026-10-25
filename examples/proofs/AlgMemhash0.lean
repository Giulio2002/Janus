import Extracted

/-!
# `runtime.memhash0` meets the `Memhash0` contract

**Guarantee.** For every hash model `H` and every stack bound `d`, the machine code of Go 1.26's
`runtime.memhash0(p, h)` (the hash function of zero-size types) satisfies
`Janus.Contracts.Hash.Memhash0 … H d`: from every call state with the contract's precondition it
returns to `X30` without faulting, keeps `SP`, `X18`, `X28`, `X29` and `FPCR`, changes no memory
(so `H.Env` still holds), and returns the seed `h` in `X0`.

**What the code does.** `MOVD R1, R0; RET`: it reads nothing.

**Assumptions.** Only the contract's precondition; nothing about `H` (not even its laws).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem
  Janus.Contracts.Hash

namespace Proof

/-- An `EqRet` return (memory changed only in the callee's window) whose memory satisfies
`H.Env` is an `HRet` return. -/
theorem hRet_of_eqRet (H : HashModel) {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (h : EqRet d nargs s s' P) (he : H.Env s'.mem (s.regs 28)) : HRet H d nargs s s' P := by
  obtain ⟨r, v, fl, fs, m, rfl, hf, hp⟩ := h
  exact ⟨r, v, fl, fs, m, rfl, hf.mono (fun a n h => by simp only [outside_append] at h; exact h.2), he, hp⟩

theorem correctness (H : HashModel) (d : Nat) : Memhash0 Extracted.program Extracted.entry H d := by
  intro s hpc ⟨he, hg, ⟨hl1, hl2, hc⟩, hout, _, _⟩
  janus_run
  refine hRet_of_eqRet H (EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl (MemFrame.refl _ _) ?_) he
  simp [setReg]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memhash0(VAL, 7)` on `EqHashModel.wmem` (model `H0`), goroutine
`wg` (its stack guard word is 0), stack pointer `wsp`, return address `wret`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 1 then 7
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (model `H0`, stack bound 64). -/
theorem pre : HPre H0 64 2 s0 := by
  refine ⟨wmem_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CallOK, H0_priv, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ HPre H0 64 2 s :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns the seed 7. -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => HRet H0 64 2 s0 s' fun r => r 0 = 7) :=
  correctness H0 64 s0 rfl pre

end Witness

end Proof

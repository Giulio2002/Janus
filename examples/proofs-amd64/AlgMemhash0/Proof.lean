import Janus
import Extracted

/-!
# `runtime.memhash0` (amd64) meets the `Memhash0` contract

**Guarantee.** For every hash model `H` and every stack bound `d`, the amd64 machine code of Go
1.26's `runtime.memhash0(p, h)` (the hash function of zero-size types) satisfies
`Janus.Contracts.HashAmd64.Memhash0 … H d`: from every call state with the contract's
precondition it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`,
`FS` and `MXCSR` kept, changes no memory (so `H.Env` still holds), and returns the seed `h` in
`RAX`.

**What the code does.** `MOVQ BX, AX; RET`: it reads nothing.

**Assumptions.** Only the contract's precondition; nothing about `H` (not even its laws).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64 Janus.Contracts.HashAmd64
open Janus.Contracts.Hash (HashModel)

namespace Proof

/-- An `EqRet` return (memory changed only in the callee's window) whose memory satisfies
`H.Env` is an `HRet` return (amd64). -/
theorem hRet_of_eqRet (H : HashModel) {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (h : EqRet d nargs s s' P) (he : H.Env s'.mem (s.regs 14)) : HRet H d nargs s s' P := by
  obtain ⟨r, x, y, fl, mx, m, zh, kr, rfl, hmx, hf, hp⟩ := h
  exact ⟨r, x, y, fl, mx, m, zh, kr, rfl, hmx,
    hf.mono (fun a n h => by simp only [outside_append] at h; exact h.2), he, hp⟩

theorem correctness (H : HashModel) (d : Nat) : Memhash0 Extracted.program Extracted.entry H d := by
  intro s hpc ⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, hgo⟩
  janus64_run
  refine hRet_of_eqRet H (EqRet.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?_) he <;>
    simp_all [setRegF, retAddrOf]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memhash0(VAL, 7)` on `EqHashModel.wmem64` (model `H0`; return
address `wret` at `[wsp]`), goroutine `wg` (its stack guard word is 0), `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 3 then 7
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (model `H0`, stack bound 64). -/
theorem pre : HPre H0 64 2 s0 := by
  refine ⟨wmem64_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_⟩ <;>
    simp only [CallOK, H0_priv, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
      outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.rip = BitVec.ofNat 64 Extracted.entry ∧ HPre H0 64 2 s :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns the seed 7. -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => HRet H0 64 2 s0 s' fun r => r 0 = 7) :=
  correctness H0 64 s0 rfl pre

end Witness

end Proof

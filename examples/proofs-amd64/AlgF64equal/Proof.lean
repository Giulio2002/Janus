import Janus
import Extracted

/-!
# `runtime.f64equal` (amd64) meets the `Fequal binary64 8` contract

**Guarantee.** For every stack bound `d`, the amd64 machine code of Go 1.26's
`runtime.f64equal(a, b)` (the equality function of `float64`) satisfies
`Janus.Contracts.MemAmd64.Fequal … d binary64 8`: from every call state with the contract's
precondition (the stack guard and ABI conditions, Go's `MXCSR`, the 8 bytes at `a` and at `b`
readable) it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS`
and the control bits of `MXCSR` kept, changes no memory, and returns in `AL` Go's `==` on the two
`float64` values (`Mem.feq`: false if either is a NaN, true for `+0 == -0`).

**What the code does.** `MOVSD 0(AX), X0; MOVSD 0(BX), X1; UCOMISD X1, X0; SETEQ AL; SETPC CL;
ANDL CX, AX; RET`. The `UCOMIS` may raise exception flags in `MXCSR` (a NaN, a denormal), which
the contract allows; `MemAmd64.comis_feq` and `sete_setnp_and` turn `ZF ∧ ¬PF` into `feq`.

**Assumptions.** Only the contract's precondition.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Float Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes feq)

namespace Proof

theorem correctness (d : Nat) : Fequal Extracted.program Extracted.entry d binary64 8 := by
  intro s hpc ⟨⟨hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  refine EqRet.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?_
  all_goals try (simp_all [setRegF, retAddrOf]; done)
  · simp only [setXmmF]; simp only [reduceIte, Nat.reduceEqDiff]
  · simp only [BitVec.toNat_ofNat]; rw [mx_raise_div, GoMXCSR.mod hm]
  · have h0 := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
    have h1 := Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
    rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 0).toNat 8 < 340282366920938463463374607431768211456),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 3).toNat 8 < 340282366920938463463374607431768211456)]
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_setWidth, BitVec.toNat_and]
    rw [Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 64), show (2:Nat) ^ 32 = 4294967296 from rfl,
      sete_setnp_and, comis_feq]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `f64equal(VAL, VAL)` on `EqHashModel.wmem64` (return address `wret`
at `[wsp]`; `VAL` holds 42, a denormal `float64`), goroutine `wg` (its stack guard word is 0),
`RSP = wsp`, the default `MXCSR` `0x1F80`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 VAL
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ GoMXCSR s0 ∧ Input s0 64 2 (s0.regs 0).toNat 8 ∧
    Input s0 64 2 (s0.regs 3).toNat 8 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, by unfold GoMXCSR; decide, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
      outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ GoMXCSR s ∧ Input s 64 2 (s.regs 0).toNat 8 ∧ Input s 64 2 (s.regs 3).toNat 8) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true` (a number equals itself). -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  have hv : feq binary64 (s0.mem.readLE (s0.regs 0).toNat 8) (s0.mem.readLE (s0.regs 3).toNat 8) = true := by
    decide
  refine (correctness 64 s0 rfl pre).mono ?_
  intro s' h; simpa only [hv] using h

end Witness

end Proof

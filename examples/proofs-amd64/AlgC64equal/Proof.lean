import Janus
import Extracted

/-!
# `runtime.c64equal` (amd64) meets the `Cequal binary32 4` contract

**Guarantee.** For every stack bound `d`, the amd64 machine code of Go 1.26's
`runtime.c64equal(a, b)` (the equality function of `complex64`) satisfies
`Janus.Contracts.MemAmd64.Cequal … d binary32 4`: from every call state with the contract's
precondition (the stack guard and ABI conditions, Go's `MXCSR`, the 8 bytes at `a` and at `b`
readable) it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS`
and the control bits of `MXCSR` kept, changes no memory, and returns in `AL` Go's `==` on the
real parts and on the imaginary parts (`Mem.feq`), and-ed.

**What the code does.** Four `MOVSS` loads (`0(AX)`, `4(AX)`, `0(BX)`, `4(BX)`), `UCOMISS` of the
real parts with `SETEQ AL; SETPC CL; ANDL CX, AX`, of the imaginary parts with
`SETEQ DL; SETPC CL; ANDL CX, DX`, then `ANDL DX, AX; RET`. Both comparisons may raise exception
flags in `MXCSR`, which the contract allows.

**Assumptions.** Only the contract's precondition.
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Float Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (BoolRes feq)

namespace Proof

/-- The low byte of an `AND`. -/
theorem and_low_byte (m n : Nat) : (m &&& n) % 256 = m % 256 &&& n % 256 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.and_mod_two_pow]

theorem mod32_low_byte (x : Nat) : x % 2 ^ 32 % 256 = x % 256 := Nat.mod_mod_of_dvd _ (by decide)
theorem mod64_low_byte (x : Nat) : x % 2 ^ 64 % 256 = x % 256 := Nat.mod_mod_of_dvd _ (by decide)

/-- `SETE` and `SETNP` bytes, `AND`ed. -/
theorem sete_setnp (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then 1#8 else 0#8).toNat &&& (if Q then 0#8 else 1#8).toNat) = (decide P && !decide Q).toNat := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem bool_and_toNat (a b : Bool) : a.toNat &&& b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

theorem correctness (d : Nat) : Cequal Extracted.program Extracted.entry d binary32 4 := by
  intro s hpc ⟨⟨hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  refine EqRet.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (MemFrame.refl _ _) ?_
  all_goals try (simp_all [setRegF, retAddrOf]; done)
  · simp only [setXmmF]; simp only [reduceIte, Nat.reduceEqDiff]
  · simp only [BitVec.toNat_ofNat]
    rw [show (2:Nat) ^ 32 = 4294967296 from rfl, mx_raise_div, Nat.mod_mod, mx_raise_div, GoMXCSR.mod hm]
  · have h0 := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
    have h1 := Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 4
    have h2 := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 4) 4
    have h3 := Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 4) 4
    rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 0).toNat 4 < 4294967296),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 3).toNat 4 < 4294967296),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE ((s.regs 0).toNat + 4) 4 < 4294967296),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE ((s.regs 3).toNat + 4) 4 < 4294967296)]
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_setWidth, BitVec.toNat_and]
    simp only [and_low_byte, mod32_low_byte, mod64_low_byte, Janus.Contracts.IfaceAmd64.setcc_low_byte,
      sete_setnp, bool_and_toNat, comis_feq]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `c64equal(VAL, VAL)` on `EqHashModel.wmem64` (return address `wret`
at `[wsp]`), goroutine `wg` (its stack guard word is 0), `RSP = wsp`, the default `MXCSR`
`0x1F80`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 3 then BitVec.ofNat 64 VAL
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ GoMXCSR s0 ∧ Input s0 64 2 (s0.regs 0).toNat (2 * 4) ∧
    Input s0 64 2 (s0.regs 3).toNat (2 * 4) := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, by unfold GoMXCSR; decide, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons,
      outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ GoMXCSR s ∧ Input s 64 2 (s.regs 0).toNat (2 * 4) ∧
      Input s 64 2 (s.regs 3).toNat (2 * 4)) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true` (a number equals itself). -/
theorem returns : ReachesRet Extracted.program (retAddrOf s0) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  have hv : (feq binary32 (s0.mem.readLE (s0.regs 0).toNat 4) (s0.mem.readLE (s0.regs 3).toNat 4) &&
      feq binary32 (s0.mem.readLE ((s0.regs 0).toNat + 4) 4)
        (s0.mem.readLE ((s0.regs 3).toNat + 4) 4)) = true := by
    decide
  refine (correctness 64 s0 rfl pre).mono ?_
  intro s' h; simpa only [hv] using h

end Witness

end Proof

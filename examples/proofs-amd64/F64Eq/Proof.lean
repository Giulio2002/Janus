import Janus
import Extracted

/-!
# `F64Eq(x, y float64) bool` on amd64: Go's `==` on `float64`

```
UCOMISD X1, X0 ; SETE AL ; SETNP CL ; ANDL CX, AX ; RET
```

**Guarantee.** For all binary64 encodings `x`, `y` in the low halves of `X0`, `X1` and every Go
call state with Go's `MXCSR` controls (`GoMXCSR`), the call returns and the `bool` result in `AL`
is `feq x y` (`ZF ∧ ¬PF` of `UCOMISD`, `MemAmd64.comis_feq`): `false` for a NaN, otherwise value
equality, so `+0 == -0`. The same specification as the arm64 theorem.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Contracts.Mem

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = y.toNat ∧ GoMXCSR s)
      (fun _ s' => (s'.regs 0).toNat % 256 = (feq binary64 x.toNat y.toNat).toNat) := by
  intro ret hret s hs ⟨hst, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [ha, hb, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]

/-! ## Non-vacuity: the precondition holds for a concrete call, and the result is reached -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- `+0` and `-0`. -/
def x : BitVec 64 := 0#64
def y : BitVec 64 := 0x8000000000000000#64

/-- The witness call state `F64Eq(+0, -0)`. -/
def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun i => if i = 1 then BitVec.ofNat 128 0x8000000000000000 else 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ (s0.xmm 0).toNat % 2 ^ 64 = x.toNat ∧
    (s0.xmm 1).toNat % 2 ^ 64 = y.toNat ∧ GoMXCSR s0 :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by unfold GoMXCSR; decide⟩

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = y.toNat ∧
      GoMXCSR s) :=
  ⟨ret, s0, x, y, hret, setup, hpre⟩

/-- So the guarantee is reached: `+0 == -0` returns `true`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness x y ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof

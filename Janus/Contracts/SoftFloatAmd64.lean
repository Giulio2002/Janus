import Janus.Contracts.SoftFloat
import Janus.Contracts.InstrumentCallsAmd64

/-!
# `runtime.KeepAlive` and the soft-float entry points (amd64)

The amd64 versions of `Janus.Contracts.SoftFloat` (whose module documentation explains the
contracts, the IEEE 754 specification and why it is restricted to results that are not tiny): Go's
ABIInternal of amd64 passes the two integer arguments in `RAX`, `RBX` (`KeepAlive`'s interface in
`RAX`, `RBX` too) and returns the result in `RAX`; `g` is in `R14`, the return address at `[RSP]`.

The soft-float runtime ignores `MXCSR`; the contracts require the Go environment `GoMXCSR` (round
to nearest even, every exception masked, no `DAZ`/`FTZ`, any sticky flags) so that the
satisfiability witness may be hardware `ADDSD`/`SUBSD`/`MULSD`/`DIVSD`, and leave the sticky
exception flags (`MXCSR` bits 0–5) unspecified after the call and the upper vector halves and the
opmask registers (`zmmHi`, `kreg`) unspecified as for every amd64 contract.
-/

namespace Janus.Contracts.SoftFloat

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument

/-- The return of a soft-float function or `KeepAlive` from `s` to `s'` (amd64) with the facts `P r`
about the result registers `r`: `RSP` popped, `RBP`, `R14` kept, `X15` kept, the `MXCSR` controls
(everything above the sticky flags) kept, memory changed only in the callee's stack window; the
other registers, the flags and the other vector state unspecified. -/
def SoftRet64 (n : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r x y fl m zh kr mx, s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                                        ymmHi := y, flags := fl, mem := m, rip := retAddrOf s, zmmHi := zh,
                                        kreg := kr, mxcsr := mx } ∧
    mx.toNat / 64 = s.mxcsr.toNat / 64 ∧ MemFrame s.mem m (rtWrites64 softEnv s n) ∧ P r

/-- The control bits of `MXCSR` (bit 6 and up) survive OR-ing in sticky flags. -/
theorem mxcsr_ctl (a b : Nat) (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 (a ||| b % 64)).toNat / 64 = a / 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha (by omega))]
  have h1 : (a ||| b % 64) / 64 = (a ||| b % 64) >>> 6 := by rw [Nat.shiftRight_eq_div_pow]
  have h2 : a / 64 = a >>> 6 := by rw [Nat.shiftRight_eq_div_pow]
  rw [h1, h2, Nat.shiftRight_or_distrib, Nat.shiftRight_eq_zero _ _ (show b % 64 < 2 ^ 6 by omega), Nat.or_zero]

theorem SoftRet64.intro (n : Nat) (s s' : State) (P : (Nat → W64) → Prop) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64) (hfr : MemFrame s.mem s'.mem (rtWrites64 softEnv s n))
    (hp : P s'.regs) (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all)
    (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : SoftRet64 n s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, s'.zmmHi, s'.kreg, s'.mxcsr, ?_, hmx, hfr, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hx87 hfw ⊢
  subst hrip hfs hdf hx87 hfw
  congr
  · funext i
    simp only [MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- A call of a two-argument soft-float function: the runtime call frame and Go's `MXCSR`. -/
def SoftPre64 (s : State) : Prop := RTPre64 softEnv 2 s ∧ GoMXCSR s

/-- **`runtime.fadd64(f, g)`** (amd64; `RAX = f`, `RBX = g`, result `RAX`): the IEEE sum (round to
nearest even; some NaN where IEEE has one), when the exact sum is not tiny. -/
def SoftFaddContract64 (p : Janus.Amd64.Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre64 s ∧ ¬ AddTiny (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => SoftRet64 2 s s' fun r =>
      ResultIs binary64 (add binary64 .rne (s.regs 0).toNat (s.regs 3).toNat) (r 0).toNat)

/-- **`runtime.fsub64(f, g)`** (amd64): the IEEE difference, when the exact difference is not tiny. -/
def SoftFsubContract64 (p : Janus.Amd64.Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre64 s ∧ ¬ SubTiny (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => SoftRet64 2 s s' fun r =>
      ResultIs binary64 (sub binary64 .rne (s.regs 0).toNat (s.regs 3).toNat) (r 0).toNat)

/-- **`runtime.fmul64(f, g)`** (amd64): the IEEE product, when the exact product is not tiny. -/
def SoftFmulContract64 (p : Janus.Amd64.Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre64 s ∧ ¬ MulTiny (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => SoftRet64 2 s s' fun r =>
      ResultIs binary64 (mul binary64 .rne (s.regs 0).toNat (s.regs 3).toNat) (r 0).toNat)

/-- **`runtime.fdiv64(f, g)`** (amd64): the IEEE quotient, when the exact quotient is not tiny. -/
def SoftFdivContract64 (p : Janus.Amd64.Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre64 s ∧ ¬ DivTiny (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => SoftRet64 2 s s' fun r =>
      ResultIs binary64 (div binary64 .rne (s.regs 0).toNat (s.regs 3).toNat) (r 0).toNat)

/-- **`runtime.KeepAlive(x any)`** (amd64; `RAX, RBX = x`): returns, changing only the callee's
frame, when `runtime.cgoAlwaysFalse` (at `cgoFalse`) is `false` and not inside the callee's stack
window (the function stores its arguments there before it reads the global). -/
def KeepAliveContract64 (p : Janus.Amd64.Program) (addr cgoFalse : Nat) : Prop :=
  Summary p addr
    (fun s => RTPre64 softEnv 2 s ∧ Misc.CgoAlwaysFalse s.mem cgoFalse ∧
      Spec.Disjoint cgoFalse 1 ((s.regs 4).toNat - softDepth) (softDepth + 8 + 8 * 2))
    (fun s s' => SoftRet64 2 s s' fun _ => True)

end Janus.Contracts.SoftFloat

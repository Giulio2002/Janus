import Janus.Contracts.InstrumentCalls
import Janus.Contracts.Misc
import Janus.Spec.Complex

/-!
# `runtime.KeepAlive` and the soft-float entry points (arm64)

Two groups of runtime functions that compiled code reaches without any runtime state:

| Go (1.26) | Linked name | Contract |
| --- | --- | --- |
| `runtime.KeepAlive(x any)`: `if cgoAlwaysFalse { println(x) }` | `runtime.KeepAlive` | `KeepAliveContract` |
| `a + b` of `float64` on a soft-float target (`-d=softfloat`), and the test binary of `runtime` | `runtime.fadd64` | `SoftFaddContract` |
| `a - b` (`fsub64(f, g) = fadd64(f, fneg64(g))`) | `runtime.fsub64` | `SoftFsubContract` |
| `a * b` | `runtime.fmul64` | `SoftFmulContract` |
| `a / b` | `runtime.fdiv64` | `SoftFdivContract` |

`KeepAlive` is also a compiler intrinsic (`ssagen` `OpKeepAlive`): a call that the compiler
keeps (a function value, `-N`, another package's non-inlined caller) reaches the function, whose
body is dead code behind `cgoAlwaysFalse`. Its contract is a no-op: the call returns, changes only
the callee's frame, and needs the global `runtime.cgoAlwaysFalse` to be `false` (a stated
hypothesis, `Janus.Contracts.Misc.CgoAlwaysFalse`: the extractor does not copy writable data).

**Soft float.** The four functions take and return IEEE 754 binary64 encodings in integer
registers (`X0`, `X1`; the result in `X0`), use no runtime state, and are leaf code apart from the
stack-growth call and `fpack64`/`divlu`. The contracts specify them as **IEEE 754 binary64
round-to-nearest-even** (`Janus.Float.add`, `sub`, `mul`, `div`; a NaN result is "some NaN":
the runtime delivers the canonical `0x7FF8000000000000`), but only where the runtime is known to
deliver that:

* Go's soft float is **not** IEEE 754 for subnormal results. Its `fpack64` has a separate path
  for a result below `2^-1022`, and `fadd64` (hence `fsub64`) gives a wrong value for many
  cancellations that leave a subnormal: for example `0x0170000000155555 + 0x816fffffffffffff`
  is `0x00000000002aaaab` where IEEE (and the hardware) gives `0x0000055555600000`. So **no
  contract claims IEEE where the exact result is tiny** (`AddTiny`, `MulTiny`, `DivTiny`:
  finite non-zero operands whose exact sum, product or quotient is non-zero and below `2^-1022`
  in magnitude); the precondition excludes those calls and the contract says nothing about
  what the runtime returns for them. `fmul64` and `fdiv64` showed no deviation on millions of
  random subnormal-range draws (`examples/rtmisc/softcheck`), but the same precondition is
  kept: the sampled agreement is not a proof, and the precondition costs nothing for results
  in the normal range.
* Everywhere else (zeros of either sign, infinities, NaNs, overflow, normal results, subnormal
  operands) the runtime's result is the IEEE one (NaN for NaN). That is a claim about the
  runtime, tested against the hardware on random draws that include every one of those classes
  (`examples/rtmisc/softcheck`, `scripts/softfloat-check.sh`) and pinned to the runtime's code
  (`runtimeContractStubs`). It is **not** derived from the code.

The soft-float runtime ignores `FPCR`, `FPSR`; the contracts nevertheless require the Go
environment `FPCR = 0` (so that the satisfiability witness may be a hardware `FADD`, whose
result under `FPCR = 0` is the IEEE one) and leave `FPSR` unspecified.

**Frame.** As for the other runtime contracts: the call returns to `X30` with `SP`, `X18`, `X28`,
`X29` preserved, every other register, the SIMD registers and the flags arbitrary (and the
exclusive monitor unspecified), memory changed only in the `softDepth` bytes below `SP` and the
argument spill slots; `FPCR`, `TPIDR_EL0`, `DCZID_EL0` unchanged.
-/

namespace Janus.Float

/-- A binary64 encoding of a finite non-zero number (normal or subnormal). -/
def IsNum (x : Nat) : Prop := classify binary64 x = .normal ∨ classify binary64 x = .subnormal

/-- The exact result of an operation (`addExact`/`mulExact` form) is non-zero and tiny: below
`2^-1022` in magnitude before rounding (`Rounded.tinyBefore`). -/
def TinyExact : Option (Bool × Nat × Int) → Prop
  | none => False
  | some (neg, m, e) => (round binary64 .rne neg m e).tinyBefore = true

/-- `a + b` has a tiny exact result (finite non-zero operands). -/
def AddTiny (a b : Nat) : Prop :=
  IsNum a ∧ IsNum b ∧
    TinyExact (addExact (valueOf binary64 a).n (valueOf binary64 a).e (valueOf binary64 b).n (valueOf binary64 b).e)

/-- `a - b` has a tiny exact result (finite non-zero operands). -/
def SubTiny (a b : Nat) : Prop :=
  IsNum a ∧ IsNum b ∧
    TinyExact (addExact (valueOf binary64 a).n (valueOf binary64 a).e (-(valueOf binary64 b).n) (valueOf binary64 b).e)

/-- `a * b` has a tiny exact result (finite non-zero operands). -/
def MulTiny (a b : Nat) : Prop :=
  IsNum a ∧ IsNum b ∧
    TinyExact (mulExact (valueOf binary64 a).n (valueOf binary64 a).e (valueOf binary64 b).n (valueOf binary64 b).e)

/-- `a / b` has a tiny exact quotient (finite non-zero operands; the quotient in round-to-odd
form has the exponent of the exact one). -/
def DivTiny (a b : Nat) : Prop :=
  IsNum a ∧ IsNum b ∧
    (let q := divOdd binary64.fbits (valueOf binary64 a).mag.1 (valueOf binary64 a).mag.2
      (valueOf binary64 b).mag.1 (valueOf binary64 b).mag.2
     (round binary64 .rne false q.1 q.2).tinyBefore = true)

instance (x : Nat) : Decidable (IsNum x) := inferInstanceAs (Decidable (_ ∨ _))
instance (o : Option (Bool × Nat × Int)) : Decidable (TinyExact o) := by
  unfold TinyExact; split <;> infer_instance
instance (a b : Nat) : Decidable (AddTiny a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (a b : Nat) : Decidable (SubTiny a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (a b : Nat) : Decidable (MulTiny a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (a b : Nat) : Decidable (DivTiny a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Janus.Float

namespace Janus.Contracts.SoftFloat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument

/-- The stack the soft-float functions and `KeepAlive` may use below `SP`: their frames (at most
`80` bytes for `fdiv64`) and those of `fpack64`, `divlu` and `printlock`'s caller chain are far
below this. -/
def softDepth : Nat := 256

/-- No runtime state: the environment is trivial and there is no private memory. -/
def softEnv : RtEnv := { Env := fun _ _ => True, priv := [], depth := softDepth }

theorem softEnv_laws : softEnv.Laws := ⟨fun _ _ _ h _ => h⟩

/-- The return of a soft-float function or `KeepAlive` from `s` to `s'` (arm64) with the facts `P r`
about the result registers `r`: `SP`, `X18`, `X28`, `X29`, `FPCR`, `TPIDR_EL0`, `DCZID_EL0` kept,
memory changed only in the callee's stack window; `FPSR`, the flags, the SIMD registers, the
other registers and the exclusive monitor unspecified. -/
def SoftRet (n : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r v fl fp m ex ep, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, fpsr := fp,
                                      mem := m, pc := s.regs 30, excl := ex, exclPass := ep } ∧
    MemFrame s.mem m (rtWrites softEnv s n) ∧ P r

theorem SoftRet.intro (n : Nat) (s s' : State) (P : (Nat → W64) → Prop)
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hfr : MemFrame s.mem s'.mem (rtWrites softEnv s n)) (hp : P s'.regs) : SoftRet n s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, s'.excl, s'.exclPass, ?_, hfr, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- A call of a two-argument soft-float function: the runtime call frame and the Go `FPCR`. -/
def SoftPre (s : State) : Prop := RTPre softEnv 2 s ∧ s.fpcr = 0

/-- **`runtime.fadd64(f, g)`** (arm64; `X0 = f`, `X1 = g`, result `X0`): the IEEE sum (round to
nearest even; some NaN where IEEE has one), when the exact sum is not tiny. -/
def SoftFaddContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre s ∧ ¬ AddTiny (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => SoftRet 2 s s' fun r =>
      ResultIs binary64 (add binary64 .rne (s.regs 0).toNat (s.regs 1).toNat) (r 0).toNat)

/-- **`runtime.fsub64(f, g)`** (arm64): the IEEE difference, when the exact difference is not tiny. -/
def SoftFsubContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre s ∧ ¬ SubTiny (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => SoftRet 2 s s' fun r =>
      ResultIs binary64 (sub binary64 .rne (s.regs 0).toNat (s.regs 1).toNat) (r 0).toNat)

/-- **`runtime.fmul64(f, g)`** (arm64): the IEEE product, when the exact product is not tiny. -/
def SoftFmulContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre s ∧ ¬ MulTiny (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => SoftRet 2 s s' fun r =>
      ResultIs binary64 (mul binary64 .rne (s.regs 0).toNat (s.regs 1).toNat) (r 0).toNat)

/-- **`runtime.fdiv64(f, g)`** (arm64): the IEEE quotient, when the exact quotient is not tiny. -/
def SoftFdivContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr
    (fun s => SoftPre s ∧ ¬ DivTiny (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => SoftRet 2 s s' fun r =>
      ResultIs binary64 (div binary64 .rne (s.regs 0).toNat (s.regs 1).toNat) (r 0).toNat)

/-- **`runtime.KeepAlive(x any)`** (arm64; `X0, X1 = x`): returns, changing only the callee's
frame, when `runtime.cgoAlwaysFalse` (at `cgoFalse`) is `false` and not inside the callee's stack
window (the function stores its arguments there before it reads the global). -/
def KeepAliveContract (p : Program) (addr cgoFalse : Nat) : Prop :=
  Summary p addr
    (fun s => RTPre softEnv 2 s ∧ Misc.CgoAlwaysFalse s.mem cgoFalse ∧
      Spec.Disjoint cgoFalse 1 (s.sp.toNat - softDepth) (softDepth + 8 + 8 * 2))
    (fun s s' => SoftRet 2 s s' fun _ => True)

end Janus.Contracts.SoftFloat

import Janus.Contracts.Instrument
import Janus.Contracts.Map

/-!
# Instrumented builds: the `-d=checkptr` runtime checks, and the cgo pointer checks (arm64)

`go build -gcflags=-d=checkptr` (also implied by `-race` and `-msan`, which Janus rejects,
docs/CLI.md "Build modes") makes the compiler check unsafe pointer operations at run time:

| Go source | Runtime entry (Go 1.26, `runtime/checkptr.go`) | Contract |
| --- | --- | --- |
| `(*T)(p)`, `(*[n]T)(p)` for `p unsafe.Pointer` | `checkptrAlignment(p, type:T, n)` | `CheckptrAlignment` |
| `unsafe.Pointer(uintptr(p) + off)` and similar | `checkptrArithmetic(p, originals)` | `CheckptrArithmetic` |

Each check **returns** when the operation is valid and otherwise calls `throw` (a fatal error,
not a recoverable panic). The contracts state the return exactly under the runtime's own
conditions and exclude the throw:

* `checkptrAlignment(p, elem, n)`: `p = nil`; or, when `elem` has pointers, `p` is aligned to
  `elem.Align_`, and the `n·elem.Size_` bytes at `p` do not "straddle": one byte or less, no
  address overflow, and the same `checkptrBase` at the first and the last byte;
* `checkptrArithmetic(p, originals)`: `p` is not a small non-zero value (`0 < p < 4096`,
  `minLegalPointer`), and `checkptrBase(p)` is `0` (not Go memory) or the base of one of
  `originals`.

`checkptrBase(q)` is the start of the Go object holding `q` (a heap object through
`findObject`, the current goroutine's stack, a data or bss segment), or `0`. What the runtime
uses to compute it (the heap's spans, the module data, the goroutine's stack bounds `g.stack`) is
runtime state that a theorem cannot see; it is the model's abstract function `C.base m g q` of
the memory `m` and the goroutine `g`, with one law: it depends only on the runtime's memory
`C.priv` and the goroutine's `stack` field (the first 16 bytes of `g`). A theorem quantifies over
every model `C : CheckptrModel` that satisfies its laws, so it holds for the real runtime as
soon as its `checkptrBase` is such a function, which it is.

**Frame.** As for the interface and map contracts: the call returns to `X30` with `SP`, `X18`,
`X28`, `X29` preserved, every other register, the SIMD registers and the flags arbitrary,
memory changed only in `C.priv`, the `C.depth` bytes below `SP` (never the caller's saved frame
pointer) and the argument spill slots; `C.Env` holds again (`RtEnv`, `RTPre`, `RTReturn`).
-/

namespace Janus.Contracts.Instrument

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts

/-! ## A runtime environment and its call frame (shared by the contracts of this file and of
`Janus.Contracts.Misc`) -/

/-- The part of the runtime a call into it needs: `Env m g` (it is usable in memory `m` by the
goroutine `g`), its private memory `priv` (the caller's data lies outside it) and the stack it
may use below `SP`, `depth`. -/
structure RtEnv where
  Env : Memory → W64 → Prop
  priv : List (Nat × Nat)
  depth : Nat

/-- The law of every `RtEnv`: the environment lives in the private memory. -/
structure RtEnv.Laws (E : RtEnv) : Prop where
  env_frame : ∀ m m' g, E.Env m g → Agrees m m' E.priv → E.Env m' g

/-- What a runtime call with `nargs` register arguments needs (arm64). -/
def RTPre (E : RtEnv) (nargs : Nat) (s : State) : Prop :=
  E.Env s.mem (s.regs 28) ∧ StackGuardOK s E.depth ∧ CallOK s E.depth nargs ∧
    Outside (s.sp.toNat - E.depth) (E.depth + 8 + 8 * nargs) E.priv

/-- The byte ranges a runtime call with `nargs` register arguments may write. -/
def rtWrites (E : RtEnv) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  E.priv ++ calleeStack s E.depth nargs

attribute [janus_exec, janus_post] rtWrites

/-- The return of a runtime call from `s` to `s'` (arm64), with the facts `P r m` about the
result registers `r` and the new memory `m`. -/
def RTReturn (E : RtEnv) (nargs : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) : Prop :=
  ∃ r v fl m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, mem := m,
                            pc := s.regs 30 } ∧
    MemFrame s.mem m (rtWrites E s nargs) ∧ E.Env m (s.regs 28) ∧ P r m

/-- What a caller needs to call the runtime from inside a frame of `frame` bytes below its `SP`,
with `above` bytes of its caller's frame it may write. -/
def CallerOK (E : RtEnv) (s : State) (frame above : Nat) : Prop :=
  E.Env s.mem (s.regs 28) ∧ StackGuardOK s (E.depth + frame) ∧ s.sp.toNat % 16 = 0 ∧
    8 ≤ E.depth ∧ E.depth + frame ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - (E.depth + frame)) (E.depth + frame + above) true = true ∧
    Outside (s.sp.toNat - (E.depth + frame)) (E.depth + frame + above) E.priv ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (E.depth + frame)) (E.depth + frame + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 E.priv

theorem RTPre.of_parts {E : RtEnv} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK E s frame above) (henv : E.Env S.mem (s.regs 28))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre E nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, -⟩ := hc
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨by rw [hg]; exact henv, ⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- `RTPre.of_parts` for a first call: the call state's memory differs from the caller's entry
memory only inside the caller's window. -/
theorem RTPre.of_caller {E : RtEnv} (hl : E.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK E s frame above)
    (hf : MemFrame s.mem S.mem [(s.sp.toNat - (E.depth + frame), s.sp.toNat + above)])
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : RTPre E nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hlr hlr' hfr hn

/-- A model implementation's return as `RTReturn`: the preserved registers and fields. -/
theorem RTReturn.intro (E : RtEnv) (nargs : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop)
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hfs : s'.fpsr = s.fpsr) (hfr : MemFrame s.mem s'.mem (rtWrites E s nargs))
    (henv : E.Env s'.mem (s.regs 28)) (hp : P s'.regs s'.mem)
    (hex : s'.excl = s.excl := by first | rfl | simp_all) (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) : RTReturn E nargs s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, henv, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 hex hep ⊢
  subst hsp hpc hdz htp hfc hfs hex hep
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-! ## `checkptrBase` and the checks -/

/-- The runtime around the pointer checks: its environment and `checkptrBase` (`base m g q`: the
start of the Go object holding `q` in memory `m` for the goroutine `g`, `0` if none). -/
structure CheckptrModel extends RtEnv where
  base : Memory → W64 → Nat → Nat

/-- The laws: the environment depends only on the runtime's memory, `checkptrBase` only on it and
the goroutine's stack bounds (`g.stack`, offsets 0–15). -/
structure CheckptrModel.Laws (C : CheckptrModel) : Prop where
  env : C.toRtEnv.Laws
  base_frame : ∀ m m' g, Agrees m m' (C.priv ++ [(g.toNat, g.toNat + 16)]) → C.base m' g = C.base m g

/-- `uintptr(a) - 1` as a mask (the runtime's `uintptr(elem.Align_) - 1`, wrapping at 0). -/
def alignMask (a : Nat) : Nat := (a + 2 ^ 64 - 1) % 2 ^ 64

/-- `elem.Align_` (offset 21 of `abi.Type`, one byte). -/
def typAlign (m : Memory) (typ : Nat) : Nat := m.readLE (typ + 21) 1

/-- `checkptrStraddles(p, size)` is false: at most one byte, no address overflow, and the first
and the last byte in the same object (`runtime/checkptr.go`). -/
def NoStraddle (C : CheckptrModel) (m : Memory) (g : W64) (p size : Nat) : Prop :=
  size ≤ 1 ∨ (p < 2 ^ 64 - (size - 1) ∧ C.base m g p = C.base m g (p + (size - 1)))

/-- `checkptrAlignment(p, elem, n)` returns (does not throw): `p = nil`, or `elem`'s `Size_`,
`PtrBytes` and `Align_` are readable, a pointerful `elem` is aligned, and the `n·Size_` bytes
(computed in `uintptr`, modulo `2^64`) do not straddle. -/
def AlignOK (C : CheckptrModel) (m : Memory) (g : W64) (p elem n : Nat) : Prop :=
  p = 0 ∨ (elem + 24 ≤ 2 ^ 48 ∧ m.accessible elem 24 false = true ∧
    (typPtrBytes m elem ≠ 0 → p &&& alignMask (typAlign m elem) = 0) ∧
    NoStraddle C m g p (n * typSize m elem % 2 ^ 64))

/-- **`runtime.checkptrAlignment(p, elem, n)`** (arm64; `X0 = p`, `X1 = elem`, `X2 = n`): returns
when the conversion `(*[n]elem)(p)` is valid (`AlignOK`); the throw is excluded. -/
def CheckptrAlignment (p : Program) (addr : Nat) (C : CheckptrModel) : Prop :=
  Summary p addr
    (fun s => RTPre C.toRtEnv 3 s ∧
      AlignOK C s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)
    (fun s s' => RTReturn C.toRtEnv 3 s s' fun _ _ => True)

/-- `minLegalPointer` (4096): smaller non-zero pointer values are bad. -/
def minLegalPointer : Nat := 4096

/-- `checkptrArithmetic(p, originals)` returns: `p` is not a small non-zero value, and
`checkptrBase(p)` is `0` or the base of one of the `len` readable `originals` at `orig`. -/
def ArithOK (C : CheckptrModel) (m : Memory) (g : W64) (p orig len : Nat) : Prop :=
  ¬ (0 < p ∧ p < minLegalPointer) ∧
    (C.base m g p = 0 ∨ (orig + 8 * len ≤ 2 ^ 48 ∧ m.accessible orig (8 * len) false = true ∧
      ∃ i, i < len ∧ C.base m g p = C.base m g (m.readLE (orig + 8 * i) 8)))

/-- **`runtime.checkptrArithmetic(p, originals)`** (arm64; `X0 = p`, `X1, X2, X3` the slice
`originals`): returns when the arithmetic result is valid (`ArithOK`); the throw is excluded. -/
def CheckptrArithmetic (p : Program) (addr : Nat) (C : CheckptrModel) : Prop :=
  Summary p addr
    (fun s => RTPre C.toRtEnv 4 s ∧
      ArithOK C s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)
    (fun s s' => RTReturn C.toRtEnv 4 s s' fun _ _ => True)

/-! ## The cgo pointer checks (`runtime/cgocall.go`)

cgo-generated Go code checks the Go values it passes to C (`_cgoCheckPointer(ptr, arg)`, before
`cgocall`, for every argument whose type holds pointers) and the results an exported Go function
returns to C (`_cgoCheckResult(val)`), by the rules of `cmd/cgo` ("Passing pointers"): C may not
receive a Go pointer to memory that holds unpinned Go pointers. Each check **returns** when the
value passes (or `GODEBUG=cgocheck=0`) and otherwise panics. Whether a value passes depends on the
runtime's heap metadata (spans, pinner bits, the type's GC data), so it is the model's abstract
predicate, and the panic is excluded: the contracts state the return under the check's success. -/

/-- The cgo pointer checks: `ok m g t v at av` when `cgoCheckPointer(ptr, arg)` passes for
`ptr = (t, v)` and `arg = (at, av)` (two interfaces; `at = 0` for a nil `arg`) in memory `m` and
goroutine `g`; `resOK m g t v` when `cgoCheckResult((t, v))` passes. -/
structure CgoCheckModel extends RtEnv where
  ok : Memory → W64 → Nat → Nat → Nat → Nat → Prop
  resOK : Memory → W64 → Nat → Nat → Prop

/-- **`runtime.cgoCheckPointer(ptr, arg any)`** (arm64; `X0, X1 = ptr`, `X2, X3 = arg`): returns
when the check passes (`C.ok`); the panic is excluded. -/
def CgoCheckPointer (p : Program) (addr : Nat) (C : CgoCheckModel) : Prop :=
  Summary p addr
    (fun s => RTPre C.toRtEnv 4 s ∧
      C.ok s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat)
    (fun s s' => RTReturn C.toRtEnv 4 s s' fun _ _ => True)

/-- **`runtime.cgoCheckResult(val any)`** (arm64; `X0, X1 = val`): returns when the check passes
(`C.resOK`); the panic is excluded. -/
def CgoCheckResult (p : Program) (addr : Nat) (C : CgoCheckModel) : Prop :=
  Summary p addr
    (fun s => RTPre C.toRtEnv 2 s ∧ C.resOK s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => RTReturn C.toRtEnv 2 s s' fun _ _ => True)

end Janus.Contracts.Instrument

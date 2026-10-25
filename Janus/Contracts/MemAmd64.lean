import Janus.Contracts.Mem
import Janus.Contracts.IfaceAmd64

/-!
# Contracts of the Go equality and typed-memory runtime (amd64)

The amd64 counterparts of `Janus.Contracts.Mem` (see that file and docs/RUNTIME-CONTRACTS.md,
"Equality, hashing and typed memory"): the same runtime entry points and results, stated with
the amd64 ABIInternal. Arguments are in `RAX`, `RBX`, `RCX` (`regs 0`, `regs 3`, `regs 1`), the
closure context in `RDX` (`regs 2`), the `bool` result in `AL`; `CALL` pushes the return address,
so the callee starts with `[RSP]` holding it and returns to it with `RSP + 8`; `RBP`, `R14`
(`g`), `X15` (zero), the direction flag, `FS` and the control bits of `MXCSR` are preserved,
every other general register, `X0`–`X14`, the upper `YMM` halves, the flags and the exception
bits of `MXCSR` (a comparison of a NaN or a denormal sets them) are arbitrary afterwards. A call
may write at most `d` bytes below `RSP` (never the return-address slot), the argument spill
slots `[RSP + 8, RSP + 8 + 8·nargs)` and, for the contracts over a model, the runtime's private
memory and the destination.

The ISA-independent definitions (`feq`, `strEq`, `MemModel`, `WriteBarrierOff`, `Copied`,
`Zeroed`) are those of `Janus.Contracts.Mem`. The floating-point contracts require Go's `MXCSR`
(`GoABI.GoMXCSR`: all exceptions masked, round to nearest, no `DAZ`/`FTZ`).
-/

namespace Janus.Contracts.MemAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts Janus.Contracts.Mem Janus.Float

/-! ## The common shape -/

/-- The callee's part of the stack window (amd64), `MapAmd64.calleeStack`. -/
abbrev calleeStack (s : State) (d nargs : Nat) : List (Nat × Nat) := MapAmd64.calleeStack s d nargs

/-- The ABI part of every precondition (amd64): an 8-aligned `RSP`, the window
`[RSP - d, RSP + 8 + 8·nargs)` writable and below `2^48`, `X15 = 0`, the direction flag clear,
and a canonical return address (below `2^47`) at `[RSP]`. -/
def CallOK (s : State) (d nargs : Nat) : Prop :=
  (s.regs 4).toNat % 8 = 0 ∧ d ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - d) (d + 8 + 8 * nargs) true = true ∧
    s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

/-- What every equality runtime call needs (amd64): the stack guard at least `d` bytes below
`RSP` and `CallOK`. -/
def EqPre (d nargs : Nat) (s : State) : Prop :=
  StackGuardOK s d ∧ CallOK s d nargs ∧ Outside ((s.regs 14).toNat + 16) 8 (calleeStack s d nargs)

/-- The state a runtime call returns in (amd64): `RSP + 8`, `RBP`, `R14` kept, the other general
registers from `r`, `X15` kept and `X0`–`X14` from `x`, the upper halves `y`, the flags `fl`,
`MXCSR` `mx`, memory `m`, at the return address. -/
def retState (s : State) (r : Nat → W64) (x y : Nat → BitVec 128) (fl : Flags) (mx : BitVec 32)
    (m : Janus.Arm64.Memory) : State :=
  { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x, ymmHi := y,
           flags := fl, mxcsr := mx, mem := m, rip := retAddrOf s }

attribute [janus64_exec, janus64_post] retState

/-- The return of an equality runtime call (amd64): `retState`, with the control bits of `MXCSR`
kept, memory changed only in the callee's window, and `P r`. -/
def EqRet (d nargs : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r x y fl mx m, s' = retState s r x y fl mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧
    MemFrame s.mem m (calleeStack s d nargs) ∧ P r

/-- An input of `n` bytes at `a` of a call at `s` (amd64). -/
def Input (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n false = true ∧ Outside a n (calleeStack s d nargs)

/-! ## `memequal` and the fixed-size equality functions -/

/-- **`runtime.memequal(a, b, n)`** (`RAX = a`, `RBX = b`, `RCX = n`): as `Mem.Memequal`. -/
def Memequal (p : Janus.Amd64.Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 0 s ∧ Input s d 0 (s.regs 0).toNat (s.regs 1).toNat ∧
      Input s d 0 (s.regs 3).toNat (s.regs 1).toNat)
    (fun s s' => EqRet d 0 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat (s.regs 1).toNat == s.mem.readLE (s.regs 3).toNat (s.regs 1).toNat))

/-- **`runtime.memequal0/8/16/32/64/128(a, b)`** (`RAX = a`, `RBX = b`; `n = 0, 1, 2, 4, 8, 16`). -/
def MemequalN (p : Janus.Amd64.Program) (addr d n : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat n ∧ Input s d 2 (s.regs 3).toNat n)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat n == s.mem.readLE (s.regs 3).toNat n))

/-- The size a `memequal_varlen` closure carries: the word at `8(RDX)`. -/
def varlenSize (s : State) : Nat := s.mem.readLE ((s.regs 2).toNat + 8) 8

/-- **`runtime.memequal_varlen(a, b)`** (`RAX = a`, `RBX = b`, the closure context `RDX`). -/
def MemequalVarlen (p : Janus.Amd64.Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ Input s d 2 ((s.regs 2).toNat + 8) 8 ∧
      Input s d 2 (s.regs 0).toNat (varlenSize s) ∧ Input s d 2 (s.regs 3).toNat (varlenSize s))
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat (varlenSize s) == s.mem.readLE (s.regs 3).toNat (varlenSize s)))

/-! ## Floating-point and complex equality -/

/-- **`runtime.f32equal`/`f64equal(a, b)`** (`Fequal binary32 4`, `Fequal binary64 8`). -/
def Fequal (p : Janus.Amd64.Program) (addr d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat k ∧
      Input s d 2 (s.regs 3).toNat k)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (feq f (s.mem.readLE (s.regs 0).toNat k) (s.mem.readLE (s.regs 3).toNat k)))

/-- **`runtime.c64equal`/`c128equal(a, b)`** (`Cequal binary32 4`, `Cequal binary64 8`). -/
def Cequal (p : Janus.Amd64.Program) (addr d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
      Input s d 2 (s.regs 3).toNat (2 * k))
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (feq f (s.mem.readLE (s.regs 0).toNat k) (s.mem.readLE (s.regs 3).toNat k) &&
        feq f (s.mem.readLE ((s.regs 0).toNat + k) k) (s.mem.readLE ((s.regs 3).toNat + k) k)))

/-! ## Strings and interfaces -/

/-- The string with the header at `h` is an input of the call at `s` (amd64). -/
def StrInput (s : State) (d nargs h : Nat) : Prop :=
  Input s d nargs h 16 ∧ Input s d nargs (strPtr s.mem h) (strLen s.mem h)

/-- **`runtime.strequal(a, b)`** (`RAX = a`, `RBX = b`, pointers to string headers): `strEq`. -/
def Strequal (p : Janus.Amd64.Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ StrInput s d 2 (s.regs 0).toNat ∧ StrInput s d 2 (s.regs 3).toNat)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r (strEq s.mem (s.regs 0).toNat (s.regs 3).toNat))

/-- What an `interequal`/`nilinterequal` call needs of the interface model `R` (amd64). -/
def IfacePre (R : IfaceModel) (d : Nat) (s : State) : Prop :=
  R.Env s.mem (s.regs 14) ∧ StackGuardOK s d ∧ CallOK s d 2 ∧
    Outside ((s.regs 4).toNat - d) (d + 8 + 8 * 2) R.priv ∧
    Outside ((s.regs 14).toNat + 16) 8 (calleeStack s d 2)

/-- The return of an `interequal`/`nilinterequal` call (amd64). -/
def IfaceRet (R : IfaceModel) (d : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r x y fl mx m, s' = retState s r x y fl mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧
    MemFrame s.mem m (R.priv ++ calleeStack s d 2) ∧ R.Env m (s.regs 14) ∧ P r

/-- **`runtime.nilinterequal(a, b)`** (`RAX = a`, `RBX = b`): as `Mem.Nilinterequal`. -/
def Nilinterequal (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => IfacePre R d s ∧ Input s d 2 (s.regs 0).toNat 16 ∧ Input s d 2 (s.regs 3).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 →
        Iface.EqOK R s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
          (s.mem.readLE ((s.regs 3).toNat + 8) 8) ∧
        EqFrame R (s.mem.readLE (s.regs 0).toNat 8) s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8)
          (s.mem.readLE ((s.regs 3).toNat + 8) 8) (calleeStack s d 2)))
    (fun s s' => IfaceRet R d s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat 8 == s.mem.readLE (s.regs 3).toNat 8 &&
        Iface.efaceEqual R s.mem (s.mem.readLE (s.regs 0).toNat 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)))

/-- **`runtime.interequal(a, b)`** (`RAX = a`, `RBX = b`): as `Mem.Interequal`. -/
def Interequal (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => IfacePre R d s ∧ Input s d 2 (s.regs 0).toNat 16 ∧ Input s d 2 (s.regs 3).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 →
        s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        Outside (s.mem.readLE (s.regs 0).toNat 8) 16 R.priv ∧
        s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
        Iface.EqOK R s.mem (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) ∧
        EqFrame R (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8) s.mem
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)
          (calleeStack s d 2)))
    (fun s s' => IfaceRet R d s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat 8 == s.mem.readLE (s.regs 3).toNat 8 &&
        Iface.ifaceEqual R s.mem (s.mem.readLE (s.regs 0).toNat 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)))

/-! ## Typed memory -/

/-- What a typed-memory call needs (amd64): as `Mem.TPre`. -/
def TPre (M : MemModel) (wb d nargs : Nat) (s : State) : Prop :=
  M.Env s.mem (s.regs 14) ∧ StackGuardOK s d ∧ CallOK s d nargs ∧
    Outside ((s.regs 4).toNat - d) (d + 8 + 8 * nargs) M.priv ∧ Input s d nargs wb 4 ∧
    WriteBarrierOff s.mem wb ∧ Outside ((s.regs 14).toNat + 16) 8 (calleeStack s d nargs)

/-- The destination of a typed-memory call (amd64): as `Mem.Dest`, and also outside the
return-address slot `[RSP, RSP + 8)` (overwriting it would make the return impossible). -/
def Dest (M : MemModel) (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n true = true ∧ Outside a n (calleeStack s d nargs) ∧
    Outside a n M.priv ∧ Outside a n [((s.regs 4).toNat, (s.regs 4).toNat + 8)]

/-- The return of a typed-memory call (amd64). -/
def TRet (M : MemModel) (d nargs : Nat) (extra : List (Nat × Nat)) (s s' : State)
    (P : Janus.Arm64.Memory → Prop) : Prop :=
  ∃ r x y fl mx m, s' = retState s r x y fl mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧
    MemFrame s.mem m (M.priv ++ calleeStack s d nargs ++ extra) ∧ M.Env m (s.regs 14) ∧ P m

/-- **`runtime.typedmemmove(typ, dst, src)`** (`RAX = typ`, `RBX = dst`, `RCX = src`). -/
def TypedMemmove (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 3 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
      Outside (s.regs 0).toNat 16 (calleeStack s d 3) ∧
      Input s d 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) ∧
      Dest M s d 3 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => TRet M d 3 [((s.regs 3).toNat, (s.regs 3).toNat + typSize s.mem (s.regs 0).toNat)] s s'
      fun m => Copied s.mem m (s.regs 3).toNat (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.typedmemclr(typ, ptr)`** (`RAX = typ`, `RBX = ptr`). -/
def TypedMemclr (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 2 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
      Outside (s.regs 0).toNat 16 (calleeStack s d 2) ∧
      Dest M s d 2 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => TRet M d 2 [((s.regs 3).toNat, (s.regs 3).toNat + typSize s.mem (s.regs 0).toNat)] s s'
      fun m => Zeroed m (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.memclrHasPointers(ptr, n)`** (`RAX = ptr`, `RBX = n`, both multiples of 8). -/
def MemclrHasPointers (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
      Dest M s d 2 (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => TRet M d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 3).toNat)] s s'
      fun m => Zeroed m (s.regs 0).toNat (s.regs 3).toNat)

/-! ## The callees of the typed-memory functions -/

/-- **`runtime.memmove(dst, src, n)`** (`RAX = dst`, `RBX = src`, `RCX = n`). -/
def Memmove (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => M.Env s.mem (s.regs 14) ∧ EqPre d 3 s ∧
      Outside ((s.regs 4).toNat - d) (d + 8 + 8 * 3) M.priv ∧
      Input s d 3 (s.regs 3).toNat (s.regs 1).toNat ∧ Dest M s d 3 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => TRet M d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] s s'
      fun m => Copied s.mem m (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat)

/-- **`runtime.memclrNoHeapPointers(ptr, n)`** (`RAX = ptr`, `RBX = n`). -/
def MemclrNoHeapPointers (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => M.Env s.mem (s.regs 14) ∧ EqPre d 2 s ∧
      Outside ((s.regs 4).toNat - d) (d + 8 + 8 * 2) M.priv ∧
      Dest M s d 2 (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => TRet M d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 3).toNat)] s s'
      fun m => Zeroed m (s.regs 0).toNat (s.regs 3).toNat)

/-- **`runtime.bulkBarrierPreWrite(dst, src, size, typ)`** (`RAX`, `RBX`, `RCX`, `RDI`) with the
barrier off and `dst`, `src`, `size` multiples of 8: returns without changing anything but its
stack window. -/
def BulkBarrierOff (p : Janus.Amd64.Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 4 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
      (s.regs 1).toNat % 8 = 0)
    (fun s s' => TRet M d 4 [] s s' fun _ => True)

/-! ## Proof tools -/

/-- How a proof from a function's code ends (amd64): the final state keeps `RBP`, `R14`, `X15`,
`DF` and `FS`, has `RSP + 8` and the control bits of `MXCSR`, is at the return address, and its
memory and registers satisfy the contract; then it is `EqRet`. -/
theorem EqRet.intro {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (calleeStack s d nargs)) (hp : P s'.regs) : EqRet d nargs s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mxcsr, s'.mem, ?_, hmx, hf, hp⟩
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf ⊢
  subst hrip hfs hdf
  simp only [retState, State.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact hsp
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

end Janus.Contracts.MemAmd64

namespace Janus.Contracts.MemAmd64

open Janus Janus.Amd64 Janus.Float Janus.Contracts.Mem

/-! ## Floating-point comparison (amd64) -/

/-- `SETE AL; SETNP CL; ANDL CX, AX` (the compiled `==` on floats after `UCOMISS`/`UCOMISD`):
the low byte of the result is `ZF ∧ ¬PF`. -/
@[janus64_exec, janus64_post] theorem sete_setnp_and (a b : W64) (P Q : Prop) [Decidable P] [Decidable Q] :
    (BitVec.toNat (a &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (if P then 1#8 else 0#8)) % 4294967296 &&&
      BitVec.toNat (b &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (if Q then 0#8 else 1#8)) % 4294967296) % 256 =
    (decide P && !decide Q).toNat := by
  rw [show (256:Nat) = 2^8 from rfl, Nat.and_mod_two_pow, Nat.mod_mod_of_dvd _ (by decide : 2^8 ∣ 4294967296),
    Nat.mod_mod_of_dvd _ (by decide : 2^8 ∣ 4294967296), show (2:Nat)^8 = 256 from rfl,
    IfaceAmd64.setcc_low_byte, IfaceAmd64.setcc_low_byte]
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- `UCOMIS`/`COMIS` with Go's `MXCSR` controls: `ZF ∧ ¬PF` exactly for Go's `==` (`feq`). -/
@[janus64_exec, janus64_post] theorem comis_feq (sig : Bool) (f : Fmt) (a b : Nat) :
    (decide ((FP.comis sig f { rc := RM.rne, daz := false, ftz := false } a b).res / 4 % 2 = 1) &&
      !decide ((FP.comis sig f { rc := RM.rne, daz := false, ftz := false } a b).res / 2 % 2 = 1)) =
      feq f a b := by
  have hv : ∀ x, FP.valOf f { rc := RM.rne, daz := false, ftz := false } x = valueOf f x := by
    intro x; unfold FP.valOf FP.kindOf valueOf; cases h : classify f x <;> simp
  simp only [FP.comis, FP.relation, hv, feq]
  cases isNaN f a <;> cases isNaN f b <;> simp [FP.check]
  cases (valueOf f a).eq (valueOf f b) <;> cases (valueOf f a).lt (valueOf f b) <;> simp

end Janus.Contracts.MemAmd64

namespace Janus.Contracts.MemAmd64
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- What a Go function needs to call an equality runtime function with stack bound `d` with `RSP`
at `frame` bytes below its entry `RSP` at the callee's entry (its frame plus the pushed return
address), with `above` bytes from its entry `RSP` up it may write (its return address and argument
spill slots) (amd64): the stack guard at least `d + frame` below `RSP`, an 8-aligned `RSP`, the
window `[RSP - d - frame, RSP + above)` writable and below `2^48`, the guard word outside it. -/
def CallerOK (s : State) (d frame above : Nat) : Prop :=
  StackGuardOK s (d + frame) ∧ (s.regs 4).toNat % 8 = 0 ∧ d + frame ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - (d + frame)) (d + frame + above) true = true ∧
    Outside ((s.regs 14).toNat + 16) 8 [((s.regs 4).toNat - (d + frame), (s.regs 4).toNat + above)]

/-- The caller's window (amd64). -/
def callerWindow (s : State) (d frame above : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (d + frame), (s.regs 4).toNat + above)]

/-- `EqPre` at a call site `S` from the caller's `CallerOK` at its entry `s` (amd64). -/
theorem EqPre.of_caller {s S : State} {d frame above nargs : Nat} (hc : CallerOK s d frame above)
    (hf : MemFrame s.mem S.mem (callerWindow s d frame above))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : EqPre d nargs S := by
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout⟩ := hc
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [callerWindow, outside_cons, outside_nil, and_true] at hout hf
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hx, hdf, hra⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg, hsp]
    rw [hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [calleeStack, MapAmd64.calleeStack, outside_cons, outside_nil, and_true, hg, hsp]
    omega

/-- `Input` at a call site `S` (see `EqPre.of_caller`) of a range readable at the caller's entry
and outside the caller's window (amd64). -/
theorem Input.of_caller {s S : State} {d frame above nargs a n : Nat}
    (hf : MemFrame s.mem S.mem (callerWindow s d frame above))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame + above)
    (hfr : frame ≤ (s.regs 4).toNat)
    (hb : a + n ≤ 2 ^ 48) (hacc : s.mem.accessible a n false = true)
    (ho : Outside a n (callerWindow s d frame above)) : Input S d nargs a n := by
  simp only [callerWindow, outside_cons, outside_nil, and_true] at ho
  refine ⟨hb, by rw [hf.accessible]; exact hacc, ?_⟩
  simp only [calleeStack, MapAmd64.calleeStack, outside_cons, outside_nil, and_true, hsp]
  omega

end Janus.Contracts.MemAmd64

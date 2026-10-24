import Janus.GoABI

/-!
# The C calling convention on arm64 (AAPCS64, Linux), and `CEnsures`

Source of truth: *Procedure Call Standard for the Arm 64-bit Architecture* (AAPCS64, Arm IHI
0055), sections 6.1 (general-purpose registers), 6.4 (the stack) and 6.8 (parameter passing),
as used by GNU/Linux (the `aarch64-linux-gnu` ABI, which gcc and clang implement).

| Register | At call | At return | In body |
| --- | --- | --- | --- |
| `X0`–`X7` | integer and pointer arguments | `X0` (and `X1` for 128-bit) results | scratch |
| `X8` | indirect result location | scratch | scratch |
| `X9`–`X15` | scratch | scratch | scratch |
| `X16`, `X17` (`IP0`, `IP1`) | intra-procedure-call scratch (veneers, PLT) | scratch | scratch |
| `X18` | platform register; a temporary on Linux | scratch | scratch |
| `X19`–`X28` | callee-saved | **same** | must be restored |
| `X29` (`FP`) | frame pointer (frame record chain) | **same** | must be restored |
| `X30` (`LR`) | return address | | scratch after saving |
| `SP` | 16-byte aligned | **same** | 16-byte aligned at every access through it |

`V8`–`V15` (their low 64 bits) are also callee-saved in AAPCS64. No supported instruction of a C
integer function touches them in the code Janus proves (gcc only uses them for floating point
and vectorised loops), and the model has no floating point; `CReturn` therefore does not mention
them, and a proof about a C function that does use them has to state their preservation in its
own postcondition.

**Red zone.** AAPCS64 has none: memory below `SP` may be clobbered at any time (by a signal
handler), so C code never keeps live data there. The model has no signals, so this only means
that a C stack precondition (`CStack`) must cover every byte the code stores below `SP` — the
frames it pushes.

**Linux user space** adds: `SP` alignment checking is enabled (`SCTLR_EL1.SA0`, an access
through a misaligned `SP` faults; the model faults the same way), and `X18` is an ordinary
temporary (gcc may allocate it), unlike in Go's ABIInternal where it is never touched.

**What differs from Go's ABIInternal** (`Janus.GoABI`): eight argument registers instead of
sixteen; `X19`–`X28` are callee-saved (Go has no callee-saved general registers); `X28` is not
`g`; `X18` is not preserved; and there is no stack-growth prologue. A Go function that calls C
does so only through `runtime.cgocall` (see `Janus.FFI`), which saves and restores the Go state
around the C call.
-/

namespace Janus

open Arm64

namespace CABI

/-! ## Register roles -/

/-- Integer argument registers are `X0 .. X(numArgRegs-1)`. -/
def numArgRegs : Nat := 8
/-- The frame pointer. -/
abbrev regFP : Nat := 29
/-- The link register. -/
abbrev regLR : Nat := 30
/-- The callee-saved general registers `X19`–`X28` and the frame pointer `X29`. -/
def calleeSaved : List Nat := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-! ## Calls -/

/-- `s` is a state in which the C function at `entry` has just been called (`BL`) with integer
arguments `args`, returning to `p.exitAddr`: the Go-side `CallSetup` (`pc = entry`, `X30` the
return address, argument `i` in `Xi`), at most eight arguments, and `SP` 16-byte aligned (AAPCS64
6.4.5.1: "SP mod 16 = 0" at every public interface). Everything else (other registers, flags,
the SIMD&FP registers, memory) is arbitrary. Specifications use it with `p.withExit ret` for a
universally quantified admissible `ret` (`GoABI.RetAddr`). -/
structure CCall (p : Program) (entry : Nat) (args : List W64) (s : State) : Prop where
  call : GoABI.CallSetup p entry args s
  nargs : args.length ≤ numArgRegs
  spAligned : s.sp.toNat % 16 = 0

/-- What every AAPCS64 function must restore on return, relative to its call state `s₀`: `SP`
and the callee-saved registers `X19`–`X29`. -/
structure CReturn (s₀ s₁ : State) : Prop where
  sp : s₁.sp = s₀.sp
  x19 : s₁.regs 19 = s₀.regs 19
  x20 : s₁.regs 20 = s₀.regs 20
  x21 : s₁.regs 21 = s₀.regs 21
  x22 : s₁.regs 22 = s₀.regs 22
  x23 : s₁.regs 23 = s₀.regs 23
  x24 : s₁.regs 24 = s₀.regs 24
  x25 : s₁.regs 25 = s₀.regs 25
  x26 : s₁.regs 26 = s₀.regs 26
  x27 : s₁.regs 27 = s₀.regs 27
  x28 : s₁.regs 28 = s₀.regs 28
  fp : s₁.regs 29 = s₀.regs 29

/-- The C stack window: `SP` 16-aligned, and `[SP - below, SP + above)` writable and below
`2^48` (the frames the function and its callees push are below `SP`). -/
def CStack (s : State) (below above : Nat) : Prop :=
  s.sp.toNat % 16 = 0 ∧ below ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - below) (below + above) true = true

/-- `n` bytes at `ptr` are readable (`w = false`) or writable (`w = true`) and below `2^48`. -/
def Buffer (s : State) (ptr : W64) (n : Nat) (w : Bool) : Prop :=
  ptr.toNat + n ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat n w = true

/-- The first `k` integer result registers. -/
def results (k : Nat) (s : State) : List W64 := (List.range k).map s.regs

/-! ## Specifications

`CEnsures` is the C analogue of `GoABI.Ensures`: for **every** admissible return address `ret`
and **every** C call state satisfying `pre`, the call returns to `ret` after finitely many steps
(never faulting), restores `SP` and the callee-saved registers (`CReturn`), and satisfies
`post s₀ s₁`. The outcome predicates (`Returns`, `Faults`, ...) are the ones of `Janus.GoABI`:
they are about the run of the program, not about Go. -/

def CEnsures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s, CCall (p.withExit ret) entry args s → pre s →
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s')

/-- `CEnsures` stated on the first `nres` result registers. -/
def CEnsuresResults (p : Program) (entry : Nat) (args : List W64) (nres : Nat)
    (pre : State → Prop) (post : List W64 → Prop) : Prop :=
  CEnsures p entry args pre (fun _ s' => post (results nres s'))

/-! ## Lemmas -/

section Lemmas

variable {p : Program} {s s' : State} {entry : Nat} {args : List W64}

theorem CReturn.refl (s : State) : CReturn s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CReturn.trans {s₀ s₁ s₂ : State} (h₁ : CReturn s₀ s₁) (h₂ : CReturn s₁ s₂) :
    CReturn s₀ s₂ :=
  ⟨h₂.sp.trans h₁.sp, h₂.x19.trans h₁.x19, h₂.x20.trans h₁.x20, h₂.x21.trans h₁.x21,
    h₂.x22.trans h₁.x22, h₂.x23.trans h₁.x23, h₂.x24.trans h₁.x24, h₂.x25.trans h₁.x25,
    h₂.x26.trans h₁.x26, h₂.x27.trans h₁.x27, h₂.x28.trans h₁.x28, h₂.fp.trans h₁.fp⟩

/-- `CReturn` as a conjunction of equations (for the post-processing simp set). -/
theorem cReturn_iff (s₀ s₁ : State) :
    CReturn s₀ s₁ ↔ s₁.sp = s₀.sp ∧ s₁.regs 19 = s₀.regs 19 ∧ s₁.regs 20 = s₀.regs 20 ∧
      s₁.regs 21 = s₀.regs 21 ∧ s₁.regs 22 = s₀.regs 22 ∧ s₁.regs 23 = s₀.regs 23 ∧
      s₁.regs 24 = s₀.regs 24 ∧ s₁.regs 25 = s₀.regs 25 ∧ s₁.regs 26 = s₀.regs 26 ∧
      s₁.regs 27 = s₀.regs 27 ∧ s₁.regs 28 = s₀.regs 28 ∧ s₁.regs 29 = s₀.regs 29 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩⟩

/-- Every callee-saved register is restored. -/
theorem CReturn.saved {s₀ s₁ : State} (h : CReturn s₀ s₁) {r : Nat} (hr : r ∈ calleeSaved) :
    s₁.regs r = s₀.regs r := by
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hr
  have := (cReturn_iff s₀ s₁).1 h
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [this]

theorem CEnsures.returns {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : CEnsures p entry args pre post) (hret : GoABI.RetAddr p ret)
    (hs : CCall (p.withExit ret) entry args s) (hpre : pre s) :
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s') := h ret hret s hs hpre

theorem CEnsures.mono {pre pre' : State → Prop} {post post' : State → State → Prop}
    (h : CEnsures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : CEnsures p entry args pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

/-- A canonical C call state built from any state `s`, with `SP` rounded down to 16 bytes
(used to show `CCall` is satisfiable). -/
def setup (p : Program) (entry : Nat) (args : List W64) (s : State) : State :=
  { GoABI.setup p entry args s with sp := BitVec.ofNat 64 (s.sp.toNat / 16 * 16) }

theorem setup_cCall (s : State) (h : args.length ≤ numArgRegs) :
    CCall p entry args (setup p entry args s) where
  call :=
    have h' : args.length ≤ GoABI.numIntRegs := by
      simp only [numArgRegs, GoABI.numIntRegs] at h ⊢; omega
    let hc := GoABI.setup_callSetup (p := p) (entry := entry) s h'
    ⟨hc.pc, hc.lr, hc.args⟩
  nargs := h
  spAligned := by
    simp only [setup, BitVec.toNat_ofNat]
    have := s.sp.isLt
    have h1 : s.sp.toNat / 16 * 16 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1]
    omega

end Lemmas

end CABI
end Janus

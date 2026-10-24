import Janus.Amd64.GoABI

/-!
# The C calling convention on amd64 (System V AMD64 psABI), and `CEnsures`

Source of truth: *System V Application Binary Interface, AMD64 Architecture Processor
Supplement* (version 1.0), sections 3.2.1 (registers and the stack frame), 3.2.2 (the stack
frame and the red zone) and 3.2.3 (parameter passing), as gcc and clang implement it on Linux.

| Register | At call | At return | In body |
| --- | --- | --- | --- |
| `RDI RSI RDX RCX R8 R9` | integer and pointer arguments 1–6 | | scratch |
| `RAX` | (number of vector arguments for varargs) | result | scratch |
| `RDX` | argument 3 | second result (128-bit values) | scratch |
| `R10`, `R11` | scratch (static chain, PLT) | scratch | scratch |
| `RBX`, `RBP`, `R12`–`R15` | callee-saved | **same** | must be restored |
| `RSP` | `RSP + 8` 16-byte aligned (`[RSP]` = return address) | entry value + 8 | |
| `RFLAGS.DF` | clear | **clear** | |
| `XMM0`–`XMM15` | floating-point arguments (not modelled here) | | scratch |

**The red zone.** The 128 bytes below `RSP` are reserved for the function: signal and interrupt
handlers do not modify them, so a leaf function may keep data there without moving `RSP`. In
the model there are no signals; the only consequence is that a C stack precondition (`CStack`)
must make every byte the code stores writable, including red-zone bytes below `RSP`.

**Not modelled:** the x87 control word and `MXCSR` (callee-saved control bits): no supported
instruction reads or writes them. A C function using floating point is outside the model.

**What differs from Go's ABIInternal** (`Janus.Amd64.GoABI`): different argument registers
(`RDI RSI RDX RCX R8 R9` instead of `RAX RBX RCX RDI RSI R8 R9 R10 R11`); `RBX`, `R12`–`R15` are
callee-saved (Go has none besides `RBP`); `R14` is not `g` and `X15` is not zero; the stack is
16-byte aligned at calls (`RSP ≡ 8 mod 16` at entry); no stack-growth prologue. Go reaches C only
through `runtime.cgocall` (see `Janus.Amd64.FFI`).
-/

namespace Janus.Amd64

namespace CABI

/-! ## Register roles -/

/-- The integer argument registers, in order: `RDI RSI RDX RCX R8 R9`. -/
def intArgRegs : List Nat := [7, 6, 2, 1, 8, 9]

def numArgRegs : Nat := 6

/-- The `i`-th integer argument register. -/
def argReg (i : Nat) : Nat := intArgRegs.getD i 0

/-- The integer result registers `RAX`, `RDX`. -/
def resultRegs : List Nat := [0, 2]

abbrev regSP : Nat := 4
abbrev regFP : Nat := 5

/-- The callee-saved general registers `RBX RBP R12 R13 R14 R15`. -/
def calleeSaved : List Nat := [3, 5, 12, 13, 14, 15]

/-- Size of the red zone below `RSP`. -/
def redZone : Nat := 128

/-! ## Calls -/

/-- `s` is a state in which the C function at `entry` has just been called (`CALL`) with
integer arguments `args`, returning to `p.exitAddr`: `RIP = entry`, the return address at
`[RSP]`, at most six arguments, argument `i` in `argReg i`, `RSP + 8` 16-byte aligned (psABI
3.2.2: "the value (%rsp + 8) is always a multiple of 16 when control is transferred to the
function entry point") and the direction flag clear (psABI 3.2.1). Everything else is arbitrary.
Specifications use it with `p.withExit ret` for a universally quantified admissible `ret`. -/
structure CCall (p : Program) (entry : Nat) (args : List W64) (s : State) : Prop where
  rip : s.rip = BitVec.ofNat 64 entry
  ret : s.mem.readLE (s.regs regSP).toNat 8 = p.exitAddr
  len : args.length ≤ numArgRegs
  args : ∀ i (h : i < args.length), s.regs (argReg i) = args[i]
  spAligned : (s.regs regSP).toNat % 16 = 8
  df : s.df = false

/-- What every System V function must restore on return, relative to its call state `s₀`:
`RSP` (popped past the return address), `RBX RBP R12 R13 R14 R15`, and a clear direction
flag. -/
structure CReturn (s₀ s₁ : State) : Prop where
  sp : s₁.regs regSP = s₀.regs regSP + 8
  rbx : s₁.regs 3 = s₀.regs 3
  rbp : s₁.regs 5 = s₀.regs 5
  r12 : s₁.regs 12 = s₀.regs 12
  r13 : s₁.regs 13 = s₀.regs 13
  r14 : s₁.regs 14 = s₀.regs 14
  r15 : s₁.regs 15 = s₀.regs 15
  df : s₁.df = false

/-- The C stack window: `RSP ≡ 8 mod 16`, and `[RSP - below, RSP + above)` writable and below
`2^48`; `above ≥ 8` covers the return address, `below` the frames pushed by the function and its
callees (and the red zone, if the code uses it). -/
def CStack (s : State) (below above : Nat) : Prop :=
  (s.regs regSP).toNat % 16 = 8 ∧ below ≤ (s.regs regSP).toNat ∧
    (s.regs regSP).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs regSP).toNat - below) (below + above) true = true

/-- The result registers `RAX`, `RDX` (the first `k` of them). -/
def results (k : Nat) (s : State) : List W64 := (resultRegs.take k).map s.regs

/-! ## Specifications -/

/-- The C contract: for **every** admissible return address `ret` and **every** C call state
with these arguments and `[RSP] = ret` satisfying `pre`, the call returns to `ret` (never
faulting), restores `RSP`, the callee-saved registers and `DF` (`CReturn`), and satisfies
`post s₀ s₁`. -/
def CEnsures (p : Program) (entry : Nat) (args : List W64) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s, CCall (p.withExit ret) entry args s → pre s →
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s')

def CEnsuresResults (p : Program) (entry : Nat) (args : List W64) (nres : Nat)
    (pre : State → Prop) (post : List W64 → Prop) : Prop :=
  CEnsures p entry args pre (fun _ s' => post (results nres s'))

/-! ## Lemmas -/

section Lemmas

variable {p : Program} {s s' : State} {entry : Nat} {args : List W64}

theorem CCall.rip_toNat (h : CCall p entry args s) (he : entry < 2 ^ 64) :
    s.rip.toNat = entry := by
  rw [h.rip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem CCall.reg (h : CCall p entry args s) {i : Nat} (hi : i < args.length) :
    s.regs (argReg i) = args[i] := h.args i hi

/-- `CReturn` as a conjunction of equations (for the post-processing simp set). -/
theorem cReturn_iff (s₀ s₁ : State) :
    CReturn s₀ s₁ ↔ s₁.regs 4 = s₀.regs 4 + 8 ∧ s₁.regs 3 = s₀.regs 3 ∧ s₁.regs 5 = s₀.regs 5 ∧
      s₁.regs 12 = s₀.regs 12 ∧ s₁.regs 13 = s₀.regs 13 ∧ s₁.regs 14 = s₀.regs 14 ∧
      s₁.regs 15 = s₀.regs 15 ∧ s₁.df = false :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
    fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-- Every callee-saved register is restored. -/
theorem CReturn.saved {s₀ s₁ : State} (h : CReturn s₀ s₁) {r : Nat} (hr : r ∈ calleeSaved) :
    s₁.regs r = s₀.regs r := by
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hr
  have := (cReturn_iff s₀ s₁).1 h
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [this]

theorem CEnsures.returns {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : CEnsures p entry args pre post) (hret : GoABI.RetAddr p ret)
    (hs : CCall (p.withExit ret) entry args s) (hpre : pre s) :
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s') := h ret hret s hs hpre

theorem CEnsures.mono {pre pre' : State → Prop} {post post' : State → State → Prop}
    (h : CEnsures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : CEnsures p entry args pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

end Lemmas

end CABI
end Janus.Amd64

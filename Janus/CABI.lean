import Janus.GoABI
import Janus.Tactic.Basic
import Janus.CABI.AAPCS64

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

`V8`–`V15` are callee-saved in their low 64 bits (`D8`–`D15`, AAPCS64 6.1.2): `CReturn.v8`
… `CReturn.v15`; their upper halves and `V0`–`V7`, `V16`–`V31` are not. `FPCR` is preserved
(`CReturn.fpcr`), `FPSR` is not (its cumulative exception flags are sticky).

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
  /-- `FPCR` (rounding mode, flush-to-zero, default NaN, trap enables) is preserved across a
  call (AAPCS64); `FPSR`'s cumulative exception flags are not. -/
  fpcr : s₁.fpcr = s₀.fpcr
  /-- The low 64 bits of `V8`–`V15` (`D8`–`D15`) are callee-saved (AAPCS64 6.1.2). -/
  v8 : (s₁.vregs 8).toNat % 2 ^ 64 = (s₀.vregs 8).toNat % 2 ^ 64
  v9 : (s₁.vregs 9).toNat % 2 ^ 64 = (s₀.vregs 9).toNat % 2 ^ 64
  v10 : (s₁.vregs 10).toNat % 2 ^ 64 = (s₀.vregs 10).toNat % 2 ^ 64
  v11 : (s₁.vregs 11).toNat % 2 ^ 64 = (s₀.vregs 11).toNat % 2 ^ 64
  v12 : (s₁.vregs 12).toNat % 2 ^ 64 = (s₀.vregs 12).toNat % 2 ^ 64
  v13 : (s₁.vregs 13).toNat % 2 ^ 64 = (s₀.vregs 13).toNat % 2 ^ 64
  v14 : (s₁.vregs 14).toNat % 2 ^ 64 = (s₀.vregs 14).toNat % 2 ^ 64
  v15 : (s₁.vregs 15).toNat % 2 ^ 64 = (s₀.vregs 15).toNat % 2 ^ 64

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
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

theorem CReturn.trans {s₀ s₁ s₂ : State} (h₁ : CReturn s₀ s₁) (h₂ : CReturn s₁ s₂) :
    CReturn s₀ s₂ :=
  ⟨h₂.sp.trans h₁.sp, h₂.x19.trans h₁.x19, h₂.x20.trans h₁.x20, h₂.x21.trans h₁.x21,
    h₂.x22.trans h₁.x22, h₂.x23.trans h₁.x23, h₂.x24.trans h₁.x24, h₂.x25.trans h₁.x25,
    h₂.x26.trans h₁.x26, h₂.x27.trans h₁.x27, h₂.x28.trans h₁.x28, h₂.fp.trans h₁.fp,
    h₂.fpcr.trans h₁.fpcr, h₂.v8.trans h₁.v8, h₂.v9.trans h₁.v9, h₂.v10.trans h₁.v10,
    h₂.v11.trans h₁.v11, h₂.v12.trans h₁.v12, h₂.v13.trans h₁.v13, h₂.v14.trans h₁.v14,
    h₂.v15.trans h₁.v15⟩

/-- `CReturn` as a conjunction of equations (for the post-processing simp set). -/
theorem cReturn_iff (s₀ s₁ : State) :
    CReturn s₀ s₁ ↔ s₁.sp = s₀.sp ∧ s₁.regs 19 = s₀.regs 19 ∧ s₁.regs 20 = s₀.regs 20 ∧
      s₁.regs 21 = s₀.regs 21 ∧ s₁.regs 22 = s₀.regs 22 ∧ s₁.regs 23 = s₀.regs 23 ∧
      s₁.regs 24 = s₀.regs 24 ∧ s₁.regs 25 = s₀.regs 25 ∧ s₁.regs 26 = s₀.regs 26 ∧
      s₁.regs 27 = s₀.regs 27 ∧ s₁.regs 28 = s₀.regs 28 ∧ s₁.regs 29 = s₀.regs 29 ∧
      s₁.fpcr = s₀.fpcr ∧
      (s₁.vregs 8).toNat % 2 ^ 64 = (s₀.vregs 8).toNat % 2 ^ 64 ∧
      (s₁.vregs 9).toNat % 2 ^ 64 = (s₀.vregs 9).toNat % 2 ^ 64 ∧
      (s₁.vregs 10).toNat % 2 ^ 64 = (s₀.vregs 10).toNat % 2 ^ 64 ∧
      (s₁.vregs 11).toNat % 2 ^ 64 = (s₀.vregs 11).toNat % 2 ^ 64 ∧
      (s₁.vregs 12).toNat % 2 ^ 64 = (s₀.vregs 12).toNat % 2 ^ 64 ∧
      (s₁.vregs 13).toNat % 2 ^ 64 = (s₀.vregs 13).toNat % 2 ^ 64 ∧
      (s₁.vregs 14).toNat % 2 ^ 64 = (s₀.vregs 14).toNat % 2 ^ 64 ∧
      (s₁.vregs 15).toNat % 2 ^ 64 = (s₀.vregs 15).toNat % 2 ^ 64 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q, r, t, u, v, w⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q, r, t, u, v, w⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q, r, t, u, v, w⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q, r, t, u, v, w⟩⟩

/-- Every callee-saved register is restored. -/
theorem CReturn.saved {s₀ s₁ : State} (h : CReturn s₀ s₁) {r : Nat} (hr : r ∈ calleeSaved) :
    s₁.regs r = s₀.regs r := by
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hr
  have := (cReturn_iff s₀ s₁).1 h
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [this]

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


/-! ## Classified calls: every argument and result class

`CCall` above is the integer-register special case. `CCallA p entry sig vals s` is the general
AAPCS64 call state for a prototype `sig` (`Janus.C.AAPCS64.Sig`) and argument values `vals`
(each the little-endian bytes of the C object, `vals[i] < 2^(8·sizeof)`): every argument is
where the classification `sig.passing` (`Janus.C.AAPCS64.assignAll`) puts it — the low bytes of
`X0`–`X7`, the low bytes of `V0`–`V7` (one member of a homogeneous aggregate per register), the
stacked-argument area at `SP`, or (rule B.4) a pointer to a caller-made copy — and, for a result
returned in memory, `X8` holds the address of a writable result buffer. The same state serves a
variadic callee (on Linux, variadic arguments are passed as named ones). Register bytes above a
piece, and the stack bytes of a slot above the value, are unspecified (AAPCS64 does not define
them; a callee may not rely on them). `ResultAt` reads a result back, `CEnsuresA`/`CEnsuresR`
are the contracts. -/

open Janus.C

/-- Bytes `[src, src + len)` of the little-endian value `v`. -/
def bytesOf (v src len : Nat) : Nat := v / 256 ^ src % 256 ^ len

/-- The piece `pc` of the value `v` is in place in `s` (a state at the call or at the return;
`.stack o` is `SP + o`). -/
def PieceAt (s : State) (v : Nat) (pc : Piece) : Prop :=
  match pc.loc with
  | .gpr r => (s.regs r).toNat % 256 ^ pc.len = bytesOf v pc.src pc.len
  | .vec r o => (s.vregs r).toNat / 256 ^ o % 256 ^ pc.len = bytesOf v pc.src pc.len
  | .stack o => s.sp.toNat + o + pc.len ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat + o) pc.len false = true ∧
      s.mem.readLE (s.sp.toNat + o) pc.len = bytesOf v pc.src pc.len
  | .x87 _ => False

/-- Every piece is in place. -/
def PiecesAt (s : State) (v : Nat) : List Piece → Prop
  | [] => True
  | pc :: ps => PieceAt s v pc ∧ PiecesAt s v ps

/-- The argument of type `t` with value `v` is passed as `p`; for a copy (`indirect`), the
pointer `q` at `l` addresses `sizeof t` writable bytes holding `v` (the callee may modify the
copy). -/
def ArgAt (s : State) (t : CType) (v : Nat) : Passing → Prop
  | .direct ps => PiecesAt s v ps
  | .indirect l => ∃ q, PieceAt s q ⟨0, 8, l⟩ ∧ q + CType.size t ≤ 2 ^ 48 ∧
      s.mem.accessible q (CType.size t) true = true ∧ s.mem.readLE q (CType.size t) = v

/-- All arguments are in place. -/
def ArgsAt (s : State) : List CType → List Nat → List Passing → Prop
  | t :: ts, v :: vs, p :: ps => ArgAt s t v p ∧ ArgsAt s ts vs ps
  | [], [], [] => True
  | _, _, _ => False

/-- A result returned in memory has a writable buffer of its size at `X8`. -/
def RetBuf (s : State) (sig : AAPCS64.Sig) : Prop :=
  ∀ t, sig.ret = some t → AAPCS64.result t = .indirect (.gpr 8) →
    Buffer s (s.regs 8) (CType.size t) true

/-- The general AAPCS64 call state: the C function at `entry` has just been called with
prototype `sig` and argument values `vals`, returning to `p.exitAddr` (see the section
comment). -/
structure CCallA (p : Program) (entry : Nat) (sig : AAPCS64.Sig) (vals : List Nat) (s : State) :
    Prop where
  pc : s.pc = BitVec.ofNat 64 entry
  lr : s.regs GoABI.regLR = BitVec.ofNat 64 p.exitAddr
  spAligned : s.sp.toNat % 16 = 0
  args : ArgsAt s sig.args vals sig.passing
  retBuf : RetBuf s sig

/-- The result `v` of type `t`, passed as `p`, is returned in `s₁` by the call made in `s₀`:
in its registers, or in the buffer whose address `X8` held at the call. -/
def ResultAt (s₀ s₁ : State) (t : CType) (v : Nat) : Passing → Prop
  | .direct ps => PiecesAt s₁ v ps
  | .indirect _ => s₁.mem.readLE (s₀.regs 8).toNat (CType.size t) = v

/-- `v` is the result of the call (any `v` for `void`). -/
def Returned (sig : AAPCS64.Sig) (s₀ s₁ : State) (v : Nat) : Prop :=
  match sig.ret with
  | none => True
  | some t => ResultAt s₀ s₁ t v (AAPCS64.result t)

/-- The C contract for a classified call: for every admissible return address and every
`CCallA` state satisfying `pre`, the call returns, restores what AAPCS64 requires (`CReturn`)
and satisfies `post`. -/
def CEnsuresA (p : Program) (entry : Nat) (sig : AAPCS64.Sig) (vals : List Nat)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s, CCallA (p.withExit ret) entry sig vals s → pre s →
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s')

/-- `CEnsuresA` with the result: `post s s' v` for the value `v` the call returns. -/
def CEnsuresR (p : Program) (entry : Nat) (sig : AAPCS64.Sig) (vals : List Nat)
    (pre : State → Prop) (post : State → State → Nat → Prop) : Prop :=
  CEnsuresA p entry sig vals pre (fun s s' => ∃ v, Returned sig s s' v ∧ post s s' v)

section Classified

/-- The low `k` bytes of a two-part value `x + 256^k·y` (a struct of two members, `x` first). -/
theorem bytesOf_lo (x y k : Nat) (hx : x < 256 ^ k) : bytesOf (x + 256 ^ k * y) 0 k = x := by
  simp only [bytesOf, Nat.pow_zero, Nat.div_one]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- The bytes from `k` on of a two-part value `x + 256^k·y`. -/
theorem bytesOf_hi (x y k m : Nat) (hx : x < 256 ^ k) : bytesOf (x + 256 ^ k * y) k m = y % 256 ^ m := by
  simp only [bytesOf]
  have hk : 0 < 256 ^ k := Nat.pow_pos (by decide)
  rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hx, Nat.zero_add]

/-- The bytes of a 16-byte struct of two 8-byte members `x`, `y` (`x` first). -/
def pair (x y : BitVec 64) : Nat := x.toNat + 2 ^ 64 * y.toNat

theorem pair_lt (x y : BitVec 64) : pair x y < 2 ^ 128 := by
  have := x.isLt; have := y.isLt; simp only [pair]; omega

theorem bytesOf_pair_lo (x y : BitVec 64) : bytesOf (pair x y) 0 8 = x.toNat :=
  bytesOf_lo x.toNat y.toNat 8 x.isLt

theorem bytesOf_pair_hi (x y : BitVec 64) : bytesOf (pair x y) 8 8 = y.toNat := by
  rw [pair, show (2 : Nat) ^ 64 = 256 ^ 8 from rfl, bytesOf_hi _ _ _ _ x.isLt]
  exact Nat.mod_eq_of_lt y.isLt

/-- A 32-byte read as four 8-byte words (a 32-byte struct of 8-byte members). -/
theorem readLE_32 (m : Memory) (a : Nat) : m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
    2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc, Nat.reducePow, Nat.reduceAdd]
  omega

/-- A 16-byte read as two 8-byte words. -/
theorem readLE_16 (m : Memory) (a : Nat) :
    m.readLE a 16 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 := by
  rw [show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]

/-- Reading back the first member of a 16-byte struct of two 8-byte members just stored. -/
theorem readLE_writeLE_pair_lo (m : Memory) (a b : Nat) (x y : BitVec 64) (h : b = a) :
    (m.writeLE a 16 (pair x y)).readLE b 8 = x.toNat := by
  subst h
  rw [Janus.Arm64.Memory.readLE_writeLE_inside (m := m) (a := b) (n := 16) (b := b) (k := 8) _ (Nat.le_refl _) (by omega)]
  have := bytesOf_pair_lo x y
  simp only [bytesOf] at this
  simpa using this

/-- … and its second member. -/
theorem readLE_writeLE_pair_hi (m : Memory) (a b : Nat) (x y : BitVec 64) (h : b = a + 8) :
    (m.writeLE a 16 (pair x y)).readLE b 8 = y.toNat := by
  subst h
  rw [Janus.Arm64.Memory.readLE_writeLE_inside (m := m) (a := a) (n := 16) (b := a + 8) (k := 8) _ (by omega) (by omega)]
  have := bytesOf_pair_hi x y
  simp only [bytesOf] at this
  simpa using this

/-- All bytes of a value of `k` bytes. -/
theorem bytesOf_all (x k : Nat) (hx : x < 256 ^ k) : bytesOf x 0 k = x := by
  simp only [bytesOf, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hx]

variable {p : Program} {s : State} {entry : Nat}

theorem piecesAt_cons (s : State) (v : Nat) (pc : Piece) (ps : List Piece) :
    PiecesAt s v (pc :: ps) ↔ PieceAt s v pc ∧ PiecesAt s v ps := Iff.rfl

theorem argsAt_cons (s : State) (t : CType) (ts : List CType) (v : Nat) (vs : List Nat)
    (q : Passing) (qs : List Passing) :
    ArgsAt s (t :: ts) (v :: vs) (q :: qs) ↔ ArgAt s t v q ∧ ArgsAt s ts vs qs := Iff.rfl

/-- A piece in a general register, as an equation on the register's low bytes. -/
theorem pieceAt_gpr (s : State) (v r src len : Nat) :
    PieceAt s v ⟨src, len, .gpr r⟩ ↔ (s.regs r).toNat % 256 ^ len = bytesOf v src len := Iff.rfl

/-- A whole 64-bit integer in a general register. -/
theorem pieceAt_gpr_word (s : State) (r : Nat) (x : BitVec 64) :
    PieceAt s x.toNat ⟨0, 8, .gpr r⟩ ↔ s.regs r = x := by
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have h1 := (s.regs r).isLt
    have h2 := x.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    exact h
  · intro h; rw [h]

/-- A whole 64-bit value in the stacked-argument area. -/
theorem pieceAt_stack_word (s : State) (o : Nat) (x : BitVec 64) :
    PieceAt s x.toNat ⟨0, 8, .stack o⟩ ↔ s.sp.toNat + o + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.sp.toNat + o) 8 false = true ∧ s.mem.readLE (s.sp.toNat + o) 8 = x.toNat := by
  simp only [PieceAt, bytesOf, Nat.pow_zero, Nat.div_one]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega)]

/-- A double (or any 64-bit value) in the low half of a SIMD&FP register. -/
theorem pieceAt_vec_d (s : State) (r : Nat) (x : BitVec 64) :
    PieceAt s x.toNat ⟨0, 8, .vec r 0⟩ ↔ (s.vregs r).toNat % 2 ^ 64 = x.toNat := by
  show (s.vregs r).toNat / 256 ^ 0 % 256 ^ 8 = x.toNat / 256 ^ 0 % 256 ^ 8 ↔ _
  have := x.isLt
  rw [Nat.pow_zero, Nat.div_one, Nat.div_one, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl,
    Nat.mod_eq_of_lt (a := x.toNat) this]

/-- A float (or any 32-bit value) in the low bytes of a SIMD&FP register. -/
theorem pieceAt_vec_s (s : State) (r : Nat) (x : BitVec 32) :
    PieceAt s x.toNat ⟨0, 4, .vec r 0⟩ ↔ (s.vregs r).toNat % 2 ^ 32 = x.toNat := by
  show (s.vregs r).toNat / 256 ^ 0 % 256 ^ 4 = x.toNat / 256 ^ 0 % 256 ^ 4 ↔ _
  have := x.isLt
  rw [Nat.pow_zero, Nat.div_one, Nat.div_one, show (256 : Nat) ^ 4 = 2 ^ 32 by rfl,
    Nat.mod_eq_of_lt (a := x.toNat) this]

/-- One 64-bit integer argument when `NGRN = k < 8`: `X[k]`. -/
theorem assign_int8 (k : Nat) (hk : k < 8) :
    AAPCS64.assign { ngrn := k } (.int 8 true) = (.direct [⟨0, 8, .gpr k⟩], { ngrn := k + 1 }) := by
  have hk1 : k + 1 ≤ 8 := by omega
  simp [AAPCS64.assign, CType.hfa, CType.hfaCand, AAPCS64.byRef, CType.isAggregate,
    AAPCS64.gprOrStack, CType.size, CType.align, hk1]

theorem argsAt_ints (s : State) : ∀ (k : Nat) (xs : List W64), k + xs.length ≤ 8 →
    (ArgsAt s (xs.map fun _ => .int 8 true) (xs.map BitVec.toNat)
        (AAPCS64.assignAll { ngrn := k } (xs.map fun _ => .int 8 true)).1 ↔
      ∀ i (hi : i < xs.length), s.regs (k + i) = xs[i])
  | k, [], _ => by simp [ArgsAt, AAPCS64.assignAll]
  | k, x :: xs, hk => by
    simp only [List.length_cons] at hk
    simp only [List.map_cons, AAPCS64.assignAll, assign_int8 k (by omega)]
    rw [argsAt_cons, argsAt_ints s (k + 1) xs (by omega)]
    simp only [ArgAt, PiecesAt, and_true, pieceAt_gpr_word]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := hr i (by simp at hi; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · intro hr
      have h0 := hr 0 (by simp)
      rw [List.getElem_cons_zero, Nat.add_zero] at h0
      refine ⟨h0, fun i hi => ?_⟩
      have := hr (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- One 64-bit integer when the general registers are used up: the next stacked slot. -/
theorem assign_int8_stack (nsrn o : Nat) (ho : o % 8 = 0) :
    AAPCS64.assign ⟨8, nsrn, o⟩ (.int 8 true) =
      (.direct [⟨0, 8, .stack o⟩], ⟨8, nsrn, o + 8⟩) := by
  have hr : (o + 7) / 8 * 8 = o := by omega
  simp [AAPCS64.assign, CType.hfa, CType.hfaCand, AAPCS64.byRef, CType.isAggregate,
    AAPCS64.gprOrStack, CType.size, CType.align, hr, CType.roundUp]

/-- One 64-bit integer when `NGRN = k < 8` (any `NSRN`, `NSAA`). -/
theorem assign_int8' (k nsrn o : Nat) (hk : k < 8) :
    AAPCS64.assign ⟨k, nsrn, o⟩ (.int 8 true) = (.direct [⟨0, 8, .gpr k⟩], ⟨k + 1, nsrn, o⟩) := by
  have hk1 : k + 1 ≤ 8 := by omega
  simp [AAPCS64.assign, CType.hfa, CType.hfaCand, AAPCS64.byRef, CType.isAggregate,
    AAPCS64.gprOrStack, CType.size, CType.align, hk1]

/-- Where the `i`-th of a run of 64-bit integer arguments goes, from the state `st`: the next
general registers while they last, then consecutive 8-byte stacked slots. -/
def intLoc (st : AAPCS64.Next) (i : Nat) : Loc :=
  if st.ngrn + i < 8 then .gpr (st.ngrn + i) else .stack (st.nsaa + 8 * (st.ngrn + i - 8))

theorem intLoc_stack (st : AAPCS64.Next) (i : Nat) (h : 8 ≤ st.ngrn + i) :
    intLoc st i = .stack (st.nsaa + 8 * (st.ngrn + i - 8)) := by
  simp only [intLoc, show ¬ st.ngrn + i < 8 by omega, ↓reduceIte]

/-- Any number of 64-bit integer (or pointer) arguments, from a state with `NGRN ≤ 8` and an
8-aligned `NSAA`: the classification and its state predicate, as one statement per argument. -/
theorem argsAt_ints_gen (s : State) : ∀ (st : AAPCS64.Next) (xs : List W64),
    st.ngrn ≤ 8 → st.nsaa % 8 = 0 →
    (ArgsAt s (xs.map fun _ => .int 8 true) (xs.map BitVec.toNat)
        (AAPCS64.assignAll st (xs.map fun _ => .int 8 true)).1 ↔
      ∀ i (hi : i < xs.length), PieceAt s xs[i].toNat ⟨0, 8, intLoc st i⟩)
  | st, [], _, _ => by simp [ArgsAt, AAPCS64.assignAll]
  | ⟨k, nsrn, o⟩, x :: xs, hk, ho => by
    by_cases h8 : k < 8
    · simp only [List.map_cons, AAPCS64.assignAll, assign_int8' k nsrn o h8]
      rw [argsAt_cons, argsAt_ints_gen s ⟨k + 1, nsrn, o⟩ xs (by simp; omega) ho]
      simp only [ArgAt, PiecesAt, and_true]
      constructor
      · rintro ⟨h0, hr⟩ i hi
        cases i with
        | zero => simpa [intLoc, h8] using h0
        | succ i =>
          have := hr i (by simp at hi; omega)
          simpa [intLoc, Nat.add_assoc, Nat.add_comm 1 i] using this
      · intro hr
        have h0 := hr 0 (by simp)
        simp only [List.getElem_cons_zero, intLoc, Nat.add_zero, h8, ↓reduceIte] at h0
        refine ⟨h0, fun i hi => ?_⟩
        have := hr (i + 1) (by simp; omega)
        simpa [intLoc, Nat.add_assoc, Nat.add_comm 1 i] using this
    · have hk8 : k = 8 := by simp at hk; omega
      subst hk8
      simp only [List.map_cons, AAPCS64.assignAll, assign_int8_stack nsrn o ho]
      rw [argsAt_cons, argsAt_ints_gen s ⟨8, nsrn, o + 8⟩ xs (by simp) (by simp at ho ⊢; omega)]
      simp only [ArgAt, PiecesAt, and_true]
      constructor
      · rintro ⟨h0, hr⟩ i hi
        cases i with
        | zero => simpa [intLoc] using h0
        | succ i =>
          have := hr i (by simp at hi; omega)
          rw [intLoc_stack _ _ (by simp)] at this
          rw [intLoc_stack _ _ (by simp)]
          simp only [List.getElem_cons_succ]
          have e : o + 8 + 8 * (8 + i - 8) = o + 8 * (8 + (i + 1) - 8) := by omega
          simpa only [e] using this
      · intro hr
        have h0 := hr 0 (by simp)
        simp only [List.getElem_cons_zero, intLoc] at h0
        refine ⟨by simpa using h0, fun i hi => ?_⟩
        have := hr (i + 1) (by simp; omega)
        rw [intLoc_stack _ _ (by simp)] at this
        rw [intLoc_stack _ _ (by simp)]
        simp only [List.getElem_cons_succ] at this
        have e : o + 8 + 8 * (8 + i - 8) = o + 8 * (8 + (i + 1) - 8) := by omega
        simpa only [e] using this

/-- The integer-register call `CCall` is the classified call of a prototype of 64-bit integer
(or pointer) arguments with no indirect result. -/
theorem cCallA_iff_cCall (ret : Option CType) (args : List W64) (h : args.length ≤ numArgRegs)
    (hret : ∀ t, ret = some t → AAPCS64.result t ≠ .indirect (.gpr 8)) :
    CCallA p entry ⟨ret, args.map fun _ => .int 8 true, none⟩ (args.map BitVec.toNat) s ↔
      CCall p entry args s := by
  have hA := argsAt_ints s 0 args (by simp only [numArgRegs] at h; omega)
  simp only [Nat.zero_add] at hA
  have hrb : RetBuf s ⟨ret, args.map fun _ => .int 8 true, none⟩ := by
    intro t ht hi; exact absurd hi (hret t ht)
  constructor
  · intro hc
    exact ⟨⟨hc.pc, hc.lr, hA.1 hc.args⟩, h, hc.spAligned⟩
  · intro hc
    exact ⟨hc.call.pc, hc.call.lr, hc.spAligned, hA.2 hc.call.args, hrb⟩

/-- A `CEnsuresA` from a callee `Summary` (as `FFI.CEnsures.of_summary` for `CEnsures`). -/
theorem CEnsuresA.of_summary {sig : AAPCS64.Sig} {vals : List Nat}
    {pre spre : State → Prop} {post post' : State → State → Prop}
    (hsum : Janus.Tactic.Summary p entry spre post')
    (hpre : ∀ ret s, GoABI.RetAddr p ret → CCallA (p.withExit ret) entry sig vals s → pre s → spre s)
    (hpost : ∀ s s', pre s → post' s s' → CReturn s s' ∧ post s s') :
    CEnsuresA p entry sig vals pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.pc (hpre ret s hret hs hp)
  have hst' := hst.withExit hret.fetch_none
  refine GoABI.returns_of_steps hst' ?_ (hpost s s' hp hq)
  rw [hr, hs.lr]
  simp only [Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

theorem CEnsuresA.mono {sig : AAPCS64.Sig} {vals : List Nat} {pre pre' : State → Prop}
    {post post' : State → State → Prop} (h : CEnsuresA p entry sig vals pre post)
    (hpre : ∀ s, pre' s → pre s) (hpost : ∀ s s', pre' s → post s s' → post' s s') :
    CEnsuresA p entry sig vals pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

/-- `CReturn` from the equations a callee summary states (all SIMD&FP registers kept). -/
theorem CReturn.of_eqs {s₀ s₁ : State} (hsp : s₁.sp = s₀.sp) (h19 : s₁.regs 19 = s₀.regs 19)
    (h20 : s₁.regs 20 = s₀.regs 20) (h21 : s₁.regs 21 = s₀.regs 21) (h22 : s₁.regs 22 = s₀.regs 22)
    (h23 : s₁.regs 23 = s₀.regs 23) (h24 : s₁.regs 24 = s₀.regs 24) (h25 : s₁.regs 25 = s₀.regs 25)
    (h26 : s₁.regs 26 = s₀.regs 26) (h27 : s₁.regs 27 = s₀.regs 27) (h28 : s₁.regs 28 = s₀.regs 28)
    (h29 : s₁.regs 29 = s₀.regs 29) (hfc : s₁.fpcr = s₀.fpcr) (hv : s₁.vregs = s₀.vregs) :
    CReturn s₀ s₁ :=
  ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, by rw [hv], by rw [hv],
    by rw [hv], by rw [hv], by rw [hv], by rw [hv], by rw [hv], by rw [hv]⟩

/-- The return address of a `CCallA` state, as a callee `Summary` needs it. -/
theorem CCallA.lr_ok {sig : AAPCS64.Sig} {vals : List Nat} {ret : Nat} (hret : GoABI.RetAddr p ret)
    (hs : CCallA (p.withExit ret) entry sig vals s) :
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 := by
  have hlr := hs.lr
  simp only [Program.withExit, GoABI.regLR] at hlr
  rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]
  exact ⟨hret.aligned, by have := hret.user; omega⟩

/-- The bytes a list of pieces determines: if the pieces of `v` and of `w` are in place in the
same state and cover the same byte ranges, `v` and `w` agree on those bytes. -/
theorem PiecesAt.bytes_eq {s : State} {v w : Nat} :
    ∀ {ps : List Piece}, PiecesAt s v ps → PiecesAt s w ps →
      ∀ pc ∈ ps, bytesOf v pc.src pc.len = bytesOf w pc.src pc.len
  | [], _, _, _, h => by simp at h
  | pc :: ps, ⟨h1, hr⟩, ⟨h2, hr'⟩, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · unfold PieceAt at h1 h2
      split at h1 <;> simp_all
    · exact PiecesAt.bytes_eq hr hr' q hq

end Classified

end CABI
end Janus

import Janus.Amd64.GoABI
import Janus.Amd64.Tactic
import Janus.CABI.SysV

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
| `XMM0`–`XMM7` | SSE-class arguments (`CCallA`) | `XMM0`, `XMM1` SSE results | scratch |
| `XMM8`–`XMM15` | scratch | scratch | scratch |

**The red zone.** The 128 bytes below `RSP` are reserved for the function: signal and interrupt
handlers do not modify them, so a leaf function may keep data there without moving `RSP`. In
the model there are no signals; the only consequence is that a C stack precondition (`CStack`)
must make every byte the code stores writable, including red-zone bytes below `RSP`.

**Floating point:** the `MXCSR` control bits (bits 6 and up) are callee-saved
(`CReturn.mxcsr`), its status flags are not (they are sticky). The x87 control word is
callee-saved too (`CReturn.fpucw`; psABI 3.2.1: "the control bits of the MXCSR register and the
x87 control word are callee-saved"). No decoded instruction touches the x87 state, so the model
keeps it in every run; the x87 register stack itself, which must be empty at a call and holds a
`long double` result on return, is not modelled (WP-J).

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
  /-- The `MXCSR` control bits (rounding, masks, `FTZ`/`DAZ`: bits 6 and up) are callee-saved;
  the status flags (bits 0-5) are sticky and not. -/
  mxcsr : s₁.mxcsr.toNat / 64 = s₀.mxcsr.toNat / 64
  /-- The x87 control word is callee-saved. -/
  fpucw : s₁.fpucw = s₀.fpucw

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
      s₁.regs 15 = s₀.regs 15 ∧ s₁.df = false ∧ s₁.mxcsr.toNat / 64 = s₀.mxcsr.toNat / 64 ∧
      s₁.fpucw = s₀.fpucw :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩⟩

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


/-! ## Classified calls: every argument and result class

`CCall` above is the integer-register special case. `CCallA p entry sig vals s` is the general
System V call state for a prototype `sig` (`Janus.C.SysV.Sig`) and argument values `vals` (each
the little-endian bytes of the C object): every argument is where the classification
`sig.passing` (`Janus.C.SysV.assignAll`) puts it — the low bytes of an integer argument register
for each INTEGER eightbyte, of `XMM0`–`XMM7` for each SSE eightbyte (SSEUP: the upper half), or
the argument area at `RSP + 8` (MEMORY, x87, or not enough registers left for the whole
argument); a MEMORY result has a writable result buffer whose address is in `RDI` (the hidden
first argument); and a variadic call has in `AL` an upper bound, at most 8, on the vector
registers used (`Sig.vecRegs`). Register bytes above a piece and stack bytes above the value in
its slot are unspecified (the psABI leaves them undefined; gcc does not extend small integers,
clang assumes callers extend `_Bool`, `char` and `short` to 32 bits — a proof of a callee that
relies on it would need that as an extra hypothesis, which `CCallA` does not give). -/

open Janus.C

/-- Bytes `[src, src + len)` of the little-endian value `v`. -/
def bytesOf (v src len : Nat) : Nat := v / 256 ^ src % 256 ^ len

/-- The piece `pc` of the value `v` is in place in `s` (`.stack o` is `RSP + 8 + o`, above the
return address at a call). -/
def PieceAt (s : State) (v : Nat) (pc : Piece) : Prop :=
  match pc.loc with
  | .gpr r => (s.regs r).toNat % 256 ^ pc.len = bytesOf v pc.src pc.len
  | .vec r o => (s.xmm r).toNat / 256 ^ o % 256 ^ pc.len = bytesOf v pc.src pc.len
  | .stack o => (s.regs regSP).toNat + 8 + o + pc.len ≤ 2 ^ 48 ∧
      s.mem.accessible ((s.regs regSP).toNat + 8 + o) pc.len false = true ∧
      s.mem.readLE ((s.regs regSP).toNat + 8 + o) pc.len = bytesOf v pc.src pc.len
  | .x87 _ => False

def PiecesAt (s : State) (v : Nat) : List Piece → Prop
  | [] => True
  | pc :: ps => PieceAt s v pc ∧ PiecesAt s v ps

/-- The argument of type `t` with value `v` is passed as `p` (System V never passes a copy by
reference: `indirect` does not occur among arguments). -/
def ArgAt (s : State) (t : CType) (v : Nat) : Passing → Prop
  | .direct ps => PiecesAt s v ps
  | .indirect l => ∃ q, PieceAt s q ⟨0, 8, l⟩ ∧ q + CType.size t ≤ 2 ^ 48 ∧
      s.mem.accessible q (CType.size t) true = true ∧ s.mem.readLE q (CType.size t) = v

def ArgsAt (s : State) : List CType → List Nat → List Passing → Prop
  | t :: ts, v :: vs, p :: ps => ArgAt s t v p ∧ ArgsAt s ts vs ps
  | [], [], [] => True
  | _, _, _ => False

/-- A MEMORY result has a writable buffer of its size at `RDI`. -/
def RetBuf (s : State) (sig : SysV.Sig) : Prop :=
  ∀ t, sig.ret = some t → SysV.result t = .indirect (.gpr 7) →
    (s.regs 7).toNat + CType.size t ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 7).toNat (CType.size t) true = true

/-- `AL` for a variadic callee: an upper bound, at most 8, on the vector registers used. -/
def VarargAL (s : State) (sig : SysV.Sig) : Prop :=
  sig.named.isSome → sig.vecRegs ≤ (s.regs 0).toNat % 256 ∧ (s.regs 0).toNat % 256 ≤ 8

/-- The general System V call state (see the section comment). -/
structure CCallA (p : Program) (entry : Nat) (sig : SysV.Sig) (vals : List Nat) (s : State) :
    Prop where
  rip : s.rip = BitVec.ofNat 64 entry
  ret : s.mem.readLE (s.regs regSP).toNat 8 = p.exitAddr
  spAligned : (s.regs regSP).toNat % 16 = 8
  df : s.df = false
  args : ArgsAt s sig.args vals sig.passing
  retBuf : RetBuf s sig
  al : VarargAL s sig

/-- The result `v` of type `t`, passed as `p`, is returned in `s₁` by the call made in `s₀`:
in its registers, or (MEMORY) in the buffer whose address `RDI` held at the call, with that
address in `RAX`. An x87 result (`ST0`) cannot be stated: the x87 stack is not modelled. -/
def ResultAt (s₀ s₁ : State) (t : CType) (v : Nat) : Passing → Prop
  | .direct ps => PiecesAt s₁ v ps
  | .indirect _ => s₁.mem.readLE (s₀.regs 7).toNat (CType.size t) = v ∧ s₁.regs 0 = s₀.regs 7

def Returned (sig : SysV.Sig) (s₀ s₁ : State) (v : Nat) : Prop :=
  match sig.ret with
  | none => True
  | some t => ResultAt s₀ s₁ t v (SysV.result t)

/-- The C contract for a classified call. -/
def CEnsuresA (p : Program) (entry : Nat) (sig : SysV.Sig) (vals : List Nat)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s, CCallA (p.withExit ret) entry sig vals s → pre s →
    GoABI.Returns (p.withExit ret) s (fun s' => CReturn s s' ∧ post s s')

/-- `CEnsuresA` with the result. -/
def CEnsuresR (p : Program) (entry : Nat) (sig : SysV.Sig) (vals : List Nat)
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

/-- All bytes of a value of `k` bytes. -/
theorem bytesOf_all (x k : Nat) (hx : x < 256 ^ k) : bytesOf x 0 k = x := by
  simp only [bytesOf, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hx]

variable {p : Program} {s : State} {entry : Nat}

theorem argsAt_cons (s : State) (t : CType) (ts : List CType) (v : Nat) (vs : List Nat)
    (q : Passing) (qs : List Passing) :
    ArgsAt s (t :: ts) (v :: vs) (q :: qs) ↔ ArgAt s t v q ∧ ArgsAt s ts vs qs := Iff.rfl

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

theorem pieceAt_stack_word (s : State) (o : Nat) (x : BitVec 64) :
    PieceAt s x.toNat ⟨0, 8, .stack o⟩ ↔ (s.regs regSP).toNat + 8 + o + 8 ≤ 2 ^ 48 ∧
      s.mem.accessible ((s.regs regSP).toNat + 8 + o) 8 false = true ∧
      s.mem.readLE ((s.regs regSP).toNat + 8 + o) 8 = x.toNat := by
  show _ ∧ _ ∧ _ = x.toNat / 256 ^ 0 % 256 ^ 8 ↔ _
  rw [Nat.pow_zero, Nat.div_one, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl, Nat.mod_eq_of_lt x.isLt]

theorem pieceAt_vec_d (s : State) (r : Nat) (x : BitVec 64) :
    PieceAt s x.toNat ⟨0, 8, .vec r 0⟩ ↔ (s.xmm r).toNat % 2 ^ 64 = x.toNat := by
  show (s.xmm r).toNat / 256 ^ 0 % 256 ^ 8 = x.toNat / 256 ^ 0 % 256 ^ 8 ↔ _
  rw [Nat.pow_zero, Nat.div_one, Nat.div_one, show (256 : Nat) ^ 8 = 2 ^ 64 by rfl,
    Nat.mod_eq_of_lt (a := x.toNat) x.isLt]

theorem pieceAt_vec_s (s : State) (r : Nat) (x : BitVec 32) :
    PieceAt s x.toNat ⟨0, 4, .vec r 0⟩ ↔ (s.xmm r).toNat % 2 ^ 32 = x.toNat := by
  show (s.xmm r).toNat / 256 ^ 0 % 256 ^ 4 = x.toNat / 256 ^ 0 % 256 ^ 4 ↔ _
  rw [Nat.pow_zero, Nat.div_one, Nat.div_one, show (256 : Nat) ^ 4 = 2 ^ 32 by rfl,
    Nat.mod_eq_of_lt (a := x.toNat) x.isLt]

/-- One 64-bit integer argument when `k < 6` integer registers are used: `argReg k`. -/
theorem assign_int8 (k : Nat) (hk : k < 6) :
    SysV.assign { gp := k } (.int 8 true) =
      (.direct [⟨0, 8, .gpr (argReg k)⟩], { gp := k + 1 }) := by
  have hk1 : ¬ 6 < k + 1 := by omega
  simp [SysV.assign, SysV.classify, SysV.cls, SysV.scalarCls, CType.leaves, SysV.addLeaf,
    SysV.mergeAt, SysV.merge, SysV.inMemory, SysV.regPieces, CType.size, hk1, argReg,
    intArgRegs, SysV.intArgRegs]

theorem argsAt_ints (s : State) : ∀ (k : Nat) (xs : List W64), k + xs.length ≤ 6 →
    (ArgsAt s (xs.map fun _ => .int 8 true) (xs.map BitVec.toNat)
        (SysV.assignAll { gp := k } (xs.map fun _ => .int 8 true)).1 ↔
      ∀ i (hi : i < xs.length), s.regs (argReg (k + i)) = xs[i])
  | k, [], _ => by simp [ArgsAt, SysV.assignAll]
  | k, x :: xs, hk => by
    simp only [List.length_cons] at hk
    simp only [List.map_cons, SysV.assignAll, assign_int8 k (by omega)]
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

/-- The integer-register call `CCall` is the classified call of a non-variadic prototype of
64-bit integer (or pointer) arguments whose result is not MEMORY. -/
theorem cCallA_iff_cCall (ret : Option CType) (args : List W64) (h : args.length ≤ numArgRegs)
    (hret : ∀ t, ret = some t → ∀ l, SysV.result t ≠ .indirect l) :
    CCallA p entry ⟨ret, args.map fun _ => .int 8 true, none⟩ (args.map BitVec.toNat) s ↔
      CCall p entry args s := by
  have hst : (⟨ret, args.map fun _ => .int 8 true, none⟩ : SysV.Sig).start = {} := by
    unfold SysV.Sig.start
    cases ret with
    | none => rfl
    | some t =>
      show (match some (SysV.result t) with
        | some (.indirect _) => ({ gp := 1 } : SysV.Next) | _ => {}) = {}
      cases h : SysV.result t with
      | indirect l => exact absurd h (hret t rfl l)
      | direct ps => rfl
  have hA := argsAt_ints s 0 args (by simp only [numArgRegs] at h; omega)
  simp only [Nat.zero_add] at hA
  have hp : (⟨ret, args.map fun _ => .int 8 true, none⟩ : SysV.Sig).passing =
      (SysV.assignAll { gp := 0 } (args.map fun _ => .int 8 true)).1 := by
    simp only [SysV.Sig.passing, hst]
  have hrb : RetBuf s ⟨ret, args.map fun _ => .int 8 true, none⟩ := by
    intro t ht hi; exact absurd hi (hret t ht _)
  have hal : VarargAL s ⟨ret, args.map fun _ => .int 8 true, none⟩ := by
    intro h; simp at h
  constructor
  · intro hc
    exact ⟨hc.rip, hc.ret, h, hA.1 (hp ▸ hc.args), hc.spAligned, hc.df⟩
  · intro hc
    exact ⟨hc.rip, hc.ret, hc.spAligned, hc.df, hp ▸ hA.2 hc.args, hrb, hal⟩

theorem CEnsuresA.of_summary {sig : SysV.Sig} {vals : List Nat}
    {pre spre : State → Prop} {post post' : State → State → Prop}
    (hsum : Janus.Amd64.Tactic.Summary p entry spre post')
    (hpre : ∀ ret s, GoABI.RetAddr p ret → CCallA (p.withExit ret) entry sig vals s → pre s → spre s)
    (hpost : ∀ s s', pre s → post' s s' → CReturn s s' ∧ post s s') :
    CEnsuresA p entry sig vals pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.rip (hpre ret s hret hs hp)
  have hst' := hst.withExit hret.fetch_none
  refine GoABI.returns_of_steps hst' ?_ (hpost s s' hp hq)
  rw [hr, Janus.Amd64.Tactic.retAddrOf, hs.ret]
  simp only [Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

theorem CEnsuresA.mono {sig : SysV.Sig} {vals : List Nat} {pre pre' : State → Prop}
    {post post' : State → State → Prop} (h : CEnsuresA p entry sig vals pre post)
    (hpre : ∀ s, pre' s → pre s) (hpost : ∀ s s', pre' s → post s s' → post' s s') :
    CEnsuresA p entry sig vals pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

end Classified

end CABI
end Janus.Amd64

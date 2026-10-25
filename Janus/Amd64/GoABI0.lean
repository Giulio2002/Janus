import Janus.Amd64.GoABI
import Janus.Amd64.Tactic

/-!
# Go ABI0 on amd64: hand-written assembly, and the ABI wrappers

Source of truth: `$GOROOT/src/cmd/compile/abi-internal.md` ("ABI0", "Function call wrappers",
"amd64 architecture") and `$GOROOT/doc/asm.html` ("64-bit Intel 386 (a.k.a. amd64)"), checked
against Go 1.26.0 and the code it emits (`examples/asm`).

Every `TEXT ·f(SB)` of a Go assembly file is ABI0 and the linker names it `f.abi0`.

| | ABI0 (assembly) | ABIInternal (Go, `Janus.Amd64.GoABI`) |
| --- | --- | --- |
| arguments | the caller's frame: word `i` at `8+8i(RSP)` (`x+0(FP)`; `0(RSP)` is the return address) | `RAX RBX RCX RDI RSI R8 R9 R10 R11` |
| results | the caller's frame, after the arguments (pointer-aligned) | the same registers |
| `RAX`…`R15` but `RSP`/`RBP`, flags, `X0`–`X15` | caller-saved (scratch) | scratch, except `R14` and `X15` |
| `R14` | **scratch**: not `g` | `g`, preserved |
| `X15` | **scratch**: not zero | zero at calls and returns |
| `RBP` | frame pointer, preserved (the assembler pushes and pops it in a frame's prologue/epilogue) | preserved |
| `RSP` | `RSP + 8` on return (`RET` pops the return address) | same |
| `DF` | clear at calls and returns | clear at calls |

So an ABI0 function may leave anything in `R14` and `X15`, and the ABIInternal side restores
them after every ABI0 call (**re-entry**): the compiler emits

```
CALL f.abi0            // a direct ABI0 call, or inside the wrapper f
XORPS X15, X15         // X15 := 0
MOVQ  FS:-8, R14       // R14 := g, from the TLS slot runtime.tlsg
```

and the ABI0 → ABIInternal wrapper `g.abi0` of a Go function `g` called from assembly does the
same before its `CALL g`. `R14 = g` afterwards holds because the TLS slot holds `g`
(`GoABI.TlsG`, a precondition of every theorem that runs a re-entry sequence) and the ABI0 code
neither moves the `FS` base (no modelled instruction writes it; `ABIReturn0.fs` states it of the
callee) nor writes the slot (the callee's frame condition). `TlsG.reentry` is that argument as a
lemma.

## The arguments frame

As on arm64 (`Janus.GoABI0`): a frame is a list of 64-bit words, word `i` at `RSP + 8 + 8i` at
the entry, the `nres` result words after the argument words; `FrameOK` makes the whole frame
writable. All wrappers and direct calls are ordinary extracted machine code; nothing about them
is assumed. See docs/ABI0.md.
-/

namespace Janus.Amd64

open GoABI Janus.Amd64.Tactic

namespace GoABI0

/-! ## The frame -/

/-- Offset of argument word 0 from `RSP` at the entry of an ABI0 function (`x+0(FP)`). -/
def frameOffset : Nat := 8

/-- Frame word `i` of memory `m`, for the entry stack pointer `rsp`. -/
def frameWord (m : Memory) (rsp : W64) (i : Nat) : W64 :=
  BitVec.ofNat 64 (m.readLE (rsp.toNat + frameOffset + 8 * i) 8)

/-- The argument words `args` are in the frame of `s`: word `i` at `RSP + 8 + 8i`. -/
def FrameArgs (s : State) (args : List W64) : Prop :=
  ∀ i (h : i < args.length), s.mem.readLE ((s.regs regSP).toNat + 8 + 8 * i) 8 = args[i].toNat

/-- The return-address slot `[RSP]` (which the caller's `CALL` just wrote) and the `n`-word
frame above it are writable and below `2^48`. -/
def FrameOK (s : State) (n : Nat) : Prop :=
  (s.regs regSP).toNat + 8 + 8 * n ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs regSP).toNat (8 + 8 * n) true = true

/-- `s` is a state in which the ABI0 function at `entry` has just been called (`CALL`) with
argument words `args` in the caller's frame and room for `nres` result words after them,
returning to `p.exitAddr` (the word at `[RSP]`), with the direction flag clear. Everything else,
`R14` and `X15` included, is arbitrary. -/
structure CallSetup0 (p : Program) (entry : Nat) (args : List W64) (nres : Nat) (s : State) :
    Prop where
  rip : s.rip = BitVec.ofNat 64 entry
  ret : s.mem.readLE (s.regs regSP).toNat 8 = p.exitAddr
  argWords : FrameArgs s args
  frame : FrameOK s (args.length + nres)
  df : s.df = false

/-- What an ABI0 function restores on return, relative to its call state `s₀`: `RSP` (popped
past the return address), the frame pointer `RBP`, the `FS` base and the direction flag. Not
`R14` or `X15`. -/
structure ABIReturn0 (s₀ s₁ : State) : Prop where
  sp : s₁.regs regSP = s₀.regs regSP + 8
  fp : s₁.regs regFP = s₀.regs regFP
  fs : s₁.fsBase = s₀.fsBase
  df : s₁.df = s₀.df

/-- `k` words of memory `m` starting at byte address `base`. -/
def wordsAt (m : Memory) (base : Nat) : Nat → List W64
  | 0 => []
  | k + 1 => BitVec.ofNat 64 (m.readLE base 8) :: wordsAt m (base + 8) k

/-- The `nres` result words of an ABI0 call with `nargs` argument words, in the memory of the
return state `s₁`, at the frame of the call state `s₀`. -/
def results0 (s₀ s₁ : State) (nargs nres : Nat) : List W64 :=
  wordsAt s₁.mem ((s₀.regs regSP).toNat + 8 + 8 * nargs) nres

/-! ## Specifications -/

/-- ABI0 function contract: for **every** admissible return address `ret` and **every** ABI0
call state with these argument words (and `nres` result words of frame) satisfying `pre`, the
call returns to `ret` (never faulting or panicking), restores what ABI0 requires
(`ABIReturn0`), and satisfies `post s₀ s₁`. -/
def Ensures0 (p : Program) (entry : Nat) (args : List W64) (nres : Nat) (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s, CallSetup0 (p.withExit ret) entry args nres s → pre s →
    Returns (p.withExit ret) s (fun s' => ABIReturn0 s s' ∧ post s s')

/-- `Ensures0` stated on the result words of the frame. -/
def EnsuresResults0 (p : Program) (entry : Nat) (args : List W64) (nres : Nat)
    (pre : State → Prop) (post : List W64 → Prop) : Prop :=
  Ensures0 p entry args nres pre (fun s s' => post (results0 s s' args.length nres))

/-- The general registers after an ABI0 call: `RSP` is the entry value plus 8 (`RET` popped the
return address), `RBP` keeps its value from `old`; every other register, `R14` included, is the
unspecified `junk`. -/
def regs0 (old junk : Nat → W64) : Nat → W64 :=
  fun i => if i = regSP then old regSP + 8 else if i = regFP then old regFP else junk i

/-- The state an ABI0 call from `s` returns in: registers by `regs0`, `RIP` = the pushed return
address, flags, `XMM`/`YMM` registers (`X15` included), `MXCSR` and memory as given; the `FS`
base and the direction flag unchanged. -/
def retState0 (s : State) (junk : Nat → W64) (f : Flags) (v vh : Nat → W128) (mx : BitVec 32)
    (m : Memory) : State :=
  { s with regs := regs0 s.regs junk, rip := retAddrOf s, flags := f, xmm := v, ymmHi := vh,
           mxcsr := mx, mem := m }

/-- The shape of an ABI0 return from `s`: `s'` is `retState0 s …` for some unspecified registers,
flags, vector registers and `MXCSR` status flags (its control bits are kept), and memory `m`
with `Q m`. Reducible, so that the symbolic executor splits it at a call site. -/
@[reducible] def Ret0 (s s' : State) (Q : Memory → Prop) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v vh : Nat → W128) (mx : BitVec 32) (m : Memory),
    s' = retState0 s junk f v vh mx m ∧ mx.toNat / 64 = s.mxcsr.toNat / 64 ∧ Q m

/-- An ABI0 callee summary: a `Summary` (from any state at `entry` satisfying `pre`, ordinary
steps reach the pushed return address) whose return state has the ABI0 shape `Ret0` and memory
satisfying `Q s`. `janus64_run calls [h]` uses it at the `CALL` of a direct ABI0 call or of a
wrapper; the caller's re-entry sequence then re-establishes `X15` and `R14`. -/
def Summary0 (p : Program) (entry : Nat) (pre : State → Prop) (Q : State → Memory → Prop) :
    Prop :=
  Summary p entry pre (fun s s' => Ret0 s s' (Q s))

/-! ## Lemmas -/

section Lemmas

variable {p : Program} {s s' : State} {entry : Nat} {args : List W64} {nres : Nat}

@[simp] theorem wordsAt_zero (m : Memory) (base : Nat) : wordsAt m base 0 = [] := rfl

theorem wordsAt_succ (m : Memory) (base k : Nat) :
    wordsAt m base (k + 1) = BitVec.ofNat 64 (m.readLE base 8) :: wordsAt m (base + 8) k := rfl

@[simp] theorem wordsAt_length (m : Memory) (base k : Nat) : (wordsAt m base k).length = k := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih => simp [wordsAt_succ, ih]

theorem wordsAt_getElem (m : Memory) (base k j : Nat) (h : j < (wordsAt m base k).length) :
    (wordsAt m base k)[j] = BitVec.ofNat 64 (m.readLE (base + 8 * j) 8) := by
  induction k generalizing base j with
  | zero => simp at h
  | succ k ih =>
    cases j with
    | zero => simp [wordsAt_succ]
    | succ j =>
      simp only [wordsAt_succ, List.getElem_cons_succ]
      rw [ih (base + 8) j (by simp at h ⊢; omega),
        show base + 8 + 8 * j = base + 8 * (j + 1) by omega]

/-- Result word `j` is the frame word `nargs + j` of the call state's stack pointer. -/
theorem results0_getElem (s₀ s₁ : State) (nargs nres j : Nat)
    (h : j < (results0 s₀ s₁ nargs nres).length) :
    (results0 s₀ s₁ nargs nres)[j] = frameWord s₁.mem (s₀.regs regSP) (nargs + j) := by
  simp only [results0] at h ⊢
  rw [wordsAt_getElem _ _ _ _ h]
  simp only [frameWord, frameOffset]
  rw [show (s₀.regs regSP).toNat + 8 + 8 * nargs + 8 * j =
    (s₀.regs regSP).toNat + 8 + 8 * (nargs + j) by omega]

theorem results0_one (s₀ s₁ : State) (nargs : Nat) :
    results0 s₀ s₁ nargs 1 =
      [BitVec.ofNat 64 (s₁.mem.readLE ((s₀.regs regSP).toNat + 8 + 8 * nargs) 8)] := rfl

theorem CallSetup0.arg (h : CallSetup0 p entry args nres s) {i : Nat} (hi : i < args.length) :
    s.mem.readLE ((s.regs regSP).toNat + 8 + 8 * i) 8 = args[i].toNat := h.argWords i hi

theorem CallSetup0.frameWord_eq (h : CallSetup0 p entry args nres s) {i : Nat}
    (hi : i < args.length) : frameWord s.mem (s.regs regSP) i = args[i] := by
  simp only [frameWord, frameOffset, h.arg hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem CallSetup0.rip_toNat (h : CallSetup0 p entry args nres s) (he : entry < 2 ^ 64) :
    s.rip.toNat = entry := by
  rw [h.rip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]

theorem CallSetup0.frame_accessible (h : CallSetup0 p entry args nres s) :
    s.mem.accessible (s.regs regSP).toNat (8 + 8 * (args.length + nres)) true = true :=
  h.frame.2

theorem CallSetup0.frame_bound (h : CallSetup0 p entry args nres s) :
    (s.regs regSP).toNat + 8 + 8 * (args.length + nres) ≤ 2 ^ 48 := h.frame.1

theorem ABIReturn0.refl_pop {s₀ s₁ : State} (h1 : s₁.regs regSP = s₀.regs regSP + 8)
    (h2 : s₁.regs regFP = s₀.regs regFP) (h3 : s₁.fsBase = s₀.fsBase) (h4 : s₁.df = s₀.df) :
    ABIReturn0 s₀ s₁ := ⟨h1, h2, h3, h4⟩

/-- `ABIReturn0` as a conjunction of equations (for the post-processing simp set). -/
theorem abiReturn0_iff (s₀ s₁ : State) :
    ABIReturn0 s₀ s₁ ↔ s₁.regs 4 = s₀.regs 4 + 8 ∧ s₁.regs 5 = s₀.regs 5 ∧
      s₁.fsBase = s₀.fsBase ∧ s₁.df = s₀.df :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

@[janus64_exec, janus64_post] theorem regs0_apply (old junk : Nat → W64) (i : Nat) :
    regs0 old junk i = if i = 4 then old 4 + 8 else if i = 5 then old 5 else junk i := rfl

attribute [janus64_exec, janus64_post] retState0

/-- An ABI0 return state restores what `ABIReturn0` requires. -/
theorem ABIReturn0.of_ret0 {s s' : State} {Q : Memory → Prop} (h : Ret0 s s' Q) :
    ABIReturn0 s s' := by
  obtain ⟨junk, f, v, vh, mx, m, rfl, -, -⟩ := h
  exact ⟨by simp [retState0, regs0], by simp [retState0, regs0, regSP, regFP], rfl, rfl⟩

/-- `Ret0` as equations about the return state. -/
@[janus64_post] theorem ret0_iff (s s' : State) (Q : Memory → Prop) :
    Ret0 s s' Q ↔ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.rip = retAddrOf s ∧
      s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64 ∧
      s'.fpucw = s.fpucw ∧ Q s'.mem := by
  constructor
  · rintro ⟨junk, f, v, vh, mx, m, rfl, hmx, hq⟩
    simp [retState0, regs0, regSP, regFP, hq, hmx]
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, hq⟩
    refine ⟨s'.regs, s'.flags, s'.xmm, s'.ymmHi, s'.mxcsr, s'.mem, ?_, h6, hq⟩
    have hr : regs0 s.regs s'.regs = s'.regs := by
      funext i
      simp only [regs0, regSP, regFP]
      split
      · subst_vars; exact h1.symm
      · split
        · subst_vars; exact h2.symm
        · rfl
    cases s'
    simp only [retState0, hr] at *
    subst_vars
    rfl

/-- The memory of an ABI0 return state satisfies `Q`. -/
theorem Ret0.mem {s s' : State} {Q : Memory → Prop} (h : Ret0 s s' Q) : Q s'.mem := by
  obtain ⟨junk, f, v, vh, mx, m, rfl, -, hq⟩ := h
  exact hq

theorem Ensures0.returns {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : Ensures0 p entry args nres pre post) (hret : RetAddr p ret)
    (hs : CallSetup0 (p.withExit ret) entry args nres s) (hpre : pre s) :
    Returns (p.withExit ret) s (fun s' => ABIReturn0 s s' ∧ post s s') := h ret hret s hs hpre

theorem Ensures0.neverPanics {pre : State → Prop} {post : State → State → Prop} {ret : Nat}
    (h : Ensures0 p entry args nres pre post) (hret : RetAddr p ret)
    (hs : CallSetup0 (p.withExit ret) entry args nres s) (hpre : pre s) :
    NeverPanics (p.withExit ret) s := (h ret hret s hs hpre).neverPanics

theorem Ensures0.mono {pre pre' : State → Prop} {post post' : State → State → Prop}
    (h : Ensures0 p entry args nres pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s') : Ensures0 p entry args nres pre' post' :=
  fun ret hret s hs hp => (h ret hret s hs (hpre s hp)).mono fun _ ⟨ha, hq⟩ => ⟨ha, hpost _ _ hp hq⟩

/-- A callee `Summary` of an ABI0 function (precondition `spre`, implied by every ABI0 call
state satisfying `pre`) is an `Ensures0` when its postcondition implies `ABIReturn0`. -/
theorem Ensures0.of_summary {pre spre : State → Prop} {post post' : State → State → Prop}
    (hsum : Summary p entry spre post')
    (hpre : ∀ ret s, RetAddr p ret → CallSetup0 (p.withExit ret) entry args nres s → pre s →
      spre s)
    (hpost : ∀ ret s s', RetAddr p ret → CallSetup0 (p.withExit ret) entry args nres s → pre s →
      post' s s' → ABIReturn0 s s' ∧ post s s') :
    Ensures0 p entry args nres pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.rip (hpre ret s hret hs hp)
  have hst' := hst.withExit hret.fetch_none
  refine returns_of_steps hst' ?_ (hpost ret s s' hret hs hp hq)
  rw [hr, retAddrOf, hs.ret]
  simp only [Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

/-- `Summary0` version of `Ensures0.of_summary`: the summary's memory postcondition `Q` gives
the contract's postcondition. -/
theorem Ensures0.of_summary0 {pre spre : State → Prop} {post : State → State → Prop}
    {Q : State → Memory → Prop} (hsum : Summary0 p entry spre Q)
    (hpre : ∀ ret s, RetAddr p ret → CallSetup0 (p.withExit ret) entry args nres s → pre s →
      spre s)
    (hpost : ∀ ret s s', RetAddr p ret → CallSetup0 (p.withExit ret) entry args nres s → pre s →
      Q s s'.mem → post s s') :
    Ensures0 p entry args nres pre post :=
  Ensures0.of_summary hsum hpre fun ret s s' hret hs hp hr =>
    ⟨ABIReturn0.of_ret0 hr, hpost ret s s' hret hs hp hr.mem⟩

theorem Summary0.mono {pre pre' : State → Prop} {Q Q' : State → Memory → Prop}
    (hsum : Summary0 p entry pre Q) (hpre : ∀ s, pre' s → pre s)
    (hQ : ∀ s m, pre' s → Q s m → Q' s m) : Summary0 p entry pre' Q' :=
  Summary.mono hsum hpre fun s _ hp ⟨junk, f, v, vh, mx, m, he, hmx, hq⟩ =>
    ⟨junk, f, v, vh, mx, m, he, hmx, hQ s m hp hq⟩

theorem Summary0.withExit {pre : State → Prop} {Q : State → Memory → Prop} {ret : Nat}
    (hsum : Summary0 p entry pre Q) (hret : RetAddr p ret) :
    Summary0 (p.withExit ret) entry pre Q :=
  Summary.withExit hsum hret

/-- Use an ABI0 callee summary at a direct call (`CALL f.abi0`): the call returns in
`retState0 s junk f v vh mx m` for **every** choice of the unspecified registers (`R14`
included), flags, vector registers (`X15` included) and `MXCSR` flags, and every memory `m` with
`Q s m`. -/
theorem Summary0.call {pre : State → Prop} {Q : State → Memory → Prop} {Q' : Outcome → Prop}
    (hsum : Summary0 p entry pre Q) (hpc : s.rip = BitVec.ofNat 64 entry) (hpre : pre s)
    (h : ∀ junk f v vh mx m, mx.toNat / 64 = s.mxcsr.toNat / 64 → Q s m →
      Reaches p (retState0 s junk f v vh mx m) Q') :
    Reaches p s Q' :=
  Reaches.call hsum hpc hpre fun _ _ ⟨junk, f, v, vh, mx, m, he, hmx, hq⟩ =>
    he ▸ h junk f v vh mx m hmx hq

/-! ### Re-entry: `g` from TLS, `X15` zeroed -/

/-- The 8 bytes of the TLS `g` slot (`FS:-8`) of `s₀` read the same and are as accessible in
`s₁`: the ABI0 code did not write them. -/
def TlsSlotKept (s₀ s₁ : State) : Prop :=
  s₁.mem.readLE (s₀.fsBase.toNat - 8) 8 = s₀.mem.readLE (s₀.fsBase.toNat - 8) 8 ∧
    s₁.mem.accessible (s₀.fsBase.toNat - 8) 8 false = s₀.mem.accessible (s₀.fsBase.toNat - 8) 8 false

/-- **Re-entry.** If the TLS slot held `g` (`TlsG s₀`, with `R14 = g` in `s₀`), the ABI0 code
returned with the `FS` base kept and the slot not written, then in the return state the slot
still holds `s₀`'s `g`: so the re-entry load `MOVQ FS:-8, R14` reads `R14 = s₀.regs 14` back,
and any state `t` that agrees with `s₁` on memory and `FS` base and has `R14` reloaded satisfies
`TlsG` again. -/
theorem TlsG.reentry {s₀ s₁ t : State} (hg : TlsG s₀) (hfs : s₁.fsBase = s₀.fsBase)
    (hk : TlsSlotKept s₀ s₁) (hm : t.mem = s₁.mem) (htfs : t.fsBase = s₁.fsBase)
    (hr : t.regs regG = s₀.regs regG) : TlsG t where
  base := by rw [htfs, hfs]; exact hg.base
  readable := by rw [hm, htfs, hfs, hk.2]; exact hg.readable
  g := by rw [hm, htfs, hfs, hk.1, hr]; exact hg.g

/-- The re-entry load reads `g`: under `TlsG s₀` and an intact slot, the 8 bytes at `FS:-8` in
the return state are `s₀`'s `R14`. -/
theorem TlsG.load_reentry {s₀ s₁ : State} (hg : TlsG s₀) (hfs : s₁.fsBase = s₀.fsBase)
    (hk : TlsSlotKept s₀ s₁) :
    Janus.Amd64.load s₁.mem (s₁.fsBase + BitVec.ofNat 64 18446744073709551608).toNat 8 =
      .ok (s₀.regs regG).toNat := by
  have hb := hg.base
  have ha : (s₁.fsBase + BitVec.ofNat 64 18446744073709551608).toNat = s₀.fsBase.toNat - 8 := by
    rw [hfs, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [ha]; unfold Janus.Amd64.load
  rw [hk.2, hg.readable]; simp [hk.1, hg.g]

/-! ### Satisfiability -/

/-- Memory `m` with the words `ws` written at `base`, `base + 8`, ... -/
def writeWords (m : Memory) (base : Nat) : List W64 → Memory
  | [] => m
  | w :: ws => writeWords (m.writeLE base 8 w.toNat) (base + 8) ws

@[simp] theorem regions_writeWords (m : Memory) (base : Nat) (ws : List W64) :
    (writeWords m base ws).regions = m.regions := by
  induction ws generalizing m base with
  | nil => rfl
  | cons w ws ih => simp only [writeWords, ih, Janus.Arm64.Memory.regions_writeLE]

theorem readLE_writeWords_below (m : Memory) (base a k : Nat) (ws : List W64)
    (h : a + k ≤ base) : (writeWords m base ws).readLE a k = m.readLE a k := by
  induction ws generalizing m base with
  | nil => rfl
  | cons w ws ih =>
    simp only [writeWords]
    rw [ih _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem readLE_writeWords (m : Memory) (base : Nat) (ws : List W64) (i : Nat)
    (hi : i < ws.length) : (writeWords m base ws).readLE (base + 8 * i) 8 = ws[i].toNat := by
  induction ws generalizing m base i with
  | nil => simp at hi
  | cons w ws ih =>
    simp only [writeWords]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, readLE_writeWords_below _ _ _ _ _ (by omega),
        Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _]
      exact Nat.mod_eq_of_lt (by have := w.isLt; simpa using this)
    | succ i =>
      rw [show base + 8 * (i + 1) = base + 8 + 8 * i by omega]
      exact ih _ _ i (by simp at hi; omega)

/-- A canonical ABI0 call state built from any state `s`: `RIP := entry`, the return address
`p.exitAddr` at `[RSP]`, the argument words written into the frame and `DF` clear (used to show
`CallSetup0` is satisfiable). -/
def setup (p : Program) (entry : Nat) (args : List W64) (s : State) : State :=
  { s with
    rip := BitVec.ofNat 64 entry
    mem := writeWords (s.mem.writeLE (s.regs regSP).toNat 8 p.exitAddr)
      ((s.regs regSP).toNat + 8) args
    df := false }

/-- `CallSetup0` is satisfiable: from any state whose frame is writable, for an exit address
below `2^64`. -/
theorem setup_callSetup0 (s : State) (hf : FrameOK s (args.length + nres))
    (hx : p.exitAddr < 2 ^ 64) : CallSetup0 p entry args nres (setup p entry args s) where
  rip := rfl
  ret := by
    simp only [setup]
    rw [readLE_writeWords_below _ _ _ _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hx)
  argWords := fun i hi => by
    simp only [setup]
    exact readLE_writeWords _ _ _ i hi
  frame := by
    refine ⟨hf.1, ?_⟩
    simp only [setup]
    rw [Janus.Arm64.Memory.accessible_congr (regions_writeWords _ _ _),
      Janus.Arm64.Memory.accessible_congr (Janus.Arm64.Memory.regions_writeLE _ _ _ _)]
    exact hf.2
  df := rfl

end Lemmas

end GoABI0
end Janus.Amd64

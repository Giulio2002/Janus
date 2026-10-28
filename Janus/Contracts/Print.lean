import Janus.Contracts.Syscall
import Janus.Spec.Basic
import Janus.Spec.Print

/-!
# `print` and `println` (arm64; R8)

Go compiles `print(a, b)` / `println(a, b)` to `runtime.printlock()`, one `runtime.print*` call
per argument (with `printsp`/`printnl` for `println`; adjacent constant strings and separators
are merged by the compiler), and `runtime.printunlock()`. Every `print*` function formats into a
buffer and calls `runtime.gwrite`, which records the bytes in the crash backlog
(`recordForPanic`) and, when the goroutine has no `writebuf`, writes them to standard error:
`writeErr` → `writeErrData` → `runtime.write` → `runtime.write1` (assembly, `SVC #0`), one
`write(2, buf, n)` per piece. The kernel is the environment of `Janus.Kernel.ReturnsK`
(`Janus/Contracts/Syscall.lean`), so the output is an **I/O trace**: the bytes appended to
fd 2's output.

## What is executed and what is a contract

The print path below `print`/`println` is plain Go (or Go assembly) and decodes, so the proofs
(`examples/proofs-print`) **execute it from the binary**. Proved so far (arm64): `printlock`
(print count 0, taking `debuglock` through `lock2`, and count ≥ 1), `printunlock` (count 1, through
`unlock2`), `printstring`, `printnl`, `printbool`, `printuint` with
`internal/strconv.formatBase10`, `printint`, `gwrite`, `recordForPanic`, `writeErrData`, `write`,
`write1` (`SVC #0`). On amd64 the same functions are proved up to `printbool`; `formatBase10`,
`printuint`, `printint`, `printlock`/`printunlock` with the mutex, and the top-level examples are
in progress. `printsp`, `printhex`, `printpointer`, `printuintptr`, `printslice`, `printeface`,
`printiface` and the floating-point printers (`printfloat64/32`, `printcomplex128/64`, through
`internal/strconv`'s shortest formatting) are not proved yet: their output format is specified
(`Janus.Spec.Print`: `fmtHex`, `fmtPointer`, `fmtSlice`, `fmtEface`, `fmtF64`, `fmtF32`,
`fmtC128`, `fmtC64`) and differential-tested against the Go 1.26 runtime (`audit/rt-print`), but
no theorem about the machine code relies on those specifications yet.

Three runtime functions are contracts (`janus extract --contract`), stated here:

* `runtime.lock2` / `runtime.unlock2`, the mutex under `printlock` (`Lock2Contract`,
  `Unlock2Contract`). Single-threaded, `printlock` only takes `runtime.debuglock` when the M's
  print count is 0, so the lock is free: the contract is the fast path (the key's lock bit set,
  `m.locks` one higher; the reverse for `unlock2`), with every other change confined to the
  runtime-owned ranges `rt`. Concurrency is out of scope; nothing here models a second thread.
* `runtime.memmove` (`MemmoveContract`): the copy `recordForPanic` makes of every piece into the
  512-byte crash backlog `runtime.printBacklog`.

Every contract has a `_satisfiable` witness (`Janus.Contracts.PrintSat`): machine code proved to
meet it and a call state satisfying its precondition.

## The output

`Emits fd pieces es`: the trace events `es` are what writing each piece of `pieces` with one
`write(fd, piece)` may produce under the kernel contract (`Kernel.Effect .write`): for each
piece either nothing (the call failed with `-errno`) or one event `write(fd, piece[:c])` with
`c ≤ len(piece)` (a short write; the runtime does not retry). `Emits.output_eq`: if the output
of `fd` grew by as many bytes as the pieces hold, it grew by exactly their concatenation.
-/

namespace Janus.Print

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel

/-! ## Go 1.26 layout (linux/arm64 and linux/amd64 agree on these offsets) -/

/-- `g.m` (`*m`). -/
def gM : Nat := 48
/-- `g.writebuf` (`[]byte`: pointer, length, capacity). -/
def gWritebuf : Nat := 232
/-- `m.locks` (`int32`). -/
def mLocks : Nat := 264
/-- `m.dying` (`int32`). -/
def mDying : Nat := 268
/-- `m.printlock` (`int8`): the M's `printlock` nesting count. -/
def mPrintlock : Nat := 279

/-! ## The output trace -/

/-- The trace events `es` are what one `write(fd, piece)` per piece may append (see the module
doc). -/
inductive Emits (fd : Nat) : List Bytes → List Event → Prop where
  | nil : Emits fd [] []
  /-- The `write` failed (`-errno`): no event. -/
  | fail {b : Bytes} {bs : List Bytes} {es : List Event} : Emits fd bs es → Emits fd (b :: bs) es
  /-- The kernel wrote the first `c` bytes. -/
  | write {b : Bytes} {bs : List Bytes} {es : List Event} (c : Nat) (hc : c ≤ b.length) :
      Emits fd bs es → Emits fd (b :: bs) (.write fd (b.take c) :: es)

namespace Emits

theorem append {fd : Nat} {bs bs' : List Bytes} {es es' : List Event} (h : Emits fd bs es)
    (h' : Emits fd bs' es') : Emits fd (bs ++ bs') (es ++ es') := by
  induction h with
  | nil => exact h'
  | fail _ ih => exact .fail ih
  | write c hc _ ih => exact .write c hc ih

/-- One piece. -/
theorem single {fd : Nat} {b : Bytes} {es : List Event}
    (h : es = [] ∨ ∃ c, c ≤ b.length ∧ es = [.write fd (b.take c)]) : Emits fd [b] es := by
  rcases h with rfl | ⟨c, hc, rfl⟩
  · exact .fail .nil
  · exact .write c hc .nil

/-- The output of `fd` the events add is at most as long as the pieces. -/
theorem output_le {fd : Nat} {bs : List Bytes} {es : List Event} (h : Emits fd bs es) :
    (outputOf fd es).length ≤ bs.flatten.length := by
  induction h with
  | nil => simp [outputOf]
  | fail _ ih => simp only [List.flatten_cons, List.length_append]; omega
  | write c hc _ ih =>
    simp only [outputOf, if_true, List.length_append, List.length_take, List.flatten_cons]
    omega

/-- **Full output.** If the output of `fd` grew by as many bytes as the pieces hold, every
`write` was complete and the output grew by exactly the concatenation of the pieces. -/
theorem output_eq {fd : Nat} {bs : List Bytes} {es : List Event} (h : Emits fd bs es)
    (hl : (outputOf fd es).length = bs.flatten.length) : outputOf fd es = bs.flatten := by
  induction h with
  | nil => rfl
  | @fail b bs es h ih =>
    have := h.output_le
    simp only [List.flatten_cons, List.length_append] at hl
    have hb : b.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hb, List.flatten_cons, List.nil_append]
    exact ih (by omega)
  | @write b bs es c hc h ih =>
    have := h.output_le
    simp only [outputOf, if_true, List.length_append, List.length_take, List.flatten_cons]
      at hl ⊢
    have hcb : c = b.length := by omega
    subst hcb
    rw [List.take_length, ih (by rw [Nat.min_self] at hl; omega)]

end Emits

/-- `k` with the events `es` appended to its trace (what a run of `print` pieces does to the
kernel state: `write` changes nothing else). -/
def _root_.Janus.Kernel.Kern.appendTrace (k : Kern) (es : List Event) : Kern := { k with trace := k.trace ++ es }

@[simp] theorem _root_.Janus.Kernel.Kern.appendTrace_nil (k : Kern) : k.appendTrace [] = k := by
  simp [Kern.appendTrace]

theorem _root_.Janus.Kernel.Kern.appendTrace_append (k : Kern) (es es' : List Event) :
    (k.appendTrace es).appendTrace es' = k.appendTrace (es ++ es') := by
  simp [Kern.appendTrace, List.append_assoc]

theorem _root_.Janus.Kernel.Kern.emit_eq_appendTrace (k : Kern) (e : Event) : k.emit e = k.appendTrace [e] := rfl

theorem _root_.Janus.Kernel.Kern.output_appendTrace (k : Kern) (es : List Event) (fd : Nat) :
    (k.appendTrace es).output fd = k.output fd ++ outputOf fd es := by
  simp [Kern.appendTrace, Kern.output, outputOf_append]

/-- **Full output**, on a kernel state: if the output of `fd` grew by as many bytes as the pieces
hold, it grew by exactly their concatenation. -/
theorem Emits.full {fd : Nat} {k : Kern} {bs : List Bytes} {es : List Event} (h : Emits fd bs es)
    (hl : ((k.appendTrace es).output fd).length = (k.output fd).length + bs.flatten.length) :
    (k.appendTrace es).output fd = k.output fd ++ bs.flatten := by
  rw [Kern.output_appendTrace] at hl ⊢
  rw [h.output_eq (by simp only [List.length_append] at hl; omega)]

/-! ## Running a kernel-level callee

A function whose run reaches a `.syscall` stub (`gwrite` and every `print*` above it) cannot be a
`Summary` (ordinary steps only). Its proofs instead state a **continuation lemma**: from a state
at its entry, every run under the kernel semantics returns to `X30` in a state and kernel state
satisfying its postcondition, and from there the caller's continuation goes on:

`pre s k → (∀ s' k', s'.pc = s.regs 30 → post s k s' k' → ReturnsK P E Q X s' k') → ReturnsK P E Q X s k`.

`ReturnsK.to_reaches` turns the `Reaches` goal at a stopping point of `janus_run until [...]` (the
callee's entry, or its `RET`) back into a `ReturnsK` goal, to which the callee's continuation
lemma (or, after the `RET`, the caller's continuation) applies. -/

/-- A `ReturnsK` run is a `Reaches` run to an outcome satisfying `IsReturnK` (the converse of
`ReturnsK.of_reaches`). -/
theorem ReturnsK.to_reaches {p : Program} {E : KEnv} {post : State → Kern → Prop}
    {onExit : Nat → Kern → Prop} {s : State} {k : Kern} (h : ReturnsK p E post onExit s k) :
    Reaches p s (IsReturnK p E post onExit k) := by
  induction h with
  | exit hx hp => exact ⟨1, .returned _, by simp [Program.run, hx], hp⟩
  | @step s s' k w hx hs hf hst _ ih =>
    obtain ⟨n, o, hr, hq⟩ := ih
    refine ⟨n + 1, o, ?_, hq⟩
    simp only [Program.run, ite_eq_right hx, hs, hf, hst]
    exact hr
  | @sys s k st site hx hs hk hsite hsafe hn _ =>
    refine ⟨1, .stub st.name st.kind s, by simp [Program.run, hx, hs], ?_⟩
    rw [hk]
    exact ⟨site, hsite, Or.inl ⟨hsafe, hn⟩⟩
  | @halt s k st site code hx hs hk hsite he hp =>
    refine ⟨1, .stub st.name st.kind s, by simp [Program.run, hx, hs], ?_⟩
    rw [hk]
    exact ⟨site, hsite, Or.inr ⟨code, he, hp⟩⟩

/-! ## Runtime contracts -/

/-- The low byte of the mutex key at `l` (`key8(&l.key)`), bit 0 (`mutexLocked`): the lock is
held. -/
def lockHeld (m : Memory) (l : Nat) : Prop := m.readLE l 1 % 2 = 1

/-- `m.locks` of the M of the `g` at `g` (as a raw 32-bit value). -/
def mLocksOf (m : Memory) (g : Nat) : Nat := m.readLE (m.readLE (g + gM) 8 + mLocks) 4

attribute [janus_exec, janus_post] gM gWritebuf mLocks mDying mPrintlock mLocksOf lockHeld

/-- What `lock2`/`unlock2` need at the call (arm64): the mutex key (8 bytes at `X0`) writable,
the M (through `g.m`) readable with `m.locks` writable, every byte they write inside `rt`, and
`m.locks` in the range the function accepts (`lock2` throws `lock count` below 0, `unlock2`
after its decrement below 0): `lo ≤ m.locks < 2^31 - 1`. -/
def LockPre (rt : List (Nat × Nat)) (lo : Nat) (s : State) : Prop :=
  (s.regs 0).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 8 true = true ∧
    InRanges (s.regs 0).toNat 8 rt ∧
    (s.regs 28).toNat + gM + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + gM) 8 false = true ∧
    Outside ((s.regs 28).toNat + gM) 8 rt ∧
    s.mem.readLE ((s.regs 28).toNat + gM) 8 + mLocks + 4 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + gM) 8 + mLocks) 4 true = true ∧
    InRanges (s.mem.readLE ((s.regs 28).toNat + gM) 8 + mLocks) 4 rt ∧
    Apart (s.regs 0).toNat 8 (s.mem.readLE ((s.regs 28).toNat + gM) 8 + mLocks) 4 ∧
    lo ≤ mLocksOf s.mem (s.regs 28).toNat ∧ mLocksOf s.mem (s.regs 28).toNat + 1 < 2 ^ 31

/-- **`runtime.lock2(l)`** (arm64; `X0 = l`), called by `printlock` on `runtime.debuglock` when
the M's print count was 0. Precondition: the lock is free (single-threaded: nobody else holds
it), `LockPre rt 0`. Postcondition: the function returns to `X30` with `R18`, `g`, `FP` preserved,
every other register, the flags and the SIMD&FP registers unspecified, memory changed only inside
`rt` and the stack window, the lock held and `m.locks` one higher (the fast path of
`runtime/lock_spinbit.go`: `gp.m.locks++`, `Xchg8(key8(&l.key), mutexLocked)`). -/
def Lock2Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK s stack 1 ∧ LockPre rt 0 s ∧ ¬ lockHeld s.mem (s.regs 0).toNat)
    (fun s s' => AllocRet rt stack 1 (fun _ => []) s s' fun m _ =>
      lockHeld m (s.regs 0).toNat ∧
        mLocksOf m (s.regs 28).toNat = mLocksOf s.mem (s.regs 28).toNat + 1)

/-- **`runtime.unlock2(l)`** (arm64; `X0 = l`), called by `printunlock` when the M's print count
drops to 0. Precondition: the lock is held (else `unlock2` throws), `LockPre rt 1` (else it
throws `lock count`). Postcondition: returns as `Lock2Contract`, the key's low byte cleared
(`Xchg8(key8(&l.key), 0)`) and `m.locks` one lower; waking a sleeper, the lock profile and a
pending preemption request (`g.stackguard0`) are changes inside `rt`. -/
def Unlock2Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK s stack 1 ∧ LockPre rt 1 s ∧ lockHeld s.mem (s.regs 0).toNat)
    (fun s s' => AllocRet rt stack 1 (fun _ => []) s s' fun m _ =>
      m.readLE (s.regs 0).toNat 1 = 0 ∧
        mLocksOf m (s.regs 28).toNat + 1 = mLocksOf s.mem (s.regs 28).toNat)

/-- What `memmove(dst, src, n)` needs here (arm64; `X0 = dst`, `X1 = src`, `X2 = n`): an admissible
return address, `n` writable bytes at `dst` and `n` readable bytes at `src`, below `2^48` and
disjoint (the only use here: the copy of a piece into `runtime.printBacklog`). -/
def MemmovePre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (s.regs 0).toNat + (s.regs 2).toNat ≤ 2 ^ 48 ∧ (s.regs 1).toNat + (s.regs 2).toNat ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (s.regs 2).toNat true = true ∧
    s.mem.accessible (s.regs 1).toNat (s.regs 2).toNat false = true ∧
    ((s.regs 0).toNat + (s.regs 2).toNat ≤ (s.regs 1).toNat ∨
      (s.regs 1).toNat + (s.regs 2).toNat ≤ (s.regs 0).toNat)

/-- **`runtime.memmove(dst, src, n)`** (arm64): returns to `X30` with `R18`, `g`, `FP` and `SP`
preserved (every other register, the flags and the SIMD&FP registers unspecified), memory
changed only at `[dst, dst + n)`, which then holds the `n` bytes that were at `src`. -/
def MemmoveContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr MemmovePre
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
        (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      s' = retStateX s junk [] f v m ex ep ∧
        MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] ∧
        readBytes m (s.regs 0).toNat (s.regs 2).toNat =
          readBytes s.mem (s.regs 1).toNat (s.regs 2).toNat)

end Janus.Print

/-! ## Byte arithmetic the print code does (`LDRSB` + `UBFX`, `STRB` of a count)

Rewrite rules for `janus_run [...]` (not in the global simp sets): the M's `printlock` count is
an `int8` loaded sign-extended and then masked to 8 bits. -/

namespace Janus.Print

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel

theorem rotateRight_zero64 (x : BitVec 64) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_rotateRight, Nat.shiftLeft_eq, Nat.mul_mod_left]

theorem ofNat_and255 (n : Nat) : BitVec.ofNat 64 n &&& 255#64 = BitVec.ofNat 64 (n % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sext8_and255 (v : Nat) :
    BitVec.ofNat 64 (if v < 128 then v else v + 18446744073709551360) &&& 255#64 =
      BitVec.ofNat 64 (v % 256) := by
  rw [ofNat_and255]
  split <;> congr 1 <;> omega

theorem setWidth32_ofNat (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ofNat32_eq_zero (n : Nat) : (BitVec.ofNat 32 n = 0#32) = (n % 2 ^ 32 = 0) := by
  apply propext
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

/-- A sign-extended 32-bit load (`LDRSW`) plus `k`, stored back as 32 bits (`STR Wt`). -/
theorem sext32_add_mod (v k : Nat) :
    ((if v < 2147483648 then v else (v + 18446744069414584320) % 18446744073709551616) + k) %
        18446744073709551616 % 4294967296 = (v + k) % 4294967296 := by
  split <;> omega

/-- A sign-extended byte load (`LDRSB`) plus `k`, stored back as a byte (`STRB`). -/
theorem sext8_add_mod (v k : Nat) :
    ((if v < 128 then v else (v + 18446744073709551360) % 18446744073709551616) + k) %
        18446744073709551616 % 256 = (v + k) % 256 := by
  split <;> omega

theorem sext8_add_mod' (v k : Nat) :
    ((if v < 128 then v else v + 18446744073709551360) + k) % 18446744073709551616 % 256 =
      (v + k) % 256 := by
  split <;> omega

/-- A state that differs from the call state `s` only in the registers outside `R18`, `g` and `FP`,
the flags, the SIMD&FP registers and memory, at `pc = X30`, is a `retState` of `s`. -/
theorem eq_retState {s s' : State} (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28)
    (h29 : s'.regs 29 = s.regs 29) (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (hd : s'.dczid = s.dczid) (ht : s'.tpidr = s.tpidr) (hc : s'.fpcr = s.fpcr)
    (hs : s'.fpsr = s.fpsr) : s' = retStateX s s'.regs [] s'.flags s'.vregs s'.mem s'.excl s'.exclPass := by
  cases s'
  simp only [retStateX] at *
  subst hsp hpc hd ht hc hs
  congr 1
  funext i
  simp only [callRegs]
  split
  · rename_i h; rcases h with rfl | rfl | rfl <;> assumption
  · simp

/-- `ret_state`: close `s' = retState s ?junk [] ?f ?v ?m` for a state literal `s'` (the
registers `R18`, `g`, `FP` and the other fields checked by `simp`). -/
macro "ret_state" : tactic => `(tactic|
  exact eq_retState (by simp [setReg, callRegs]) (by simp [setReg, callRegs]) (by simp [setReg, callRegs])
    rfl rfl rfl rfl rfl rfl)

/-- `ret_state [h, …]`: `ret_state` with the register equations `h, …` (for a state built on a
loop-head state `S` with `S.regs 28 = …`). -/
macro "ret_state" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact eq_retState (by simp [setReg, callRegs, $hs,*]) (by simp [setReg, callRegs, $hs,*])
    (by simp [setReg, callRegs, $hs,*])
    (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*])
    (by simp [$hs,*]))

open Lean Elab Tactic Meta in
/-- `name_reads`: give every hypothesis `m.readLE a n = v` whose name is inaccessible (a callee
postcondition destructured by `janus_run calls [...]`) the name `h_rd<k>`, so that the executor
uses it as a rewrite rule (`Janus.Tactic.stateHyps`). -/
elab "name_reads" : tactic => do
  let mut g ← getMainGoal
  let mut k := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    unless d.userName.hasMacroScopes || d.userName.isInaccessibleUserName do continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    unless lhs.isAppOfArity ``Memory.readLE 3 do continue
    g ← g.rename d.fvarId (Name.mkSimple s!"h_rd_cn{k}")
    k := k + 1
  replaceMainGoal [g]

/-- An `if` in a branch condition, as a disjunction `omega` understands. -/
theorem ite_eq_nat (c : Prop) [Decidable c] (a b k : Nat) :
    ((if c then a else b) = k) = ((c ∧ a = k) ∨ (¬c ∧ b = k)) := by
  by_cases h : c <;> simp [h]

/-! ### `recordForPanic`'s index arithmetic (bounds-check masks, signed `% 512`) -/

theorem sub_wrap (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    (18446744073709551616 - b + a) % 18446744073709551616 = a - b := by omega

/-- `SUB t, x, b; AND t, x, t, ASR #63` (the spectre mask of a bounds-checked index `x < b`). -/
theorem and_sshr_lt (x b : Nat) (hx : x < b) (hb : b ≤ 9223372036854775808) :
    x &&& ((BitVec.ofNat 64 x - BitVec.ofNat 64 b).sshiftRight 63).toNat = x := by
  have : (BitVec.ofNat 64 x - BitVec.ofNat 64 b).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight]
    have hneg : (BitVec.ofNat 64 x - BitVec.ofNat 64 b).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    simp only [hneg, ite_true, BitVec.toNat_allOnes]
    simp [BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_allOnes, show 2 ^ 64 - 1 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sshr63_small (v : Nat) (h : v < 9223372036854775808) :
    (BitVec.ofNat 64 v).sshiftRight 63 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight]
  have : (BitVec.ofNat 64 v).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp only [this]
  simp [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The bits of `0xffff_ffff_ffff_fe00`. -/
theorem key9 : ∀ j : Fin 64, (18446744073709551104#64).getLsbD j.val = decide (9 ≤ j.val) := by decide
theorem mask512 (x : BitVec 64) : x &&& 18446744073709551104#64 = (x >>> 9) <<< 9 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := key9 ⟨i, hi⟩
  simp only at this
  simp only [BitVec.getLsbD_and, this, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : 9 ≤ i
  · simp [h, hi, show 9 + (i - 9) = i by omega]
  · simp [h, show i < 9 by omega]
/-- The signed `% 512` (`ASR #63`, `LSR #55`, `AND #~511`, `SUB`) of a non-negative index. -/
theorem smod512 (x : BitVec 64) (h : x.toNat < 9223372036854775808) :
    x - (x + (((if x.getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64 ||| x.rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 55) &&&
        18446744073709551104#64) = BitVec.ofNat 64 (x.toNat % 512) := by
  have h63 : x.getLsbD 63 = false := by
    rw [BitVec.getLsbD_eq_getElem (by decide)]
    simp only [BitVec.getElem_eq_testBit_toNat]
    exact Nat.testBit_lt_two_pow (by simpa using h)
  have hr : x.rotateRight 63 &&& 18446744073709551615#64 &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat]
    rw [show (1 : Nat) % 2^64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rw [show (18446744073709551615 : Nat) % 2^64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h0 : x.toNat / 2 ^ 63 = 0 := by omega
    rw [h0, Nat.zero_or]
    simp
  rw [h63, hr, mask512]
  simp only [Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp
  omega

/-! ## Disjointness facts

The print path writes a stack window, the backlog, its index and two bytes of the M, and reads
`g`'s fields, the M's fields, the globals and the printed bytes: every written range must be apart
from every range read after. `Sep a n [(b, k), …]` states `Apart a n b k` for each `(b, k)`
(`Apart`: a fact `omega` does not unfold, used one at a time by the dischargers). -/

/-- `[a, a + n)` is apart from every `[b, b + k)` of the list of `(b, k)`. -/
def Sep (a n : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (b, k) :: rs => Apart a n b k ∧ Sep a n rs

@[simp] theorem sep_nil (a n : Nat) : Sep a n [] = True := rfl
@[simp] theorem sep_cons (a n b k : Nat) (rs : List (Nat × Nat)) :
    Sep a n ((b, k) :: rs) = (Apart a n b k ∧ Sep a n rs) := rfl

open Lean Elab Tactic Meta in
/-- `split_ands`: split every conjunction hypothesis of the context (recursively), keeping
the names of the parts inaccessible. -/
partial def splitAndsCore (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then
      let gs ← g.cases d.fvarId
      let some sg := gs[0]? | return g
      return ← splitAndsCore sg.mvarId
    if ty.isAppOfArity ``True 0 then
      let g ← g.clear d.fvarId
      return ← splitAndsCore g
  return g

open Lean Elab Tactic in
elab "split_ands" : tactic => do
  replaceMainGoal [← splitAndsCore (← getMainGoal)]

theorem readBytes_take (m : Memory) (a n c : Nat) (h : c ≤ n) :
    (readBytes m a n).take c = readBytes m a c := by
  unfold readBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The one-piece trace of a `write` outcome. -/
theorem emits_write (m : Memory) (a n c : Nat) (h : c ≤ n) :
    Emits 2 [readBytes m a n] [.write 2 (readBytes m a c)] := by
  have := Emits.write (fd := 2) (b := readBytes m a n) (bs := []) (es := []) c
    (by simp; exact h) .nil
  rwa [readBytes_take m a n c h] at this

theorem emits_fail (b : Bytes) : Emits 2 [b] [] := .fail .nil

/-- `emits_write` with the bytes read from another memory that holds the same `n` bytes. -/
theorem emits_of_eq {m : Memory} {a n c : Nat} {b : Bytes} (h : readBytes m a n = b) (hc : c ≤ n) :
    Emits 2 [b] [.write 2 (readBytes m a c)] := by
  rw [← h]; exact emits_write m a n c hc

open Lean Elab Tactic Meta in
/-- `apart_mono`: an `Apart` goal from a wider `Apart` hypothesis (`Common.dischargeApart`). -/
elab "apart_mono" : tactic => do
  let g ← getMainGoal
  unless ← Janus.Tactic.Common.dischargeApart g do throwError "apart_mono: no wider `Apart` fact"
  replaceMainGoal []

/-- `kobl`: close one obligation of a continuation lemma applied at a call site (the call state
is a literal): `rfl`/an assumption (after reducing the state's projections); an `Apart` fact from
a wider one; a register or `SP` equation (`toNat` and `omega`); arithmetic (`omega`); a memory
read or accessibility fact through the stores and frames (`janus_simp`, the discharger). -/
macro "kobl_slow" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | apart_mono
  | (dsimp only; with_reducible assumption)
  | (dsimp only; apply BitVec.eq_of_toNat_eq; simp; omega)
  | omega
  | (dsimp only; janus_disch)
  | (janus_simp; first | done | with_reducible assumption | omega))

open Lean Elab Tactic Meta in
/-- `kobl`: one obligation of a continuation lemma at a call site, by its shape (see `kobl_slow`). -/
elab "kobl" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let run (stx : TSyntax `tactic) : TacticM Unit := evalTactic stx
  if t.isAppOfArity ``Janus.Apart 4 then
    run (← `(tactic| first | with_reducible assumption | apart_mono | (janus_simp; first | with_reducible assumption | apart_mono | (unfold Janus.Apart; omega)))); return
  if t.isAppOfArity ``Janus.MemFrame 3 then
    run (← `(tactic| janus_frame)); return
  if let some (ty, lhs, _) := t.eq? then
    let ty ← whnfR ty
    if ty.isAppOfArity ``BitVec 1 then
      run (← `(tactic| first | with_reducible rfl | (dsimp only; with_reducible assumption) | (dsimp only; simp only [Janus.Tactic.setReg_apply]; first | assumption | rfl) | rfl | (dsimp only; simp only [Janus.Tactic.setReg_apply]; apply BitVec.eq_of_toNat_eq; simp; omega) | (dsimp only; apply BitVec.eq_of_toNat_eq; simp; omega) | (dsimp only; apply BitVec.eq_of_toNat_eq; simp [setReg]; omega) | (simp [setReg, callRegs]) | (simp [setReg, callRegs, BitVec.ofNat_toNat]) | (apply BitVec.eq_of_toNat_eq; simp; omega))); return
    if lhs.isAppOfArity ``Memory.accessible 4 then
      run (← `(tactic| first | with_reducible assumption | (dsimp only; janus_disch) | (janus_simp; first | done | janus_disch))); return
    if lhs.isAppOfArity ``Memory.readLE 3 then
      run (← `(tactic| first | with_reducible assumption | (dsimp only; with_reducible assumption) | (janus_simp; first | done | with_reducible assumption | omega))); return
    if ty.isConstOf ``Nat then
      run (← `(tactic| first | with_reducible rfl | omega | (janus_simp; first | done | omega))); return
  if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 then
    run (← `(tactic| first | omega | (janus_simp; first | done | omega))); return
  run (← `(tactic| kobl_slow))

theorem emits_congr {m m' : Memory} {a n : Nat} {es : List Event}
    (h : Emits 2 [readBytes m a n] es) (heq : readBytes m a n = readBytes m' a n) :
    Emits 2 [readBytes m' a n] es := heq ▸ h

set_option hygiene false in
/-- `readBytes m a n = readBytes m₀ a n` through the stores and memory frames between them (the
side conditions by the discharger). -/
macro "readbytes_frame" : tactic => `(tactic| (
  repeat (first
    | refine (readBytes_writeLE (by janus_disch)).trans ?_
    | refine (MemFrame.readBytes_eq (by assumption) (by janus_disch)).trans ?_)
  rfl))

/-! ### Bitfield moves (`UBFM`: `LSR`, `UBFX`, `LSL`, `UBFIZ` by an immediate)

The model executes `UBFM` as a rotation and two masks: `x.rotateRight r &&& M &&& T`. Instances of
`ubfm_low` (a shift right and a low mask) and `ubfm_shl` (a mask and a shift left), with their side
conditions decided on the literals, rewrite each shape a proof meets into arithmetic on `x.toNat`. -/

/-- `LSR`/`UBFX`: bits `r … r + w - 1` of `x`. -/
theorem ubfm_low (x : BitVec 64) (r w M T : Nat) (hrw : r + w ≤ 64) (hT : T = 2 ^ w - 1)
    (hM : M % 2 ^ w = 2 ^ w - 1) :
    x.rotateRight r &&& BitVec.ofNat 64 M &&& BitVec.ofNat 64 T =
      BitVec.ofNat 64 (x.toNat / 2 ^ r % 2 ^ w) := by
  subst hT
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_rotateRight, hi,
    decide_true, Bool.true_and]
  have hM' : ∀ j, j < w → M.testBit j = true := by
    intro j hj
    have := Nat.testBit_mod_two_pow M w j
    rw [hM, Nat.testBit_two_pow_sub_one] at this
    simp [hj] at this; exact this
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : i < w
  · simp only [h, decide_true, Bool.and_true, hM' i h, Bool.true_and]
    rw [Nat.mod_eq_of_lt (show r < 64 by omega), if_pos (by omega), Nat.add_comm]
    rfl
  · simp [h]

/-- `LSL`/`UBFIZ`: the low `w` bits of `x`, shifted left by `s`. -/
theorem ubfm_shl (x : BitVec 64) (r w s M T : Nat) (hr : r = 64 - s) (hs : 0 < s) (hws : w + s ≤ 64)
    (hT : T = (2 ^ w - 1) * 2 ^ s) (hM : M / 2 ^ s % 2 ^ w = 2 ^ w - 1) :
    x.rotateRight r &&& BitVec.ofNat 64 M &&& BitVec.ofNat 64 T =
      BitVec.ofNat 64 (x.toNat % 2 ^ w * 2 ^ s) := by
  subst hT hr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_rotateRight, hi,
    decide_true, Bool.true_and]
  have hT' : ∀ j, ((2 ^ w - 1) * 2 ^ s).testBit j = (decide (s ≤ j) && decide (j < s + w)) := by
    intro j
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h : s ≤ j <;> simp [h] <;> omega
  have hM' : ∀ j, s ≤ j → j < s + w → M.testBit j = true := by
    intro j h1 h2
    have := Nat.testBit_mod_two_pow (M / 2 ^ s) w (j - s)
    rw [hM, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow] at this
    simp [show j - s < w by omega, show j - s + s = j by omega] at this; exact this
  rw [hT', ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
  by_cases h : s ≤ i ∧ i < s + w
  · obtain ⟨h1, h2⟩ := h
    simp only [h1, h2, decide_true, Bool.and_true, hM' i h1 h2, Bool.true_and, ge_iff_le,
      show i - s < w by omega]
    rw [Nat.mod_eq_of_lt (show 64 - s < 64 by omega), if_neg (by omega)]
    rw [show i - (64 - (64 - s)) = i - s by omega]
    rfl
  · rcases Decidable.not_and_iff_or_not.mp h with h | h
    · simp [h]
    · have : ¬ (i - s < w) ∨ ¬ s ≤ i := by omega
      rcases this with h' | h' <;> simp [h, h']

theorem and_allOnes64 (y : BitVec 64) : y &&& BitVec.ofNat 64 18446744073709551615 = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (18446744073709551615 : Nat) % 2 ^ 64 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt y.isLt

theorem and2_of_and3 (y : BitVec 64) (T : Nat) :
    y &&& BitVec.ofNat 64 T = y &&& BitVec.ofNat 64 18446744073709551615 &&& BitVec.ofNat 64 T := by
  rw [and_allOnes64]

theorem natAnd_toNat (y : BitVec 64) (T : Nat) (hT : T < 2 ^ 64) :
    y.toNat &&& T = (y &&& BitVec.ofNat 64 T).toNat := by
  simp [BitVec.toNat_and, Nat.mod_eq_of_lt hT]

/-! ### Division by constants (the compiler's magic multiplications in `formatBase10`) -/

/-- `x / 50` for `x < 2^31` as the multiply-and-shift of 32-bit code. -/
theorem magic50 (y : Nat) (h : y < 2^31) : y * 2748779070 / 137438953472 = y / 50 := by
  have h1 := Nat.div_add_mod y 50
  have h2 := Nat.mod_lt y (show 50 > 0 by decide)
  generalize y / 50 = q at *
  generalize y % 50 = r at *
  subst h1
  omega
/-- `UBFX #1, #31`, `MUL`, `LSR #37`: `x / 100` for 32-bit `x`. -/
theorem magic100 (x : Nat) (h : x < 2^32) :
    x / 2 % 2147483648 * 2748779070 / 137438953472 % 134217728 = x / 100 := by
  rw [Nat.mod_eq_of_lt (show x / 2 < 2147483648 by omega), magic50 (x / 2) (by omega)]
  omega
/-- `LSR #1`, `UMULH`, `LSR #28`: `y / 5·10^8`, i.e. `x / 10^9` for `y = x / 2`. -/
theorem magic5e8 (y : Nat) (h : y < 2^63) : y * 9903520314283042200 / 2^92 = y / 500000000 := by
  have h1 := Nat.div_add_mod y 500000000
  have h2 := Nat.mod_lt y (show 500000000 > 0 by decide)
  generalize y / 500000000 = q at *
  generalize y % 500000000 = r at *
  subst h1
  omega

/-- `UMULH` by a literal (the model's 128-bit product). -/
theorem umulh_lit (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) :
    (BitVec.extractLsb' 64 64 (x.setWidth 128 * BitVec.ofNat 128 c)).toNat =
      x.toNat * c / 2 ^ 64 := by
  have h := Janus.Tactic.umulh_toNat x (BitVec.ofNat 64 c)
  have e : (BitVec.ofNat 64 c).setWidth 128 = BitVec.ofNat 128 c := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega
  rw [e] at h; rw [h]; simp; rw [Nat.mod_eq_of_lt hc]
/-- `x / 10^9` as `formatBase10` computes it. -/
theorem magic1e9 (x : Nat) (h : x < 2 ^ 64) :
    x / 2 % 9223372036854775808 * 9903520314283042200 / 18446744073709551616 / 268435456 %
      68719476736 = x / 1000000000 := by
  rw [Nat.mod_eq_of_lt (show x / 2 < 9223372036854775808 by omega), Nat.div_div_eq_div_mul,
    show 18446744073709551616 * 268435456 = 2 ^ 92 by decide, magic5e8 (x / 2) (by omega)]
  omega

/-! ### Bytes written one at a time -/

theorem readBytes_add (m : Memory) (a n k : Nat) :
    readBytes m a (n + k) = readBytes m a n ++ readBytes m (a + n) k := by
  unfold readBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro i _; simp [Function.comp, Nat.add_assoc]
theorem readBytes_succ (m : Memory) (a n : Nat) :
    readBytes m a (n + 1) = m.bytes a :: readBytes m (a + 1) n := by
  rw [Nat.add_comm, readBytes_add]; simp [readBytes]
theorem bytes_writeLE1_self (m : Memory) (p v : Nat) : (m.writeLE p 1 v).bytes p = BitVec.ofNat 8 v := by
  simp [Memory.writeLE]
theorem bytes_writeLE1_ne (m : Memory) (p q v : Nat) (h : p ≠ q) : (m.writeLE p 1 v).bytes q = m.bytes q := by
  simp [Memory.writeLE]; omega

theorem ReachesRet.mono' {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

/-- Two bytes written in a row, read back with what follows them. -/
theorem readBytes_two_writes (m : Memory) (p n v0 v1 : Nat) :
    readBytes ((m.writeLE p 1 v0).writeLE (p + 1) 1 v1) p (n + 2) =
      [BitVec.ofNat 8 v0, BitVec.ofNat 8 v1] ++ readBytes m (p + 2) n := by
  rw [readBytes_succ, readBytes_succ]
  rw [bytes_writeLE1_ne _ _ _ _ (by omega), bytes_writeLE1_self, bytes_writeLE1_self,
    show p + 1 + 1 = p + 2 by omega, readBytes_writeLE (by omega), readBytes_writeLE (by omega)]
  rfl

theorem readBytes_two_writes' (m : Memory) (p n v0 v1 : Nat) :
    readBytes ((m.writeLE (p + 1) 1 v1).writeLE p 1 v0) p (n + 2) =
      [BitVec.ofNat 8 v0, BitVec.ofNat 8 v1] ++ readBytes m (p + 2) n := by
  rw [readBytes_succ, readBytes_succ]
  rw [bytes_writeLE1_self, bytes_writeLE1_ne _ _ _ _ (by omega), bytes_writeLE1_self,
    show p + 1 + 1 = p + 2 by omega, readBytes_writeLE (by omega), readBytes_writeLE (by omega)]
  rfl
theorem readBytes_one_write (m : Memory) (p n v : Nat) :
    readBytes (m.writeLE p 1 v) p (n + 1) = [BitVec.ofNat 8 v] ++ readBytes m (p + 1) n := by
  rw [readBytes_succ, bytes_writeLE1_self, readBytes_writeLE (by omega)]
  rfl
theorem eq_retState_res {s s' : State} {r : BitVec 64} (h0 : s'.regs 0 = r) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hsp : s'.sp = s.sp)
    (hpc : s'.pc = s.regs 30) (hd : s'.dczid = s.dczid) (ht : s'.tpidr = s.tpidr)
    (hc : s'.fpcr = s.fpcr) (hs : s'.fpsr = s.fpsr) :
    s' = retStateX s s'.regs [r] s'.flags s'.vregs s'.mem s'.excl s'.exclPass := by
  cases s'
  simp only [retStateX] at *
  subst hsp hpc hd ht hc hs
  congr 1
  funext i
  simp only [callRegs]
  split
  · rename_i h; rcases h with rfl | rfl | rfl <;> assumption
  · rcases i with _ | i
    · simpa using h0
    · simp

/-- `ret_state_res r [h, …]`: `s' = retState s ?junk [r] ?f ?v ?m` for a state literal `s'` whose
`X0` is `r`. -/
macro "ret_state_res" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact eq_retState_res (by simp [setReg, $hs,*]) (by simp [setReg, callRegs, $hs,*])
    (by simp [setReg, callRegs, $hs,*]) (by simp [setReg, callRegs, $hs,*])
    (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*])
    (by simp [$hs,*]))

/-! ### Decimal digits in chunks of nine (`formatBase10`) -/

section
open Janus.Spec.Print

theorem length_decimal_ge : ∀ k n, 10 ^ k ≤ n → k + 1 ≤ (decimal n).length
  | 0, n, _ => length_decimal_pos n
  | k + 1, n, h => by
    have h10 : 10 ≤ n := Nat.le_trans (Nat.pow_le_pow_right (show 10 > 0 by decide) (by omega : 1 ≤ k + 1)) h
    rw [decimal_ge10 h10]
    have := length_decimal_ge k (n / 10) (by rw [Nat.le_div_iff_mul_le (by decide)]; rw [Nat.pow_succ] at h; exact h)
    simp; omega
/-- The nine digits of a chunk of `formatBase10`, zero-padded. -/
def digits9 (v : Nat) : List (BitVec 8) :=
  (List.range 9).reverse.map fun k => digit (v / 10 ^ k % 10)
theorem decimal_chunk (U : Nat) (h : 1000000000 ≤ U) :
    decimal U = decimal (U / 1000000000) ++ digits9 (U % 1000000000) := by
  have e : ∀ n, 10 ≤ n → decimal n = decimal (n / 10) ++ [digit (n % 10)] := fun n h => decimal_ge10 h
  rw [e U (by omega), e (U / 10) (by omega), e (U / 10 / 10) (by omega), e (U / 10 / 10 / 10) (by omega),
    e (U / 10 / 10 / 10 / 10) (by omega), e (U / 10 / 10 / 10 / 10 / 10) (by omega),
    e (U / 10 / 10 / 10 / 10 / 10 / 10) (by omega), e (U / 10 / 10 / 10 / 10 / 10 / 10 / 10) (by omega),
    e (U / 10 / 10 / 10 / 10 / 10 / 10 / 10 / 10) (by omega)]
  simp only [digits9, List.range_succ, List.range_zero, List.reverse_append, List.append_assoc, List.map,
    List.reverse_nil, List.reverse_cons, List.nil_append, List.cons_append, List.singleton_append]
  simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  congr 1
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (congr 1; omega)

theorem length_decimal_le : ∀ k n, n < 10 ^ (k + 1) → (decimal n).length ≤ k + 1
  | 0, n, h => by rw [decimal_lt10 (by simpa using h)]; simp
  | k + 1, n, h => by
    by_cases h10 : n < 10
    · rw [decimal_lt10 h10]; simp
    · rw [decimal_ge10 (by omega)]
      have := length_decimal_le k (n / 10) (by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h)
      simp; omega

theorem decimal_nine (U : Nat) (h1 : 100000000 ≤ U) (h2 : U < 1000000000) : decimal U = digits9 U := by
  have e : ∀ n, 10 ≤ n → decimal n = decimal (n / 10) ++ [digit (n % 10)] := fun n h => decimal_ge10 h
  rw [e U (by omega), e (U / 10) (by omega), e (U / 10 / 10) (by omega), e (U / 10 / 10 / 10) (by omega),
    e (U / 10 / 10 / 10 / 10) (by omega), e (U / 10 / 10 / 10 / 10 / 10) (by omega),
    e (U / 10 / 10 / 10 / 10 / 10 / 10) (by omega), e (U / 10 / 10 / 10 / 10 / 10 / 10 / 10) (by omega),
    decimal_lt10 (show U / 10 / 10 / 10 / 10 / 10 / 10 / 10 / 10 < 10 by omega)]
  simp only [digits9, List.range_succ, List.range_zero, List.append_assoc, List.map,
    List.reverse_nil, List.reverse_cons, List.nil_append, List.cons_append]
  simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  simp only [List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals (congr 1; omega)

end

/-- The nine bytes of a `formatBase10` chunk, in the order its loop writes them, read back. -/
theorem chunk_bytes (m : Memory) (p n w0 w1 w2 w3 w4 w5 w6 w7 w8 : Nat) :
    readBytes (((((((((m.writeLE (p + 7) 1 w7).writeLE (p + 8) 1 w8).writeLE (p + 5) 1 w5).writeLE
      (p + 6) 1 w6).writeLE (p + 3) 1 w3).writeLE (p + 4) 1 w4).writeLE (p + 1) 1 w1).writeLE
      (p + 2) 1 w2).writeLE p 1 w0) p (n + 9) =
      [BitVec.ofNat 8 w0, BitVec.ofNat 8 w1, BitVec.ofNat 8 w2, BitVec.ofNat 8 w3, BitVec.ofNat 8 w4,
        BitVec.ofNat 8 w5, BitVec.ofNat 8 w6, BitVec.ofNat 8 w7, BitVec.ofNat 8 w8] ++
        readBytes m (p + 9) n := by
  rw [show n + 9 = 9 + n by omega, readBytes_add]
  congr 1
  · simp only [readBytes, List.range_succ, List.range_zero, List.map, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, Memory.writeLE]
    simp +arith
  · repeat rw [readBytes_writeLE (by omega)]

/-- `and_sshr_lt` at the bit-vector level. -/
theorem and_sshr_lt_bv (x b : Nat) (hx : x < b) (hb : b ≤ 9223372036854775808) :
    BitVec.ofNat 64 x &&& (BitVec.ofNat 64 x - BitVec.ofNat 64 b).sshiftRight 63 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, and_sshr_lt' x b hx hb]
where
  and_sshr_lt' (x b : Nat) (hx : x < b) (hb : b ≤ 9223372036854775808) :
      (BitVec.ofNat 64 x).toNat &&& ((BitVec.ofNat 64 x - BitVec.ofNat 64 b).sshiftRight 63).toNat =
        (BitVec.ofNat 64 x).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
    exact and_sshr_lt x b hx hb

/-- `CMP #0; CNEG … LT`: the magnitude of a signed 64-bit value. -/
theorem cneg_toNat (v : BitVec 64) :
    (if 0 ≤ v.toInt then v else ~~~v + 1#64).toNat = v.toInt.natAbs := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hv := v.isLt
  split
  · rw [if_pos (by omega)]; omega
  · rw [if_neg (by omega)]
    rw [BitVec.toNat_add, BitVec.toNat_not]
    simp
    omega

/-- `TBZ #63`: the sign bit. -/
theorem getLsbD63 (v : BitVec 64) : v.getLsbD 63 = decide (9223372036854775808 ≤ v.toNat) := by
  have h := BitVec.msb_eq_decide v
  rw [BitVec.msb_eq_getLsbD_last] at h
  simpa using h

/-! ## The runtime state `print` and `println` need (arm64)

`PrintReady A rt below above adj s`: what a Go call state `s` of a function that prints must
satisfy, single-threaded, outside any other `print` (the M's print count 0). `A` holds the addresses
of the runtime's print globals in the binary (`runtime.panicking`, `printBacklogIndex`,
`printBacklog`, `overrideWrite`, `debuglock`), read off the code by the proof. `rt` are the
runtime-owned ranges the mutex contracts write (`Lock2Contract`, `Unlock2Contract`): the mutex key and
`m.locks` lie in them; everything else the print path reads lies outside them. The stack window
`[SP - below, SP + above)` holds every frame of the call (and the mutex contracts' windows). -/

/-- The addresses of the runtime's print globals (see `PrintReady`). -/
structure PrintGlobals where
  pk : Nat
  bi : Nat
  bl : Nat
  ow : Nat
  dl : Nat

open Janus.Spec in
/-- See the section doc. -/
def PrintReady (A : PrintGlobals) (rt : List (Nat × Nat)) (below above adj : Nat) (s : State) : Prop :=
  let SP := s.sp.toNat
  let G := (s.regs 28).toNat
  let MP := s.mem.readLE (G + gM) 8
  -- the stack and the stack-growth checks
  StackOK s below above ∧ GuardOK s adj ∧
  -- `g`: `stackguard0`, `g.m`, no `writebuf`
  0 < G ∧ G + 256 ≤ 2 ^ 48 ∧ s.mem.accessible (G + gM) 8 false = true ∧
  s.mem.accessible (G + gWritebuf) 16 false = true ∧ s.mem.readLE (G + gWritebuf) 8 = 0 ∧
  -- the M: `locks`, `dying`, the print count (0: outside any print)
  MP + 280 ≤ 2 ^ 48 ∧ s.mem.accessible (MP + mLocks) 16 true = true ∧
  s.mem.readLE (MP + mDying) 4 = 0 ∧ s.mem.readLE (MP + mPrintlock) 1 = 0 ∧
  s.mem.readLE (MP + mLocks) 4 + 4 < 2 ^ 31 ∧
  -- the globals: not panicking-dependent, the backlog index in range, no `overrideWrite`,
  -- `debuglock` free
  s.mem.accessible A.pk 4 false = true ∧ s.mem.accessible A.bi 8 true = true ∧
  s.mem.readLE A.bi 8 < 512 ∧ s.mem.accessible A.bl 512 true = true ∧
  s.mem.accessible A.ow 8 false = true ∧ s.mem.readLE A.ow 8 = 0 ∧
  s.mem.accessible A.dl 8 true = true ∧ ¬ lockHeld s.mem A.dl ∧
  -- what the mutex contracts may write, and what they may not
  InRanges A.dl 8 rt ∧ InRanges (MP + mLocks) 4 rt ∧
  Outside (SP - below) (below + above) rt ∧ Outside (G + 16) 8 rt ∧ Outside (G + gM) 8 rt ∧
  Outside (G + gWritebuf) 16 rt ∧ Outside (MP + mDying) 4 rt ∧ Outside (MP + mPrintlock) 1 rt ∧
  Outside A.pk 4 rt ∧ Outside A.bi 8 rt ∧ Outside A.bl 512 rt ∧ Outside A.ow 8 rt ∧
  -- the stack window, `g`'s and the M's fields and the globals apart
  Sep (SP - below) (below + above) [(G + 16, 8), (G + gM, 8), (G + gWritebuf, 16), (MP + mLocks, 16),
    (A.pk, 4), (A.bi, 8), (A.bl, 512), (A.ow, 8), (A.dl, 8)] ∧
  Sep (MP + mLocks) 16 [(G + 16, 8), (G + gM, 8), (G + gWritebuf, 16), (A.pk, 4), (A.bi, 8),
    (A.bl, 512), (A.ow, 8), (A.dl, 8)] ∧
  Sep (G + 16) 8 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧ Sep (G + gM) 8 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧
  Sep (G + gWritebuf) 16 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧ Sep A.dl 8 [(A.bi, 8), (A.bl, 512)]

/-- The runtime-owned ranges `rt` miss the program's read-only data (the strings and tables the
print functions read): a contract's frame (`MemFrame … rt`) then keeps them. -/
def DataOutside (p : Program) (rt : List (Nat × Nat)) : Prop :=
  ∀ d ∈ p.data, Outside d.base d.bytes.length rt

theorem DataOutside.of_dataRead {p : Program} {rt : List (Nat × Nat)} (h : DataOutside p rt)
    {a n : Nat} (hv : (dataRead p a n).isSome = true) : Outside a n rt := by
  unfold dataRead at hv
  cases hd : dataSegAt p a n with
  | none => rw [hd] at hv; cases hv
  | some d =>
    unfold dataSegAt at hd
    have hm := List.mem_of_find?_eq_some hd
    have hp := List.find?_some hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact Outside.of_sub (h d hm) hp.1 hp.2

/-- The bytes of the program's read-only data at `[a, a+n)`, from `DataLoaded` (the side
conditions are closed on literals by `decide +kernel`). -/
theorem readBytes_data {p : Program} {m : Memory} (h : p.DataLoaded m) (a n : Nat) (bs : Bytes)
    (hs : ∀ i, i < n → (dataRead p (a + i) 1).isSome = true)
    (hv : (List.range n).map (fun i => dataReadD p (a + i) 1) = bs.map BitVec.toNat) :
    readBytes m a n = bs := by
  have hl : bs.length = n := by
    have := congrArg List.length hv; simp at this; omega
  apply List.ext_getElem (by simp [readBytes, hl])
  intro i h1 h2
  simp only [readBytes, List.getElem_map, List.getElem_range]
  have hi : i < n := by simpa [readBytes] using h1
  have e := readLE_dataReadD h (a + i) 1 (hs i hi)
  rw [Memory.readLE_one] at e
  have e2 := congrArg (·[i]?) hv
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at e2
  rw [List.getElem?_eq_getElem h2] at e2
  simp only [Option.map_some, Option.some.injEq] at e2
  apply BitVec.eq_of_toNat_eq
  rw [e, e2]

end Janus.Print

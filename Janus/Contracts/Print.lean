import Janus.Contracts.Syscall

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

Everything above is plain Go (or Go assembly) and decodes, so it is **executed from the
binary** in the proofs (`examples/proofs-print`): `printlock`, `printunlock`, `printstring`,
`printsp`, `printnl`, `printbool`, `printuint`, `printint`, `printhex`, `printpointer`,
`printuintptr`, `printslice`, `printeface`, `printiface`, `internal/strconv.formatBase10`,
`gwrite`, `recordForPanic`, `writeErrData`, `write`, `write1`. Three runtime functions are
contracts (`janus extract --contract`), stated here:

* `runtime.lock2` / `runtime.unlock2`, the mutex under `printlock` (`Lock2Contract`,
  `Unlock2Contract`). Single-threaded, `printlock` only takes `runtime.debuglock` when the M's
  print count is 0, so the lock is free: the contract is the fast path (the key's lock bit set,
  `m.locks` one higher; the reverse for `unlock2`), with every other change confined to the
  runtime-owned ranges `rt`. Concurrency is out of scope; nothing here models a second thread.
* `runtime.memmove` (`MemmoveContract`): the copy `recordForPanic` makes of every piece into the
  512-byte crash backlog `runtime.printBacklog`.
* the float formatter `internal/strconv.genericFtoa` (`FtoaContract`), behind `printfloat64`,
  `printfloat32`, `printcomplex128`, `printcomplex64`: shortest round-trip formatting (Ryū) is
  long and its correctness is a theorem about the algorithm, so it is a contract whose output is
  the exact Go 1.26 format `Janus.Spec.Print.fmtF64`/`fmtF32` (a readable specification,
  differential-tested against the real runtime, `audit/rt-print`).

Every contract has a `_satisfiable` witness (`Janus.Contracts.PrintSat`).

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
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
      s' = retState s junk [] f v m ∧
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
    (hs : s'.fpsr = s.fpsr) : s' = retState s s'.regs [] s'.flags s'.vregs s'.mem := by
  cases s'
  simp only [retState] at *
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
  exact eq_retState (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl rfl rfl rfl)

/-- `ret_state [h, …]`: `ret_state` with the register equations `h, …` (for a state built on a
loop-head state `S` with `S.regs 28 = …`). -/
macro "ret_state" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact eq_retState (by simp [setReg, $hs,*]) (by simp [setReg, $hs,*]) (by simp [setReg, $hs,*])
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

end Janus.Print

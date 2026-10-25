import Janus.FFI
import Janus.Spec.Basic
import Janus.Contracts.Alloc

/-!
# The kernel as an environment: system calls, the vDSO clocks, traps (arm64)

Go code reaches Linux in three ways: the `SVC #0` instruction (arm64; `SYSCALL` on amd64, see
`Janus.Amd64.Kernel`), the reads of time and ID registers (`MRS CNTVCT_EL0`, ...), and calls of
the clock functions in the vDSO, code the kernel maps into the process that is not in the
binary (`runtime.nanotime1`, `runtime.walltime`). None of these is determined by the user-mode
state, so the plain semantics (`Arm64.step`) faults on them (`Fault.kernel`), and the extractor
puts a **`.syscall` stub** (`StubKind.syscall`) on each: on every such instruction inside an
extracted function, and at the entry of the vDSO clock functions (authenticated like every
runtime stub, by name and pinned code). This module gives the stubs a meaning.

## The model

* **The kernel state** `Kern` is part of the environment the theorems quantify over: an explicit
  **I/O trace** (`Kern.trace`: every write, read, open, close, clock reading, mapping, sleep,
  ... in order), the **input oracle** (`Kern.input fd`: the bytes later reads of `fd` will
  return, chosen by the environment), a lower bound of `CLOCK_MONOTONIC`, the process and thread
  IDs, the signal mask, the alternate signal stack, `PSTATE.DIT`, the CPU features Linux
  reports, the page size.
* **Per-system-call contracts** (`Safe`, `Effect`): for each supported call, a precondition
  (the buffers the kernel reads or writes are mapped, the arguments are representable) and the
  set of results it allows. They are relations, not functions: the kernel may make a short
  write, return fewer bytes than asked, fail with any `-errno`, pick any address for `mmap`,
  any wall-clock time. A theorem holds for **every** result the contract allows, so it holds
  for the real kernel exactly when the real kernel's behaviour is among them; the contracts are
  written to over-approximate Linux (see docs/SOUNDNESS.md, "Kernel trust boundary").
* **The kernel semantics** `ReturnsK p E post onExit s k`: every run from `s` with kernel state
  `k` returns satisfying `post`, where an ordinary instruction is executed by the model and a
  `.syscall` stub must be `SiteSafe` and then continues from **every** successor `SiteNext`
  allows (or ends the process: `exit_group`, where `onExit` must hold). `EnsuresK` is the Go
  function contract on top of it.
* **Traps** (`BRK`, `UDF`): `Traps p s` says the run from `s` ends at a trap instruction (the
  extractor puts a `.trap` stub on each; `Traps` checks the word there).

Supported system calls (`Sys`): `read`, `write`, `openat`, `close`, `exit_group`,
`clock_gettime`, `mmap`, `munmap`, `madvise`, `rt_sigprocmask`, `sigaltstack`, `sched_yield`,
`nanosleep`, `getpid`, `gettid`. Any other number is not `SiteSafe`: no theorem gets past it.

## Satisfiability

Every contract comes with witnesses (section "Witnesses"): `Effect.total` (whenever `Safe`
holds, some result is allowed: the semantics never gets stuck vacuously), one success witness
per call (`write_ok`, `read_ok`, ...: the interesting behaviour is allowed, e.g. a write of all
the bytes), `SiteNext.total` for every stub site, and the runtime contracts of the scheduler
hooks (`SchedContract`) and `convT64` are satisfied by concrete code (`schedContract_witness`,
`convT64Contract_witness`).
-/

namespace Janus.Kernel

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ## The kernel state (ISA-independent) -/

abbrev Bytes := List (BitVec 8)

/-- The `n` bytes of `m` at `a`. -/
def readBytes (m : Memory) (a n : Nat) : Bytes := (List.range n).map fun i => m.bytes (a + i)

/-- `m` with `bs` written at `a` (no permission check: the kernel's own copy-out, which the
contract only allows into memory it requires to be writable). -/
def writeBytes (m : Memory) (a : Nat) (bs : Bytes) : Memory :=
  { m with bytes := fun x => if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else m.bytes x }

/-- One entry of the I/O trace. `env` records a value the program read from the environment
(`CNTVCT_EL0`, `MIDR_EL1`, `CPUID`, `RDTSC`, ...). -/
inductive Event where
  | write (fd : Nat) (data : Bytes)
  | read (fd : Nat) (data : Bytes)
  | openat (dirfd : Nat) (path : Bytes) (flags mode : Nat) (fd : Nat)
  | close (fd : Nat)
  | clock (clk sec nsec : Nat)
  | mmap (addr len prot flags : Nat)
  | munmap (addr len : Nat)
  | madvise (addr len advice : Nat)
  | sigmask (mask : Nat)
  | sigaltstack (sp size : Nat)
  | yield
  | sleep (sec nsec : Nat)
  | env (what : String) (value : Nat)
deriving Repr, DecidableEq, Inhabited

/-- The kernel state a run starts in (and every kernel step updates). Theorems quantify over it:
the defaults only fill in concrete states for tests and witnesses. -/
structure Kern where
  /-- Everything the program did through the kernel, oldest first. -/
  trace : List Event := []
  /-- The input oracle: the bytes later reads of `fd` return (consumed from the front). -/
  input : Nat → Bytes := fun _ => []
  /-- A lower bound of the current `CLOCK_MONOTONIC` time, in nanoseconds: the last reading
  (or the sum after a sleep). -/
  mono : Nat := 0
  /-- A lower bound of `CNTVCT_EL0` (arm64): the last reading. -/
  cntvct : Nat := 0
  /-- `CNTFRQ_EL0` (arm64), a constant of the system. -/
  cntfrq : Nat := 0
  pid : Nat := 1
  tid : Nat := 1
  /-- The blocked-signal set (`rt_sigprocmask`), 64 bits. -/
  sigmask : Nat := 0
  /-- The alternate signal stack (`sigaltstack`): base and size; `(0, 0)` is disabled. -/
  altstack : Nat × Nat := (0, 0)
  /-- `PSTATE.DIT` (arm64). -/
  dit : Bool := false
  /-- Linux emulates `MRS MIDR_EL1` at EL0 (`HWCAP_CPUID`); otherwise it is `SIGILL`. -/
  midrOK : Bool := true
  /-- The CPU implements `FEAT_DIT`; otherwise `MRS`/`MSR DIT` are `SIGILL`. -/
  ditOK : Bool := true
  /-- amd64: `RDTSC`/`RDTSCP` are allowed at CPL 3 (`CR4.TSD = 0`, `PR_SET_TSC`). -/
  tscOK : Bool := true
  /-- amd64: `XGETBV` is enabled (`CR4.OSXSAVE`). -/
  xgetbvOK : Bool := true
  /-- amd64: `XCR0`, a constant of the system. -/
  xcr0 : Nat := 3
  /-- The page size (4096 on amd64; 4096, 16384 or 65536 on arm64). -/
  pageSize : Nat := 4096

/-- The bytes written to `fd` by the trace `es`, in order. -/
def outputOf (fd : Nat) : List Event → Bytes
  | [] => []
  | .write f d :: es => (if f = fd then d else []) ++ outputOf fd es
  | _ :: es => outputOf fd es

/-- The bytes the program has written to `fd`: its output trace. -/
def Kern.output (k : Kern) (fd : Nat) : Bytes := outputOf fd k.trace

/-- `k` with `e` appended to the trace. -/
def Kern.emit (k : Kern) (e : Event) : Kern := { k with trace := k.trace ++ [e] }

theorem outputOf_append (fd : Nat) (es es' : List Event) :
    outputOf fd (es ++ es') = outputOf fd es ++ outputOf fd es' := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [outputOf, ih]

@[simp] theorem Kern.output_emit_write (k : Kern) (fd fd' : Nat) (d : Bytes) :
    (k.emit (.write fd d)).output fd' = k.output fd' ++ (if fd = fd' then d else []) := by
  simp [Kern.emit, Kern.output, outputOf_append, outputOf]

/-- The trace a program produced between two kernel states: `k'.trace = k.trace ++ new`. -/
def Kern.Extends (k k' : Kern) (new : List Event) : Prop := k'.trace = k.trace ++ new

/-- Raw results `-4095 … -1` (as 64-bit values): a failed system call, `-errno`. -/
def IsErr (r : Nat) : Prop := 2 ^ 64 - 4095 ≤ r ∧ r < 2 ^ 64

/-- `f` with `i ↦ v`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

/-- A NUL-terminated string of `len < 4096` bytes (`PATH_MAX`) at `a`, readable with its
terminator. -/
def CStr (m : Memory) (a len : Nat) : Prop :=
  len < 4096 ∧ m.accessible a (len + 1) false = true ∧ (m.bytes (a + len)).toNat = 0 ∧
    ∀ i < len, (m.bytes (a + i)).toNat ≠ 0

/-- `n` bytes at `a` are mapped (readable, or writable if `w`); nothing for `n = 0`. -/
def Buf (m : Memory) (a n : Nat) (w : Bool) : Prop := n = 0 ∨ m.accessible a n w = true

/-- `n` rounded up to a multiple of `ps`. -/
def roundUp (n ps : Nat) : Nat := (n + ps - 1) / ps * ps

/-- `[a, a + n)` and the region `r` are disjoint. -/
def disjointRegion (a n : Nat) (r : Region) : Bool := a + n ≤ r.base || r.base + r.size ≤ a

/-! ## The system calls -/

/-- The supported system calls. -/
inductive Sys where
  | read | write | openat | close | exitGroup | clockGettime | mmap | munmap | madvise
  | rtSigprocmask | sigaltstack | schedYield | nanosleep | getpid | gettid
deriving Repr, DecidableEq, Inhabited

/-- arm64 system call numbers (`include/uapi/asm-generic/unistd.h`). -/
def Sys.ofArm64 : Nat → Option Sys
  | 63 => some .read | 64 => some .write | 56 => some .openat | 57 => some .close
  | 94 => some .exitGroup | 113 => some .clockGettime | 222 => some .mmap | 215 => some .munmap
  | 233 => some .madvise | 135 => some .rtSigprocmask | 132 => some .sigaltstack
  | 124 => some .schedYield | 101 => some .nanosleep | 172 => some .getpid | 178 => some .gettid
  | _ => none

/-- amd64 system call numbers (`arch/x86/entry/syscalls/syscall_64.tbl`). -/
def Sys.ofAmd64 : Nat → Option Sys
  | 0 => some .read | 1 => some .write | 257 => some .openat | 3 => some .close
  | 231 => some .exitGroup | 228 => some .clockGettime | 9 => some .mmap | 11 => some .munmap
  | 28 => some .madvise | 14 => some .rtSigprocmask | 131 => some .sigaltstack
  | 24 => some .schedYield | 35 => some .nanosleep | 39 => some .getpid | 186 => some .gettid
  | _ => none

/-- `CLOCK_REALTIME` and `CLOCK_MONOTONIC`, the clocks Go reads. -/
def clockRealtime : Nat := 0
def clockMonotonic : Nat := 1

/-- `MAP_FIXED`, `MAP_ANONYMOUS`; `PROT_READ`, `PROT_WRITE`. -/
def mapFixed : Nat := 0x10
def mapAnon : Nat := 0x20
def flagSet (v f : Nat) : Bool := v &&& f != 0

/-- The precondition of a system call with arguments `a 0 … a 5` (the raw 64-bit values) in
kernel state `k` and memory `m`: what the program must establish for the call to be inside the
contract. -/
def Safe (sc : Sys) (a : Nat → Nat) (k : Kern) (m : Memory) : Prop :=
  match sc with
  | .write => Buf m (a 1) (a 2) false
  | .read => Buf m (a 1) (a 2) true
  | .openat => ∃ len, CStr m (a 1) len
  | .close => True
  | .exitGroup => True
  | .clockGettime => m.accessible (a 1) 16 true = true
  | .mmap =>
    -- a hint below 2^47 (the kernel then returns a lower-half address on both ISAs), and no
    -- `MAP_FIXED` over memory the model knows about (the model cannot split its regions)
    0 < a 1 ∧ a 0 + a 1 ≤ 2 ^ 47 ∧
      (flagSet (a 3) mapFixed → m.regions.all (disjointRegion (a 0) (roundUp (a 1) k.pageSize)))
  | .munmap =>
    -- whole pages, and every region of the model either inside or disjoint
    0 < k.pageSize ∧ a 0 % k.pageSize = 0 ∧ a 1 % k.pageSize = 0 ∧
      m.regions.all (fun r => disjointRegion (a 0) (a 1) r ||
        (a 0 ≤ r.base && r.base + r.size ≤ a 0 + a 1))
  | .madvise => 0 < k.pageSize
  | .rtSigprocmask =>
    a 3 = 8 ∧ (a 1 = 0 ∨ m.accessible (a 1) 8 false = true) ∧
      (a 2 = 0 ∨ m.accessible (a 2) 8 true = true)
  | .sigaltstack =>
    (a 0 = 0 ∨ m.accessible (a 0) 24 false = true) ∧ (a 1 = 0 ∨ m.accessible (a 1) 24 true = true)
  | .schedYield => True
  | .nanosleep => m.accessible (a 0) 16 false = true ∧ (a 1 = 0 ∨ m.accessible (a 1) 16 true = true)
  | .getpid => True
  | .gettid => True

/-- The new signal mask of `rt_sigprocmask(how, set)` (`SIG_BLOCK` 0, `SIG_UNBLOCK` 1,
`SIG_SETMASK` 2): `SIGKILL` (bit 8) and `SIGSTOP` (bit 18) can never be blocked. -/
def newMask (old how set : Nat) : Nat :=
  let v := if how = 0 then old ||| set else if how = 1 then old &&& (2 ^ 64 - 1 - set) else set
  v % 2 ^ 64 &&& (2 ^ 64 - 1 - 2 ^ 8 - 2 ^ 18)

/-- The results a system call allows: from kernel state `k` and memory `m` to `k'`, `m'` and
the raw result `r` (the value of `X0`/`RAX`; `IsErr r` is `-errno`). Every call may fail
(except the few Linux defines as infallible: `getpid`, `gettid`, `sched_yield`, `clock_gettime`
of `CLOCK_REALTIME`/`CLOCK_MONOTONIC` with a writable buffer); a failure changes nothing. -/
def Effect (sc : Sys) (a : Nat → Nat) (k : Kern) (m : Memory) (k' : Kern) (m' : Memory)
    (r : Nat) : Prop :=
  match sc with
  | .write =>
    -- a write of `c ≤ n` bytes (short writes allowed), appended to the fd's output
    m' = m ∧ ((∃ c ≤ a 2, r = c ∧ k' = k.emit (.write (a 0) (readBytes m (a 1) c))) ∨
      (IsErr r ∧ k' = k))
  | .read =>
    -- the next `c ≤ n` bytes of the fd's input, copied to the buffer
    (∃ c ≤ a 2, c ≤ (k.input (a 0)).length ∧ r = c ∧
        k' = { k.emit (.read (a 0) ((k.input (a 0)).take c)) with
                input := upd k.input (a 0) ((k.input (a 0)).drop c) } ∧
        m' = writeBytes m (a 1) ((k.input (a 0)).take c)) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .openat =>
    -- a new descriptor whose input the environment chooses
    m' = m ∧ ((∃ len fd content, CStr m (a 1) len ∧ fd < 2 ^ 31 ∧ r = fd ∧
        k' = { k.emit (.openat (a 0) (readBytes m (a 1) len) (a 2) (a 3) fd) with
                input := upd k.input fd content }) ∨
      (IsErr r ∧ k' = k))
  | .close =>
    m' = m ∧ (r = 0 ∨ IsErr r) ∧ k' = { k.emit (.close (a 0)) with input := upd k.input (a 0) [] }
  | .exitGroup => False
  | .clockGettime =>
    (∃ sec nsec, nsec < 10 ^ 9 ∧ sec < 2 ^ 63 ∧ r = 0 ∧
        m' = (m.writeLE (a 1) 8 sec).writeLE (a 1 + 8) 8 nsec ∧
        (a 0 = clockMonotonic →
          k.mono ≤ sec * 10 ^ 9 + nsec ∧ sec * 10 ^ 9 + nsec < 2 ^ 63 ∧
          k' = { k.emit (.clock (a 0) sec nsec) with mono := sec * 10 ^ 9 + nsec }) ∧
        (a 0 ≠ clockMonotonic → k' = k.emit (.clock (a 0) sec nsec))) ∨
      (a 0 ≠ clockRealtime ∧ a 0 ≠ clockMonotonic ∧ IsErr r ∧ k' = k ∧ m' = m)
  | .mmap =>
    -- a fresh mapping at a page-aligned address, disjoint from every region; readable (and
    -- writable with `PROT_WRITE`) when `PROT_READ` or `PROT_WRITE` is set; zero when anonymous
    (∃ base, r = base ∧ 0 < k.pageSize ∧ base % k.pageSize = 0 ∧
        base + roundUp (a 1) k.pageSize ≤ 2 ^ 47 ∧
        (flagSet (a 3) mapFixed → base = a 0) ∧
        m.regions.all (disjointRegion base (roundUp (a 1) k.pageSize)) = true ∧
        m'.regions = m.regions ++
          (if flagSet (a 2) 3 then [⟨base, a 1, flagSet (a 2) 2⟩] else []) ∧
        (∀ x, ¬ (base ≤ x ∧ x < base + roundUp (a 1) k.pageSize) → m'.bytes x = m.bytes x) ∧
        (flagSet (a 3) mapAnon →
          ∀ x, base ≤ x → x < base + roundUp (a 1) k.pageSize → m'.bytes x = 0) ∧
        k' = k.emit (.mmap base (a 1) (a 2) (a 3))) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .munmap =>
    (r = 0 ∧ m' = { m with regions := m.regions.filter (disjointRegion (a 0) (a 1)) } ∧
        k' = k.emit (.munmap (a 0) (a 1))) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .madvise =>
    -- the advised pages may lose their contents (`MADV_DONTNEED`, `MADV_FREE`, ...)
    (a 0 % k.pageSize = 0 ∧ (r = 0 ∨ IsErr r) ∧ m'.regions = m.regions ∧
        (∀ x, ¬ (a 0 ≤ x ∧ x < a 0 + roundUp (a 1) k.pageSize) → m'.bytes x = m.bytes x) ∧
        k' = k.emit (.madvise (a 0) (a 1) (a 2))) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .rtSigprocmask =>
    (r = 0 ∧ (a 1 = 0 ∨ a 0 ≤ 2) ∧
        let mask := if a 1 = 0 then k.sigmask else newMask k.sigmask (a 0) (m.readLE (a 1) 8)
        k' = { k.emit (.sigmask mask) with sigmask := mask } ∧
        m' = if a 2 = 0 then m else m.writeLE (a 2) 8 k.sigmask) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .sigaltstack =>
    -- the old stack (`ss_sp` at 0, `ss_size` at 16; the flags word and padding unspecified)
    (r = 0 ∧ m'.regions = m.regions ∧
        (a 1 = 0 → m' = m) ∧
        (a 1 ≠ 0 → (∀ x, ¬ (a 1 ≤ x ∧ x < a 1 + 24) → m'.bytes x = m.bytes x) ∧
          m'.readLE (a 1) 8 = k.altstack.1 ∧ m'.readLE (a 1 + 16) 8 = k.altstack.2) ∧
        k' = if a 0 = 0 then k else
          let st := if m.readLE (a 0 + 8) 4 = 2 then (0, 0)
                    else (m.readLE (a 0) 8, m.readLE (a 0 + 16) 8)
          { k.emit (.sigaltstack st.1 st.2) with altstack := st }) ∨
      (IsErr r ∧ k' = k ∧ m' = m)
  | .schedYield => r = 0 ∧ m' = m ∧ k' = k.emit .yield
  | .nanosleep =>
    -- a completed sleep advances the monotonic clock by at least the request
    (r = 0 ∧ m' = m ∧ m.readLE (a 0 + 8) 8 < 10 ^ 9 ∧
        k' = { k.emit (.sleep (m.readLE (a 0) 8) (m.readLE (a 0 + 8) 8)) with
                mono := k.mono + m.readLE (a 0) 8 * 10 ^ 9 + m.readLE (a 0 + 8) 8 }) ∨
      (IsErr r ∧ k' = k ∧ m'.regions = m.regions ∧
        (∀ x, ¬ (a 1 ≠ 0 ∧ a 1 ≤ x ∧ x < a 1 + 16) → m'.bytes x = m.bytes x))
  | .getpid => r = k.pid ∧ k' = k ∧ m' = m
  | .gettid => r = k.tid ∧ k' = k ∧ m' = m

/-! ## arm64: the stub sites -/

/-- What a `.syscall` stub stands for. -/
inductive Site where
  /-- `SVC #0`. -/
  | svc
  /-- `MRS Xt, r` of an environment register. -/
  | mrs (r : EnvReg) (rt : Nat)
  /-- `MSR DIT, #b`. -/
  | ditImm (b : Nat)
  /-- `MSR DIT, Xt`. -/
  | ditReg (rt : Nat)
  /-- `runtime.walltime` (ABI0): `CLOCK_REALTIME` through the vDSO. -/
  | walltime
  /-- `runtime.nanotime1` (ABI0): `CLOCK_MONOTONIC` through the vDSO. -/
  | nanotime
deriving Repr, DecidableEq, Inhabited

/-- The vDSO clock functions, by their linked names (stubs at their entries). -/
def walltimeName : String := "runtime.walltime.abi0"
def nanotimeName : String := "runtime.nanotime1.abi0"

/-- The site of the `.syscall` stub `name` at `pc`: a vDSO clock function by name, otherwise the
instruction at `pc` (which must be an `SVC #0` or an environment `MRS`/`MSR`). -/
def siteOf (p : Program) (name : String) (pc : Nat) : Option Site :=
  if name = walltimeName then some .walltime
  else if name = nanotimeName then some .nanotime
  else match p.fetch pc with
    | some w =>
      match decode w with
      | some (.svc 0) => some .svc
      | some (.mrsEnv r rt) => some (.mrs r rt)
      | some (.msrDitImm b) => some (.ditImm b)
      | some (.msrDitReg rt) => some (.ditReg rt)
      | _ => none
    | none => none

theorem siteOf_link {p : Program} (impl : List Segment) {name : String} {pc : Nat} {site : Site}
    (h : siteOf p name pc = some site) : siteOf (p.link impl) name pc = some site := by
  unfold siteOf at h ⊢
  split
  · rename_i h1; rw [if_pos h1] at h; exact h
  · rename_i h1; rw [if_neg h1] at h
    split
    · rename_i h2; rw [if_pos h2] at h; exact h
    · rename_i h2; rw [if_neg h2] at h
      cases hf : p.fetch pc with
      | none => rw [hf] at h; cases h
      | some w => rw [hf] at h; rw [Program.fetch_link impl hf]; exact h

@[simp] theorem siteOf_withExit (p : Program) (ret : Nat) (name : String) (pc : Nat) :
    siteOf (p.withExit ret) name pc = siteOf p name pc := rfl

/-- The parameters of the vDSO clock contracts: the runtime-owned ranges `rt` (the `m` and the
`g0`/`gsignal` stacks they write) and the stack bytes `stack` below `SP` they may use (when
already on `g0`). -/
structure KEnv where
  rt : List (Nat × Nat)
  stack : Nat

/-- The system call `X8` names. -/
def svcSys (s : State) : Option Sys := Sys.ofArm64 (s.regs 8).toNat

/-- The arguments `X0 … X5`. -/
def argsOf (s : State) : Nat → Nat := fun i => (s.regs i).toNat

/-- The state after `SVC #0` returns `r` with memory `m'`: only `X0` changes (Linux arm64
preserves every other register, the flags and the SIMD&FP registers), `pc + 4`. -/
def afterSvc (s : State) (r : Nat) (m' : Memory) : State :=
  { s with regs := setReg s.regs 0 (BitVec.ofNat 64 r), pc := s.pc + 4, mem := m' }

attribute [janus_exec, janus_post] afterSvc

/-- How an ABI0 vDSO clock function returns: to `X30`, with `SP`, `g` (`X28`) and `FP` (`X29`)
restored and memory `m` that differs from `s.mem` only inside the runtime-owned ranges, the
stack window below `SP` and the result slots `slots`; every other register, the flags, the
SIMD&FP registers and `FPSR` unspecified (`FPCR`, `TPIDR_EL0`, `DCZID_EL0` unchanged). -/
def VdsoRet (E : KEnv) (s s' : State) (slots : List (Nat × Nat)) (Q : Memory → Prop) : Prop :=
  ∃ regs flags vregs fpsr m,
    s' = { s with regs := regs, pc := s.regs 30, flags := flags, vregs := vregs, fpsr := fpsr,
                  mem := m } ∧
    regs 28 = s.regs 28 ∧ regs 29 = s.regs 29 ∧
    MemFrame s.mem m (E.rt ++ [(s.sp.toNat - E.stack, s.sp.toNat)] ++ slots) ∧ Q m

/-- What a stub site needs. -/
def SiteSafe (E : KEnv) (s : State) (k : Kern) : Site → Prop
  | .svc => ∃ sc, svcSys s = some sc ∧ sc ≠ .exitGroup ∧ Safe sc (argsOf s) k s.mem
  | .mrs .cntvct _ => True
  | .mrs .cntfrq _ => True
  | .mrs .midr _ => k.midrOK = true
  | .mrs .dit _ => k.ditOK = true
  | .ditImm b => k.ditOK = true ∧ b ≤ 1
  | .ditReg _ => k.ditOK = true
  | .walltime => Contracts.CallOK s E.stack 2
  | .nanotime => Contracts.CallOK s E.stack 1

/-- The successors a stub site allows. -/
def SiteNext (E : KEnv) (s : State) (k : Kern) (s' : State) (k' : Kern) : Site → Prop
  | .svc => ∃ sc m' r, svcSys s = some sc ∧ Effect sc (argsOf s) k s.mem k' m' r ∧
      s' = afterSvc s r m'
  | .mrs .cntvct rt => ∃ v, k.cntvct ≤ v ∧ v < 2 ^ 64 ∧
      k' = { k.emit (.env "CNTVCT_EL0" v) with cntvct := v } ∧
      s' = (s.writeZR rt (BitVec.ofNat 64 v)).next
  | .mrs .cntfrq rt => k' = k ∧ s' = (s.writeZR rt (BitVec.ofNat 64 k.cntfrq)).next
  | .mrs .midr rt => ∃ v, v < 2 ^ 32 ∧ k' = k.emit (.env "MIDR_EL1" v) ∧
      s' = (s.writeZR rt (BitVec.ofNat 64 v)).next
  | .mrs .dit rt => k' = k ∧ s' = (s.writeZR rt (if k.dit then BitVec.ofNat 64 (2 ^ 24) else 0)).next
  | .ditImm b => k' = { k with dit := b == 1 } ∧ s' = s.next
  | .ditReg rt => k' = { k with dit := (s.readZR rt).getLsbD 24 } ∧ s' = s.next
  | .walltime => ∃ sec nsec, nsec < 10 ^ 9 ∧ sec < 2 ^ 63 ∧ k' = k.emit (.clock 0 sec nsec) ∧
      VdsoRet E s s' [(s.sp.toNat + 8, s.sp.toNat + 20)] fun m =>
        m.readLE (s.sp.toNat + 8) 8 = sec ∧ m.readLE (s.sp.toNat + 16) 4 = nsec
  | .nanotime => ∃ sec nsec, nsec < 10 ^ 9 ∧ k.mono ≤ sec * 10 ^ 9 + nsec ∧
      sec * 10 ^ 9 + nsec < 2 ^ 63 ∧
      k' = { k.emit (.clock 1 sec nsec) with mono := sec * 10 ^ 9 + nsec } ∧
      VdsoRet E s s' [(s.sp.toNat + 8, s.sp.toNat + 16)] fun m =>
        m.readLE (s.sp.toNat + 8) 8 = sec * 10 ^ 9 + nsec

/-- A stub site that ends the process: `exit_group(code)`. -/
def SiteExit (s : State) (code : Nat) : Site → Prop
  | .svc => svcSys s = some .exitGroup ∧ code = (s.regs 0).toNat
  | _ => False

/-! ## The kernel semantics -/

/-- Every run from `s` with kernel state `k` returns (reaches `p.exitAddr`) in a state and kernel
state satisfying `post`, or ends the process with `exit_group(code)` in a kernel state where
`onExit code` holds, after finitely many steps. An ordinary instruction is executed by the model;
a `.syscall` stub must be `SiteSafe` and continues from **every** successor `SiteNext` allows.
Faults, traps, panics, `morestack` and external stubs are excluded, as for `Returns`. -/
inductive ReturnsK (p : Program) (E : KEnv) (post : State → Kern → Prop)
    (onExit : Nat → Kern → Prop) : State → Kern → Prop where
  | exit {s : State} {k : Kern} (hx : s.pc.toNat = p.exitAddr) (hp : post s k) :
      ReturnsK p E post onExit s k
  | step {s s' : State} {k : Kern} {w : Nat} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = none) (hf : p.fetch s.pc.toNat = some w)
      (hst : Arm64.step w s = .ok s') (h : ReturnsK p E post onExit s' k) :
      ReturnsK p E post onExit s k
  | sys {s : State} {k : Kern} {st : Stub} {site : Site} (hx : s.pc.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.pc.toNat = some st) (hk : st.kind = .syscall)
      (hsite : siteOf p st.name s.pc.toNat = some site) (hsafe : SiteSafe E s k site)
      (h : ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') :
      ReturnsK p E post onExit s k
  | halt {s : State} {k : Kern} {st : Stub} {site : Site} {code : Nat}
      (hx : s.pc.toNat ≠ p.exitAddr) (hs : p.stubAt s.pc.toNat = some st)
      (hk : st.kind = .syscall) (hsite : siteOf p st.name s.pc.toNat = some site)
      (he : SiteExit s code site) (hp : onExit code k) : ReturnsK p E post onExit s k

namespace ReturnsK

variable {p : Program} {E : KEnv} {P Q : State → Kern → Prop} {X Y : Nat → Kern → Prop}

theorem mono {s : State} {k : Kern} (h : ReturnsK p E P X s k) (hPQ : ∀ s k, P s k → Q s k)
    (hXY : ∀ c k, X c k → Y c k) : ReturnsK p E Q Y s k := by
  induction h with
  | exit hx hp => exact .exit hx (hPQ _ _ hp)
  | step hx hs hf hst _ ih => exact .step hx hs hf hst ih
  | sys hx hs hk hsite hsafe _ ih => exact .sys hx hs hk hsite hsafe ih
  | halt hx hs hk hsite he hp => exact .halt hx hs hk hsite he (hXY _ _ hp)

/-- Ordinary steps first. -/
theorem of_steps {s s' : State} {k : Kern} {n : Nat} (hs : Program.Steps p s n s')
    (h : ReturnsK p E P X s' k) : ReturnsK p E P X s k := by
  induction hs with
  | refl => exact h
  | step hx hst hf he _ ih => exact .step hx hst hf he (ih h)

/-- `Returns` (no kernel call on the way) implies `ReturnsK` for every kernel state, which it
leaves unchanged. -/
theorem of_returns {s : State} {k : Kern} {post : State → Prop} (h : Returns p s post) :
    ReturnsK p E (fun s' k' => post s' ∧ k' = k) X s k := by
  obtain ⟨n, s', hr, hp⟩ := h
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx ⟨hp, rfl⟩
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.pc.toNat with
      | some st => simp only [hst] at hr; cases hr
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Arm64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

end ReturnsK

/-! ### Running under the kernel semantics with `janus_run`

`ReturnsK.of_reaches` turns a `ReturnsK` goal into `Reaches p s (IsReturnK …)`: `janus_run`
stops at the exit address (goal: `post`) or at a `.syscall` stub (goal: the site, its
precondition, and every successor). Prove the site with `decide` (`siteOf` evaluates on the
closed program), the precondition, introduce the successor, and continue with
`apply ReturnsK.of_reaches` and `janus_run`. -/

/-- The outcome predicate of `ReturnsK`. -/
def IsReturnK (p : Program) (E : KEnv) (post : State → Kern → Prop) (onExit : Nat → Kern → Prop)
    (k : Kern) : Outcome → Prop
  | .returned s => post s k
  | .stub f .syscall s => ∃ site, siteOf p f s.pc.toNat = some site ∧
      ((SiteSafe E s k site ∧ ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') ∨
        ∃ code, SiteExit s code site ∧ onExit code k)
  | .stub _ _ _ => False

@[simp, janus_post] theorem isReturnK_returned (p : Program) (E : KEnv) (post : State → Kern → Prop)
    (onExit : Nat → Kern → Prop) (k : Kern) (s : State) :
    IsReturnK p E post onExit k (.returned s) = post s k := rfl
@[simp, janus_post] theorem isReturnK_syscall (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) :
    IsReturnK p E post onExit k (.stub f .syscall s) =
      ∃ site, siteOf p f s.pc.toNat = some site ∧
        ((SiteSafe E s k site ∧ ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') ∨
          ∃ code, SiteExit s code site ∧ onExit code k) := rfl
@[simp, janus_post] theorem isReturnK_panic (p : Program) (E : KEnv) (post : State → Kern → Prop)
    (onExit : Nat → Kern → Prop) (k : Kern) (f : String) (s : State) :
    IsReturnK p E post onExit k (.stub f .panic s) = False := rfl
@[simp, janus_post] theorem isReturnK_morestack (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .morestack s) = False := rfl
@[simp, janus_post] theorem isReturnK_external (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .external s) = False := rfl
@[simp, janus_post] theorem isReturnK_trap (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .trap s) = False := rfl

theorem ReturnsK.of_reaches {p : Program} {E : KEnv} {post : State → Kern → Prop}
    {onExit : Nat → Kern → Prop} {s : State} {k : Kern}
    (h : Reaches p s (IsReturnK p E post onExit k)) : ReturnsK p E post onExit s k := by
  obtain ⟨n, o, hr, hq⟩ := h
  induction n generalizing s with
  | zero => simp at hr
  | succ n ih =>
    rw [Program.run_succ] at hr
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hq
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.pc.toNat with
      | some st =>
        simp only [hst] at hr; cases hr
        cases hk : st.kind with
        | syscall =>
          rw [hk] at hq
          obtain ⟨site, hsite, hq⟩ := hq
          rcases hq with ⟨hsafe, hn⟩ | ⟨code, he, hp⟩
          · exact .sys hx hst hk hsite hsafe hn
          · exact .halt hx hst hk hsite he hp
        | panic => rw [hk] at hq; exact hq.elim
        | morestack => rw [hk] at hq; exact hq.elim
        | external => rw [hk] at hq; exact hq.elim
        | trap => rw [hk] at hq; exact hq.elim
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Arm64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

/-! ## Specifications -/

/-- The Go function contract under the kernel semantics: for **every** admissible return
address, **every** Go call state with these arguments and **every** kernel state satisfying
`pre`, every run returns to `ret` restoring `SP`, `g` and `FP` (`FFI.ABIReturnC`: the vDSO is
C code, which may use `X18`) and satisfying `post s k s' k'`, or ends the process with
`exit_group(code)` where `onExit s k code k'` holds (by default never: the function must
return). -/
def EnsuresK (p : Program) (E : KEnv) (entry : Nat) (args : List W64)
    (pre : State → Kern → Prop) (post : State → Kern → State → Kern → Prop)
    (onExit : State → Kern → Nat → Kern → Prop := fun _ _ _ _ => False) : Prop :=
  ∀ ret, GoABI.RetAddr p ret → ∀ s k, GoABI.CallSetup (p.withExit ret) entry args s → pre s k →
    ReturnsK (p.withExit ret) E (fun s' k' => FFI.ABIReturnC s s' ∧ post s k s' k')
      (onExit s k) s k

/-! ## Traps -/

/-- The word at `pc` is a trap instruction (`BRK`, `UDF`). -/
def trapAt (p : Program) (pc : Nat) : Bool :=
  match p.fetch pc with
  | some w =>
    match decode w with
    | some (.brk _) => true
    | some (.udf _) => true
    | _ => false
  | none => false

/-- The outcome is a `.trap` stub at a trap instruction. -/
def IsTrap (p : Program) : Outcome → Prop
  | .stub _ .trap s => trapAt p s.pc.toNat = true
  | _ => False

/-- **The run from `s` ends in a trap**: it reaches a trap instruction (`BRK`: `SIGTRAP`,
`UDF`: `SIGILL`), never a return, panic or fault before it. -/
def Traps (p : Program) (s : State) : Prop := Reaches p s (IsTrap p)

@[simp, janus_post] theorem isTrap_trap (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .trap s) = (trapAt p s.pc.toNat = true) := rfl
@[simp, janus_post] theorem isTrap_returned (p : Program) (s : State) :
    IsTrap p (.returned s) = False := rfl
@[simp, janus_post] theorem isTrap_panic (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .panic s) = False := rfl
@[simp, janus_post] theorem isTrap_morestack (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .morestack s) = False := rfl
@[simp, janus_post] theorem isTrap_external (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .external s) = False := rfl
@[simp, janus_post] theorem isTrap_syscall (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .syscall s) = False := rfl

theorem trapAt_link {p : Program} (impl : List Segment) {pc : Nat} (h : trapAt p pc = true) :
    trapAt (p.link impl) pc = true := by
  unfold trapAt at h ⊢
  cases hf : p.fetch pc with
  | none => rw [hf] at h; cases h
  | some w => rw [hf] at h; rw [Program.fetch_link impl hf]; exact h

@[simp] theorem trapAt_withExit (p : Program) (ret pc : Nat) :
    trapAt (p.withExit ret) pc = trapAt p pc := rfl

/-- A trap stub stands for a fault: the instruction at the stub, executed, faults with
`Fault.trap` (so the stub ends the run exactly where the hardware raises the signal). -/
theorem trapAt_faults {p : Program} {pc : Nat} (h : trapAt p pc = true) (s : State)
    (hpc : s.pc.toNat = pc) :
    ∃ w sig, p.fetch pc = some w ∧ Arm64.step w s = .error (.trap pc sig) := by
  unfold trapAt at h
  split at h
  · rename_i w hf
    split at h
    · rename_i imm hd
      exact ⟨w, 5, hf, by rw [Arm64.step_of_decode hd]; simp [exec, hpc]⟩
    · rename_i imm hd
      exact ⟨w, 4, hf, by rw [Arm64.step_of_decode hd]; simp [exec, hpc]⟩
    · cases h
  · cases h

/-! ## Runtime contracts around system calls

`syscall.Syscall` brackets the raw call with the scheduler hooks `runtime.entersyscall` and
`runtime.exitsyscall` (the P is handed off during the call and reacquired after). They are
runtime contracts (`--contract`, `Program.contracts`): `SchedContract` says they return
preserving the Go ABI registers, writing only runtime-owned memory and their stack window.
`ConvT64Contract` is `runtime.convT64(v)`, the boxing of an `Errno` into an `error` on the error
path of the `syscall` wrappers: it returns a pointer to 8 readable bytes holding `v`. -/

open Janus.Contracts Janus.Tactic in
/-- **`runtime.entersyscall()`, `runtime.exitsyscall()`** (arm64): return to `X30` with `R18`,
`g`, `FP` preserved, every other register, the flags and the SIMD&FP registers unspecified,
and memory changed only inside the runtime-owned ranges `rt` and the stack window. -/
def SchedContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK s stack 0)
    (fun s s' => AllocRet rt stack 0 (fun _ => []) s s' fun _ _ => True)

open Janus.Contracts Janus.Tactic in
/-- **`runtime.convT64(v)`** (arm64; `X0 = v`): a pointer to 8 readable bytes holding `v`
(`&staticuint64s[v]` for `v < 256`, else a fresh `mallocgc(8)` object), memory changed only
inside `rt` and the stack window. -/
def ConvT64Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK s stack 1)
    (fun s s' => AllocRet rt stack 1 (fun ptr => [ptr]) s s' fun m ptr =>
      ptr + 8 ≤ 2 ^ 48 ∧ m.accessible ptr 8 false = true ∧ m.readLE ptr 8 = (s.regs 0).toNat)

end Janus.Kernel

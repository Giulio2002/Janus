import Janus.Contracts.Syscall
import Janus.Contracts.AllocAmd64
import Janus.Amd64.FFI

/-!
# The kernel as an environment (amd64)

The amd64 counterpart of `Janus.Kernel` (read that module first): the same kernel state `Kern`,
system calls `Sys` (with the amd64 numbers, `Sys.ofAmd64`), contracts `Safe`/`Effect`, and a
kernel semantics `ReturnsK` over the x86-64 model.

The amd64 specifics:

* **`SYSCALL`** takes the number in `RAX` and the arguments in `RDI RSI RDX R10 R8 R9`, and
  returns the result in `RAX`. The CPU puts the return address in `RCX` and `RFLAGS` in `R11`;
  Linux returns with every other register, the flags, `DF` and the vector registers as they were
  (`afterSyscall`; `R11` is left unspecified).
* **Environment instructions**: `CPUID` (any 32-bit values in `EAX EBX ECX EDX`, zero-extended),
  `XGETBV` with `ECX = 0` (`EDX:EAX = XCR0`, a constant of the system; it needs `OSXSAVE`),
  `RDTSC` (any 64-bit counter in `EDX:EAX`; allowed unless the kernel disabled it for the
  process) and `RDTSCP` (also any `TSC_AUX` in `ECX`).
* **vDSO clocks**: `time.now` (Go 1.26's `runtime/time_linux_amd64.s`, ABIInternal: `sec` in
  `RAX`, `nsec` in `RBX`, the monotonic reading `mono` in `RCX`) and `runtime.nanotime1`
  (ABI0: the result at `[RSP + 8]`).
* **Traps**: `INT3`/`INT 3` (`SIGTRAP`), `UD2` (`SIGILL`), `HLT` (`SIGSEGV`).
-/

namespace Janus.Amd64.Kernel

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Kernel

/-- What a `.syscall` stub stands for (amd64). -/
inductive Site where
  /-- `SYSCALL`. -/
  | syscall
  /-- `CPUID`, `XGETBV`, `RDTSC`, `RDTSCP`. -/
  | env (op : EnvOp)
  /-- `time.now` (ABIInternal): both clocks through the vDSO. -/
  | timeNow
  /-- `runtime.nanotime1` (ABI0): `CLOCK_MONOTONIC` through the vDSO. -/
  | nanotime
deriving Repr, DecidableEq, Inhabited

def timeNowName : String := "time.now"

/-- The site of the `.syscall` stub `name` at `pc`: a vDSO clock function by name, otherwise the
instruction at `pc`. -/
def siteOf (p : Program) (name : String) (pc : Nat) : Option Site :=
  if name = timeNowName then some .timeNow
  else if name = nanotimeName then some .nanotime
  else match p.fetch pc with
    | some bs =>
      match decode bs with
      | some (.syscall, _) => some .syscall
      | some (.envRead op, _) => some (.env op)
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

theorem siteOf_link_withExit {p : Program} (impl : List Segment) (ret : Nat) {name : String}
    {pc : Nat} {site : Site} (h : siteOf p name pc = some site) :
    siteOf ((p.link impl).withExit ret) name pc = some site := siteOf_link impl h

/-- `kernel_site64`: close `siteOf P name pc = some site` (amd64) by evaluation on the closed
program. -/
macro "kernel_site64" : tactic => `(tactic| first
  | exact Janus.Amd64.Kernel.siteOf_link_withExit _ _ (by decide)
  | (rw [Janus.Amd64.Kernel.siteOf_withExit]; decide)
  | decide)

/-- The system call `RAX` names. -/
def sysOf (s : State) : Option Sys := Sys.ofAmd64 (s.regs 0).toNat

/-- The arguments `RDI RSI RDX R10 R8 R9`. -/
def argsOf (s : State) : Nat → Nat
  | 0 => (s.regs 7).toNat
  | 1 => (s.regs 6).toNat
  | 2 => (s.regs 2).toNat
  | 3 => (s.regs 10).toNat
  | 4 => (s.regs 8).toNat
  | 5 => (s.regs 9).toNat
  | _ => 0

/-- `RIP` after the 2-byte `SYSCALL`. -/
def nextRip (s : State) (len : Nat) : W64 := BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)

/-- The state after `SYSCALL` returns `r` with memory `m'`: `RAX = r`, `RCX` = the return
address, `R11 = r11` (the saved `RFLAGS`, left unspecified), everything else unchanged. -/
def afterSyscall (s : State) (r : Nat) (r11 : W64) (m' : Memory) : State :=
  { s with
    regs := fun i => if i = 0 then BitVec.ofNat 64 r else if i = 1 then nextRip s 2
      else if i = 11 then r11 else s.regs i
    rip := nextRip s 2
    mem := m' }

attribute [janus64_exec, janus64_post] nextRip afterSyscall

/-- `s` with `RAX, RBX, RCX, RDX` (registers 0, 3, 1, 2) set where given, `RIP` past `len`. -/
def withRegs (s : State) (len : Nat) (vs : List (Nat × Nat)) : State :=
  { s with
    regs := fun i => (match vs.find? (·.1 == i) with
      | some (_, v) => BitVec.ofNat 64 v
      | none => s.regs i)
    rip := nextRip s len }

attribute [janus64_exec, janus64_post] withRegs

/-- What a stub site needs (amd64). -/
def SiteSafe (E : KEnv) (s : State) (k : Kern) : Site → Prop
  | .syscall => ∃ sc, sysOf s = some sc ∧ sc ≠ .exitGroup ∧ Safe sc (argsOf s) k s.mem
  | .env .cpuid => True
  | .env .xgetbv => k.xgetbvOK = true ∧ (s.regs 1).toNat % 2 ^ 32 = 0
  | .env .rdtsc => k.tscOK = true
  | .env .rdtscp => k.tscOK = true
  | .timeNow => Contracts.CallOK64 s E.stack 0
  | .nanotime => Contracts.CallOK64 s E.stack 1

/-- The successors a stub site allows (amd64). -/
def SiteNext (E : KEnv) (s : State) (k : Kern) (s' : State) (k' : Kern) : Site → Prop
  | .syscall => ∃ sc m' r r11, sysOf s = some sc ∧ Effect sc (argsOf s) k s.mem k' m' r ∧
      s' = afterSyscall s r r11 m'
  | .env .cpuid => ∃ a b c d, a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ c < 2 ^ 32 ∧ d < 2 ^ 32 ∧ k' = k ∧
      s' = withRegs s 2 [(0, a), (3, b), (1, c), (2, d)]
  | .env .xgetbv => k' = k ∧ s' = withRegs s 3 [(0, k.xcr0 % 2 ^ 32), (2, k.xcr0 / 2 ^ 32 % 2 ^ 32)]
  | .env .rdtsc => ∃ v, v < 2 ^ 64 ∧ k' = k.emit (.env "TSC" v) ∧
      s' = withRegs s 2 [(0, v % 2 ^ 32), (2, v / 2 ^ 32)]
  | .env .rdtscp => ∃ v aux, v < 2 ^ 64 ∧ aux < 2 ^ 32 ∧ k' = k.emit (.env "TSC" v) ∧
      s' = withRegs s 3 [(0, v % 2 ^ 32), (2, v / 2 ^ 32), (1, aux)]
  | .timeNow => ∃ sec nsec msec mnsec, nsec < 10 ^ 9 ∧ sec < 2 ^ 63 ∧ mnsec < 10 ^ 9 ∧
      k.mono ≤ msec * 10 ^ 9 + mnsec ∧
      k' = { (k.emit (.clock 0 sec nsec)).emit (.clock 1 msec mnsec) with
              mono := msec * 10 ^ 9 + mnsec } ∧
      ∃ junk f x yh m, s' = Contracts.retState64 s junk
          [BitVec.ofNat 64 sec, BitVec.ofNat 64 nsec, BitVec.ofNat 64 (msec * 10 ^ 9 + mnsec)]
          f x yh m ∧
        MemFrame s.mem m (E.rt ++ [((s.regs 4).toNat - E.stack, (s.regs 4).toNat)])
  | .nanotime => ∃ sec nsec, nsec < 10 ^ 9 ∧ k.mono ≤ sec * 10 ^ 9 + nsec ∧
      k' = { k.emit (.clock 1 sec nsec) with mono := sec * 10 ^ 9 + nsec } ∧
      ∃ (regs : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
        s' = { s with regs := regs, rip := retAddrOf s, flags := f, xmm := x, ymmHi := yh,
                      mem := m } ∧
        regs 4 = s.regs 4 + 8 ∧ regs 5 = s.regs 5 ∧ regs 14 = s.regs 14 ∧
        MemFrame s.mem m (E.rt ++ [((s.regs 4).toNat - E.stack, (s.regs 4).toNat),
          ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]) ∧
        m.readLE ((s.regs 4).toNat + 8) 8 = (sec * 10 ^ 9 + nsec) % 2 ^ 64

/-- A stub site that ends the process: `exit_group(code)`. -/
def SiteExit (s : State) (code : Nat) : Site → Prop
  | .syscall => sysOf s = some .exitGroup ∧ code = (s.regs 7).toNat
  | _ => False

/-- The kernel semantics (amd64): as `Janus.Kernel.ReturnsK`. -/
inductive ReturnsK (p : Program) (E : KEnv) (post : State → Kern → Prop)
    (onExit : Nat → Kern → Prop) : State → Kern → Prop where
  | exit {s : State} {k : Kern} (hx : s.rip.toNat = p.exitAddr) (hp : post s k) :
      ReturnsK p E post onExit s k
  | step {s s' : State} {k : Kern} {w : List Nat} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = none) (hf : p.fetch s.rip.toNat = some w)
      (hst : Amd64.step w s = .ok s') (h : ReturnsK p E post onExit s' k) :
      ReturnsK p E post onExit s k
  | sys {s : State} {k : Kern} {st : Stub} {site : Site} (hx : s.rip.toNat ≠ p.exitAddr)
      (hs : p.stubAt s.rip.toNat = some st) (hk : st.kind = .syscall)
      (hsite : siteOf p st.name s.rip.toNat = some site) (hsafe : SiteSafe E s k site)
      (h : ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') :
      ReturnsK p E post onExit s k
  | halt {s : State} {k : Kern} {st : Stub} {site : Site} {code : Nat}
      (hx : s.rip.toNat ≠ p.exitAddr) (hs : p.stubAt s.rip.toNat = some st)
      (hk : st.kind = .syscall) (hsite : siteOf p st.name s.rip.toNat = some site)
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

theorem of_steps {s s' : State} {k : Kern} {n : Nat} (hs : Program.Steps p s n s')
    (h : ReturnsK p E P X s' k) : ReturnsK p E P X s k := by
  induction hs with
  | refl => exact h
  | step hx hst hf he _ ih => exact .step hx hst hf he (ih h)

end ReturnsK

/-- The outcome predicate of `ReturnsK` (amd64). -/
def IsReturnK (p : Program) (E : KEnv) (post : State → Kern → Prop) (onExit : Nat → Kern → Prop)
    (k : Kern) : Outcome → Prop
  | .returned s => post s k
  | .stub f .syscall s => ∃ site, siteOf p f s.rip.toNat = some site ∧
      ((SiteSafe E s k site ∧ ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') ∨
        ∃ code, SiteExit s code site ∧ onExit code k)
  | .stub _ _ _ => False

@[simp, janus64_post] theorem isReturnK_returned (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (s : State) :
    IsReturnK p E post onExit k (.returned s) = post s k := rfl
@[simp, janus64_post] theorem isReturnK_syscall (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) :
    IsReturnK p E post onExit k (.stub f .syscall s) =
      ∃ site, siteOf p f s.rip.toNat = some site ∧
        ((SiteSafe E s k site ∧ ∀ s' k', SiteNext E s k s' k' site → ReturnsK p E post onExit s' k') ∨
          ∃ code, SiteExit s code site ∧ onExit code k) := rfl
@[simp, janus64_post] theorem isReturnK_panic (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .panic s) = False := rfl
@[simp, janus64_post] theorem isReturnK_morestack (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .morestack s) = False := rfl
@[simp, janus64_post] theorem isReturnK_external (p : Program) (E : KEnv)
    (post : State → Kern → Prop) (onExit : Nat → Kern → Prop) (k : Kern) (f : String)
    (s : State) : IsReturnK p E post onExit k (.stub f .external s) = False := rfl
@[simp, janus64_post] theorem isReturnK_trap (p : Program) (E : KEnv)
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
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [ite_eq_left hx] at hr; cases hr; exact .exit hx hq
    · rw [ite_eq_right hx] at hr
      cases hst : p.stubAt s.rip.toNat with
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
        cases hf : p.fetch s.rip.toNat with
        | none => simp only [hst, hf] at hr; cases hr
        | some w =>
          cases he : Amd64.step w s with
          | error e => simp only [hst, hf, he] at hr; cases hr
          | ok s₁ => simp only [hst, hf, he] at hr; exact .step hx hst hf he (ih hr)

/-- The Go function contract under the kernel semantics (amd64): as `Janus.Kernel.EnsuresK`,
with the full `GoABI.ABIReturn` (`RSP + 8`, `RBP`, `R14`, `X15`). -/
def EnsuresK (p : Program) (E : KEnv) (entry : Nat) (args : List W64)
    (pre : State → Kern → Prop) (post : State → Kern → State → Kern → Prop)
    (onExit : State → Kern → Nat → Kern → Prop := fun _ _ _ _ => False) : Prop :=
  ∀ ret, RetAddr p ret → ∀ s k, CallSetup (p.withExit ret) entry args s → pre s k →
    ReturnsK (p.withExit ret) E (fun s' k' => ABIReturn s s' ∧ post s k s' k') (onExit s k) s k

/-! ## Traps -/

/-- The bytes at `pc` are a trap instruction (`INT3`, `INT 3`, `UD2`, `HLT`). -/
def trapAt (p : Program) (pc : Nat) : Bool :=
  match p.fetch pc with
  | some bs =>
    match decode bs with
    | some (.trap _, _) => true
    | _ => false
  | none => false

def IsTrap (p : Program) : Outcome → Prop
  | .stub _ .trap s => trapAt p s.rip.toNat = true
  | _ => False

/-- **The run from `s` ends in a trap** (amd64). -/
def Traps (p : Program) (s : State) : Prop := Reaches p s (IsTrap p)

@[simp, janus64_post] theorem isTrap_trap (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .trap s) = (trapAt p s.rip.toNat = true) := rfl
@[simp, janus64_post] theorem isTrap_returned (p : Program) (s : State) :
    IsTrap p (.returned s) = False := rfl
@[simp, janus64_post] theorem isTrap_panic (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .panic s) = False := rfl
@[simp, janus64_post] theorem isTrap_morestack (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .morestack s) = False := rfl
@[simp, janus64_post] theorem isTrap_external (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .external s) = False := rfl
@[simp, janus64_post] theorem isTrap_syscall (p : Program) (f : String) (s : State) :
    IsTrap p (.stub f .syscall s) = False := rfl

@[simp] theorem trapAt_withExit (p : Program) (ret pc : Nat) :
    trapAt (p.withExit ret) pc = trapAt p pc := rfl

theorem trapAt_link {p : Program} (impl : List Segment) {pc : Nat} (h : trapAt p pc = true) :
    trapAt (p.link impl) pc = true := by
  unfold trapAt at h ⊢
  cases hf : p.fetch pc with
  | none => rw [hf] at h; cases h
  | some w => rw [hf] at h; rw [Program.fetch_link impl hf]; exact h

/-- A trap stub stands for a fault: the instruction there, executed, faults with `Fault.trap`. -/
theorem trapAt_faults {p : Program} {pc : Nat} (h : trapAt p pc = true) (s : State)
    (hpc : s.rip.toNat = pc) :
    ∃ bs sig, p.fetch pc = some bs ∧ Amd64.step bs s = .error (.trap pc sig) := by
  unfold trapAt at h
  split at h
  · rename_i bs hf
    split at h
    · rename_i sig len hd
      exact ⟨bs, sig, hf, by rw [Amd64.step_of_decode hd]; simp [exec, hpc]⟩
    · cases h
  · cases h

/-! ## Runtime contracts around system calls (amd64) -/

open Janus.Contracts in
/-- **`runtime.entersyscall()`, `runtime.exitsyscall()`** (amd64): as `Janus.Kernel.SchedContract`. -/
def SchedContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK64 s stack 0)
    (fun s s' => AllocRet64 rt stack 0 (fun _ => []) s s' fun _ _ => True)

open Janus.Contracts in
/-- **`runtime.convT64(v)`** (amd64; `RAX = v`): as `Janus.Kernel.ConvT64Contract`. -/
def ConvT64Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK64 s stack 1)
    (fun s s' => AllocRet64 rt stack 1 (fun ptr => [ptr]) s s' fun m ptr =>
      ptr + 8 ≤ 2 ^ 48 ∧ m.accessible ptr 8 false = true ∧ m.readLE ptr 8 = (s.regs 0).toNat)

end Janus.Amd64.Kernel

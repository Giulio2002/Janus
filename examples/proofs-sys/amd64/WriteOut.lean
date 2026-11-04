import Janus
import Extracted

/-!
# `WriteOut(p []byte) (int, error)`: one `write(2)` of `p` to standard output (amd64)

The amd64 build of `examples/sys.WriteOut` (see the arm64 proof): `WriteOut` → `syscall.write`
→ `syscall.Syscall` → `syscall.RawSyscall6` → `internal/runtime/syscall/linux.Syscall6`
(ABIInternal assembly) down to its `SYSCALL`, all executed by the model; the scheduler hooks and
`runtime.convT64` are the runtime contracts `Amd64.Kernel.SchedContract`/`ConvT64Contract`.

**Guarantee (`correctness`).** Every run returns with the Go ABI restored (`RSP + 8`, `RBP`,
`R14`, `X15 = 0`) and either the trace gains exactly `write(1, p[:c])` with `n = c ≤ len(p)` and
`err = nil` (`RBX = RCX = 0`), or the trace is unchanged and `n = -1`. **`full_write`**: if
`n = len(p)`, the output of fd 1 grew by exactly `p`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel

namespace Proof

/-- `syscall.errEAGAIN`, `errEINVAL`, `errENOENT` (`.data`, 16 bytes each, contiguous), read off the
`MOVQ syscall.errEAGAIN(SB), DX` at `syscall.write+0x68`. -/
def errVars : Nat := ripTarget Extracted.program (segAddr Extracted.program "syscall.write" + 0x68)

set_option hygiene false in
/-- After the `write` system call: the two kernel outcomes, each run on to the return. -/
macro "after_write" : tactic => `(tactic| (
  rintro s' k' ⟨sc, m', r, r11, hsc, heff, rfl⟩
  simp [sysOf, Sys.ofAmd64, setRegF] at hsc
  subst hsc
  simp only [Effect, Amd64.Kernel.argsOf, setRegF] at heff
  obtain ⟨rfl, ⟨c, hc, rfl, rfl⟩ | ⟨⟨he1, he2⟩, rfl⟩⟩ := heff
  · simp [setRegF] at hc
    apply Amd64.Kernel.ReturnsK.of_reaches
    janus64_run calls [hent, hexit, hconv]
    all_goals (left; refine ⟨r, by omega, ?_, rfl⟩; congr 2)
    all_goals first
      | (subst hc; rfl)
      | ((repeat (first
          | refine (readBytes_writeLE (by omega)).trans ?_
          | (refine (MemFrame.readBytes_eq (by assumption) ?_).trans ?_
             · simp only [outside_append, outside_cons, outside_nil, and_true]
               exact ⟨Outside.of_sub hbo (Nat.le_refl _) (by omega), by omega, by omega⟩)))
         rfl)
  · apply Amd64.Kernel.ReturnsK.of_reaches
    janus64_run calls [hent, hexit, hconv]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hent : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024)
    (hexit : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024)
    (hconv : Amd64.Kernel.ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024)
    (ptr len cap : BitVec 64) :
    Amd64.Kernel.EnsuresK (Extracted.program.link impl) E Extracted.entry [ptr, len, cap]
      (fun s _ => StackGuardOK s 48 ∧ StackWritable s 1232 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Outside ((s.regs 4).toNat - 1232) 1248 rt ∧
        Buf s.mem ptr.toNat len.toNat false ∧ len.toNat ≤ 2 ^ 48 ∧ Outside ptr.toNat len.toNat rt ∧
        (ptr.toNat + len.toNat ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16) ∧
        s.mem.accessible errVars 48 false = true ∧
        (errVars + 48 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ errVars))
      (fun s k s' k' =>
        (∃ c, c ≤ len.toNat ∧ k' = k.emit (.write 1 (readBytes s.mem ptr.toNat c)) ∧
          s'.regs 0 = BitVec.ofNat 64 c ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
        (k' = k ∧ s'.regs 0 = BitVec.ofNat 64 (2 ^ 64 - 1))) := by
  intro ret hret s k hs ⟨hg, ⟨hb, ha, hw⟩, hal, hout, hbuf, hlen, hbo, hbd, hgd, herr, hed⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  janus_eval_nat hE : errVars
  simp only [regSP, regG, stackguard0Offset, stackguard0, hE] at hgl hgb hnw2 hgr hb ha hw hout hal herr hed ⊢
  clear hE
  apply Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  janus64_run calls [hent, hexit, hconv]
  all_goals refine ⟨.syscall, by kernel_site64, Or.inl ⟨⟨.write, by simp [sysOf, Sys.ofAmd64, setRegF], by decide, ?_⟩, ?_⟩⟩
  · simp [Safe, Buf, Amd64.Kernel.argsOf, setRegF]
  · after_write
  · simp [Safe, Buf, Amd64.Kernel.argsOf, setRegF]
    rcases hbuf with h0 | hacc
    · exact Or.inl h0
    · right; rw [(‹MemFrame _ _ _›).accessible]; simpa using hacc
  · after_write

/-- When the kernel accepts every byte (`n = len(p)`), standard output gains exactly `p`. -/
theorem full_write (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hent : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024)
    (hexit : Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024)
    (hconv : Amd64.Kernel.ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024)
    (ptr len cap : BitVec 64) :
    Amd64.Kernel.EnsuresK (Extracted.program.link impl) E Extracted.entry [ptr, len, cap]
      (fun s _ => StackGuardOK s 48 ∧ StackWritable s 1232 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Outside ((s.regs 4).toNat - 1232) 1248 rt ∧
        Buf s.mem ptr.toNat len.toNat false ∧ len.toNat ≤ 2 ^ 48 ∧ Outside ptr.toNat len.toNat rt ∧
        (ptr.toNat + len.toNat ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ ptr.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16) ∧
        s.mem.accessible errVars 48 false = true ∧
        (errVars + 48 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ errVars))
      (fun s k s' k' => s'.regs 0 = len →
        k'.output 1 = k.output 1 ++ readBytes s.mem ptr.toNat len.toNat) := by
  intro ret hret s k hs hpre
  have hl := hpre.2.2.2.2.2.1
  refine (correctness impl rt E hent hexit hconv ptr len cap ret hret s k hs hpre).mono ?_
    (fun _ _ h => h)
  rintro s' k' ⟨habi, ⟨c, hc, rfl, h0, -, -⟩ | ⟨-, h0⟩⟩
  · refine ⟨habi, fun hn => ?_⟩
    have : c = len.toNat := by
      have := congrArg BitVec.toNat (h0.symm.trans hn)
      simp [BitVec.toNat_ofNat] at this; omega
    subst this; simp
  · refine ⟨habi, fun hn => ?_⟩
    have := congrArg BitVec.toNat (h0.symm.trans hn)
    simp [BitVec.toNat_ofNat] at this; omega

/-! ## Non-vacuity witness

The stubs of `Janus/Contracts/LiveStubSysAmd64.lean` sit at the contract addresses of
`runtime.entersyscall`, `runtime.exitsyscall` and `runtime.convT64` in this program;
`janus64_sys_sched` and `janus64_sys_convt64` prove the three contracts for them by running the stub
code. Below, a concrete call state of `WriteOut(p, 0, 0)` (an empty buffer) satisfies the whole
precondition, and the call returns what the theorem describes. -/

namespace Witness

open Janus.Contracts.LiveStubSysAmd64

local macro "cEnter" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.entersyscall"))
local macro "cExit" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.exitsyscall"))
local macro "cConv" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.convT64"))

def implAt : List Amd64.Segment := [schedSeg cEnter, schedSeg cExit, convT64Seg cConv]
def linked : Amd64.Program := Extracted.program.link implAt

theorem hent0 : Amd64.Kernel.SchedContract linked cEnter [] 1024 := by janus64_sys_sched
theorem hexit0 : Amd64.Kernel.SchedContract linked cExit [] 1024 := by janus64_sys_sched
theorem hconv0 : Amd64.Kernel.ConvT64Contract linked cConv [] 1024 := by janus64_sys_convt64 1024

theorem hent : Amd64.Kernel.SchedContract (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.entersyscall") [] 1024 := by
  have h : Extracted.program.contractAddr "runtime.entersyscall" = cEnter := by decide
  rw [h]; exact hent0
theorem hexit : Amd64.Kernel.SchedContract (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.exitsyscall") [] 1024 := by
  have h : Extracted.program.contractAddr "runtime.exitsyscall" = cExit := by decide
  rw [h]; exact hexit0
theorem hconv : Amd64.Kernel.ConvT64Contract (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.convT64") [] 1024 := by
  have h : Extracted.program.contractAddr "runtime.convT64" = cConv := by decide
  rw [h]; exact hconv0

def errA : Nat := janus_eval% errVars
def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def p0 : Nat := 0x400000

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 p0 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 1232, 1232 + 16, true⟩, ⟨g0, 0x100, false⟩, ⟨errA, 48, false⟩]⟩ }

def k0 : Kern := {}
def E0 : KEnv := ⟨[], 1024⟩

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 p0, 0, 0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 48 ∧ StackWritable s0 1232 16 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Outside ((s0.regs 4).toNat - 1232) 1248 [] ∧
    Buf s0.mem (BitVec.ofNat 64 p0).toNat (0 : BitVec 64).toNat false ∧ (0 : BitVec 64).toNat ≤ 2 ^ 48 ∧
    Outside (BitVec.ofNat 64 p0).toNat (0 : BitVec 64).toNat [] ∧
    ((BitVec.ofNat 64 p0).toNat + (0 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 1232 ∨
      (s0.regs 4).toNat + 16 ≤ (BitVec.ofNat 64 p0).toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 1232 ∨ (s0.regs 4).toNat + 16 ≤ (s0.regs 14).toNat + 16) ∧
    s0.mem.accessible errVars 48 false = true ∧
    (errVars + 48 ≤ (s0.regs 4).toNat - 1232 ∨ (s0.regs 4).toNat + 16 ≤ errVars) := by
  have h : errVars = errA := by decide
  rw [h]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, by simp only [outside_nil], Or.inl rfl, by decide,
    by simp only [outside_nil], Or.inr (by decide), by decide, by decide, by decide⟩

/-- The hypotheses are satisfiable: three runtime functions meeting their contracts and a call state of
`WriteOut(p, 0, 0)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (E : KEnv) (ret : Nat)
    (s : Amd64.State) (k : Kern),
    Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024 ∧
    Amd64.Kernel.SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024 ∧
    Amd64.Kernel.ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 p0, 0, 0] s ∧
    (StackGuardOK s 48 ∧ StackWritable s 1232 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
      Outside ((s.regs 4).toNat - 1232) 1248 rt ∧
      Buf s.mem (BitVec.ofNat 64 p0).toNat (0 : BitVec 64).toNat false ∧ (0 : BitVec 64).toNat ≤ 2 ^ 48 ∧
      Outside (BitVec.ofNat 64 p0).toNat (0 : BitVec 64).toNat rt ∧
      ((BitVec.ofNat 64 p0).toNat + (0 : BitVec 64).toNat ≤ (s.regs 4).toNat - 1232 ∨
        (s.regs 4).toNat + 16 ≤ (BitVec.ofNat 64 p0).toNat) ∧
      ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16) ∧
      s.mem.accessible errVars 48 false = true ∧
      (errVars + 48 ≤ (s.regs 4).toNat - 1232 ∨ (s.regs 4).toNat + 16 ≤ errVars)) :=
  ⟨implAt, [], E0, ret, s0, k0, hent, hexit, hconv, hret, setup, pre⟩

/-- The theorem fires: `WriteOut(p, 0, 0)` returns with a successful empty write or with `-1`. -/
theorem returns : Amd64.Kernel.ReturnsK ((Extracted.program.link implAt).withExit ret) E0
    (fun s' k' => ABIReturn s0 s' ∧
      ((∃ c, c ≤ (0 : BitVec 64).toNat ∧
          k' = k0.emit (.write 1 (readBytes s0.mem (BitVec.ofNat 64 p0).toNat c)) ∧
          s'.regs 0 = BitVec.ofNat 64 c ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
        (k' = k0 ∧ s'.regs 0 = BitVec.ofNat 64 (2 ^ 64 - 1))))
    (fun _ _ => False) s0 k0 :=
  correctness implAt [] E0 hent hexit hconv (BitVec.ofNat 64 p0) 0 0 ret hret s0 k0 setup pre

end Witness

end Proof

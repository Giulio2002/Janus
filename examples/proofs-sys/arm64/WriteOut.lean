import Extracted

/-!
# `WriteOut(p []byte) (int, error)`: one `write(2)` of `p` to standard output (arm64)

```go
func WriteOut(p []byte) (int, error) { return syscall.Write(1, p) }
```

The whole path is executed by the model from the binary: `WriteOut` → `syscall.write` →
`syscall.Syscall` → `syscall.RawSyscall6` → `internal/runtime/syscall/linux.Syscall6` (assembly,
ABI0), down to its `SVC #0`, a `.syscall` stub, and back through the `-errno` decoding and
`syscall.errnoErr`. Only three runtime functions are contracts (`janus extract --contract`): the
scheduler hooks `runtime.entersyscall`/`runtime.exitsyscall` (`Kernel.SchedContract`: they
preserve the Go ABI registers and change only runtime-owned memory `rt` and their stack window)
and `runtime.convT64` (`Kernel.ConvT64Contract`, the boxing of an `Errno` on the error path). The
kernel is the environment of `Kernel.EnsuresK`: the `write` contract (`Kernel.Effect .write`) lets
it write any prefix of the buffer (a short write) or fail with any `-errno`.

**Guarantee (`correctness`).** For every kernel state `k`, every implementation of the three
contracts, every slice `(ptr, len, cap)` whose `len` bytes are readable, outside `rt` and away from
the stack, and every Go call state whose stack checks fall through (`GuardOK s 48`) with
`[SP-1232, SP+16)` writable and outside `rt`, `g.stackguard0` and the three `syscall.errE*`
variables away from that window, every run returns to the caller with `SP`, `g` and `FP` restored
and either

* the kernel wrote the first `c ≤ len` bytes of `p`: the trace gains exactly
  `write(1, p[:c])` (the bytes in memory at the call), `n = c` and `err = nil`; or
* the call failed: the trace is unchanged and `n = -1`.

**`full_write`.** When the call returns `n = len(p)`, the output of fd 1 grew by exactly the bytes
of `p`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel

namespace Proof

/-- `syscall.errEAGAIN`, `errEINVAL`, `errENOENT` (`.data`, 16 bytes each, contiguous). -/
def errVars : Nat :=
  adrpLdTarget (segAddr Extracted.program "syscall.write" + 4 * 27)
    (segWord Extracted.program "syscall.write" 27) (segWord Extracted.program "syscall.write" 28) 0

set_option hygiene false in
/-- After the `write` system call: the two kernel outcomes (some bytes written, or `-errno`),
each run on to the return. -/
macro "after_write" : tactic => `(tactic| (
  rintro s' k' ⟨sc, m', r, hsc, heff, rfl⟩
  simp [svcSys, Sys.ofArm64, setReg] at hsc
  subst hsc
  simp only [Effect, argsOf, setReg_apply] at heff
  obtain ⟨rfl, ⟨c, hc, rfl, rfl⟩ | ⟨⟨he1, he2⟩, rfl⟩⟩ := heff
  · simp [setReg, callRegs] at hc
    apply ReturnsK.of_reaches
    janus_run [addWithCarry_c] calls [hent, hexit, hconv]
    all_goals (left; refine ⟨r, by omega, ?_, rfl⟩; congr 2)
    all_goals first
      | (subst hc; rfl)
      | (repeat (first
          | refine (readBytes_writeLE (by omega)).trans ?_
          | (refine (MemFrame.readBytes_eq (by assumption) ?_).trans ?_
             · simp only [outside_append, outside_cons, outside_nil, and_true]
               exact ⟨Outside.of_sub hbo (Nat.le_refl _) (by omega), by omega, by omega⟩))
         rfl)
  · apply ReturnsK.of_reaches
    janus_run [addWithCarry_c] calls [hent, hexit, hconv]
))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hent : SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024)
    (hexit : SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024)
    (hconv : ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024)
    (ptr len cap : BitVec 64) :
    EnsuresK (Extracted.program.link impl) E Extracted.entry [ptr, len, cap]
      (fun s _ => GuardOK s 48 ∧ StackOK s 1232 16 ∧ Outside (s.sp.toNat - 1232) 1248 rt ∧
        Buf s.mem ptr.toNat len.toNat false ∧ len.toNat ≤ 2 ^ 48 ∧ Outside ptr.toNat len.toNat rt ∧
        (ptr.toNat + len.toNat ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ ptr.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        s.mem.accessible errVars 48 false = true ∧
        (errVars + 48 ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ errVars))
      (fun s k s' k' =>
        (∃ c, c ≤ len.toNat ∧ k' = k.emit (.write 1 (readBytes s.mem ptr.toNat c)) ∧
          s'.regs 0 = BitVec.ofNat 64 c ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
        (k' = k ∧ s'.regs 0 = BitVec.ofNat 64 (2 ^ 64 - 1))) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hout, hbuf, hlen, hbo, hbd, hgd, herr, hed⟩
  janus_eval_nat hE : errVars
  simp only [hE] at herr hed
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run calls [hent, hexit, hconv]
  all_goals refine ⟨.svc, by kernel_site, Or.inl ⟨⟨.write, by simp [svcSys, Sys.ofArm64, setReg], by decide, ?_⟩, ?_⟩⟩
  · simp [Safe, Buf, argsOf, setReg]
  · after_write
  · simp [Safe, Buf, argsOf, setReg]
    rcases hbuf with h0 | hacc
    · exact Or.inl h0
    · right; rw [(‹MemFrame _ _ _›).accessible]; simpa using hacc
  · after_write

/-- When the kernel accepts every byte (`n = len(p)`), standard output gains exactly `p`. -/
theorem full_write (impl : List Segment) (rt : List (Nat × Nat)) (E : KEnv)
    (hent : SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.entersyscall") rt 1024)
    (hexit : SchedContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.exitsyscall") rt 1024)
    (hconv : ConvT64Contract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.convT64") rt 1024)
    (ptr len cap : BitVec 64) :
    EnsuresK (Extracted.program.link impl) E Extracted.entry [ptr, len, cap]
      (fun s _ => GuardOK s 48 ∧ StackOK s 1232 16 ∧ Outside (s.sp.toNat - 1232) 1248 rt ∧
        Buf s.mem ptr.toNat len.toNat false ∧ len.toNat ≤ 2 ^ 48 ∧ Outside ptr.toNat len.toNat rt ∧
        (ptr.toNat + len.toNat ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ ptr.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        s.mem.accessible errVars 48 false = true ∧
        (errVars + 48 ≤ s.sp.toNat - 1232 ∨ s.sp.toNat + 16 ≤ errVars))
      (fun s k s' k' => s'.regs 0 = len →
        k'.output 1 = k.output 1 ++ readBytes s.mem ptr.toNat len.toNat) := by
  intro ret hret s k hs hpre
  have hl := hpre.2.2.2.2.1
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

end Proof

import Janus.Arm64.Instr
import Janus.Arm64.Bits

/-!
# Kernel, trap and environment encodings (WP-C)

The A64 encodings whose effect is not determined by the user-mode state, decoded here so that
the main decoder (`Janus.Arm64.Decode`) only carries two one-line hooks:

* **System call.** `SVC #0` (`0xD4000001`). Linux ignores the immediate, but Go only emits `#0`,
  so every other immediate is rejected. It executes as `Fault.kernel`: the kernel semantics
  (`Janus.Kernel.ReturnsK`) gives it a meaning, at the `.syscall` stub the extractor puts on it.
* **Traps.** `BRK #imm16` (`0xD4200000 | imm16 << 5`, Linux `SIGTRAP`) and the permanently
  undefined `UDF #imm16` (`0x0000xxxx`, `SIGILL`). They execute as `Fault.trap`: an explicit
  fault outcome. `HLT` (halting debug, `UNDEFINED` at EL0 on Linux) and the other exception
  generating instructions (`HVC`, `SMC`, `DCPS*`) are rejected.
* **Environment registers.** `MRS Xt, CNTVCT_EL0` (`0xD53BE040`), `MRS Xt, CNTFRQ_EL0`
  (`0xD53BE000`), `MRS Xt, MIDR_EL1` (`0xD5380000`, emulated by Linux for EL0 when the CPU
  feature `CPUID` is reported), `MRS Xt, DIT` (`0xD53B42A0`), `MSR DIT, Xt` (`0xD51B42A0`) and
  `MSR DIT, #imm` (`0xD503405F | CRm << 8`, `CRm ∈ {0, 1}`). They execute as `Fault.kernel`; the
  environment contract of `Janus.Kernel` gives their result.
* **Flag images** (the arm64 counterpart of `PUSHFQ`/`POPFQ`, used by `runtime.asyncPreempt`):
  `MRS`/`MSR` of `NZCV` (`0xD53B4200`/`0xD51B4200`) and `FPSR` (`0xD53B4420`/`0xD51B4420`), which
  read and write `State.flags` and `State.fpsr` deterministically.

Every other system register access stays rejected.
-/

namespace Janus.Arm64

/-- The kernel, trap and environment encodings of the "branches, exception generating and
system instructions" group (`op0 = 101x`). -/
def decodeSys (w : Nat) : Option Instr :=
  if w = 0xD4000001 then some (.svc 0)
  else if w &&& 0xFFE0001F = 0xD4200000 then some (.brk (bits w 20 5))
  else if w &&& 0xFFFFFFE0 = 0xD53BE040 then some (.mrsEnv .cntvct (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD53BE000 then some (.mrsEnv .cntfrq (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD5380000 then some (.mrsEnv .midr (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD53B42A0 then some (.mrsEnv .dit (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD51B42A0 then some (.msrDitReg (bits w 4 0))
  else if w = 0xD503405F then some (.msrDitImm 0)
  else if w = 0xD503415F then some (.msrDitImm 1)
  -- the flag images `runtime.asyncPreempt` saves and restores (deterministic, not environment)
  else if w &&& 0xFFFFFFE0 = 0xD53B4200 then some (.mrsNzcv (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD51B4200 then some (.msrNzcv (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD53B4420 then some (.mrsFpsr (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD51B4420 then some (.msrFpsr (bits w 4 0))
  else none

/-- The reserved group (`op0 = 0000`): `UDF #imm16` is `0x0000xxxx`; the rest of the group is
unallocated (or SME, `op0 = 0000` with bit 31 set) and rejected. -/
def decodeReserved (w : Nat) : Option Instr :=
  if w < 0x10000 then some (.udf w) else none

end Janus.Arm64

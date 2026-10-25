import Janus.Amd64.Instr

/-!
# Kernel, trap, environment and flag-image encodings (WP-C)

The x86-64 encodings whose effect is not determined by the user-mode state (or that read or
write the `RFLAGS` image), decoded here so that the main decoder (`Janus.Amd64.decode`) only
carries a one-line hook. Each is accepted **only in its exact, unprefixed form**: any prefix
(`66`, `F2`, `F3`, `REX`, segment overrides, `LOCK`) is rejected, because hardware either
ignores it (which the model would then have to mirror byte for byte) or raises `#UD`.

| bytes | instruction | model |
|---|---|---|
| `0F 05` | `SYSCALL` | `Fault.kernel` (the kernel semantics gives its effect) |
| `0F A2` | `CPUID` | `Fault.kernel` (environment value) |
| `0F 01 D0` | `XGETBV` | `Fault.kernel` (environment value) |
| `0F 31` | `RDTSC` | `Fault.kernel` (environment value) |
| `0F 01 F9` | `RDTSCP` | `Fault.kernel` (environment value) |
| `CC`, `CD 03` | `INT3`, `INT 3` | `Fault.trap pc 5` (`SIGTRAP`) |
| `0F 0B` | `UD2` | `Fault.trap pc 4` (`SIGILL`) |
| `F4` | `HLT` | `Fault.trap pc 11` (`#GP` at CPL 3, `SIGSEGV`) |
| `9C` | `PUSHFQ` | the `RFLAGS` image (`Exec`) |
| `9D` | `POPFQ` | status flags and `DF` from memory (`Exec`) |

`INT n` for any other `n` (in particular `INT 0x80`, the 32-bit system call gate),
`SYSENTER`, `INTO`, `INT1` and the 16-bit `PUSHF`/`POPF` (`66 9C`/`66 9D`) are rejected.
-/

namespace Janus.Amd64

/-- The kernel, trap, environment and flag-image instructions, by their exact bytes, with
their lengths. -/
def decodeSys : List Nat → Option (Instr × Nat)
  | 0x0F :: 0x05 :: _ => some (.syscall, 2)
  | 0x0F :: 0xA2 :: _ => some (.envRead .cpuid, 2)
  | 0x0F :: 0x01 :: 0xD0 :: _ => some (.envRead .xgetbv, 3)
  | 0x0F :: 0x31 :: _ => some (.envRead .rdtsc, 2)
  | 0x0F :: 0x01 :: 0xF9 :: _ => some (.envRead .rdtscp, 3)
  | 0xCC :: _ => some (.trap 5, 1)
  | 0xCD :: 0x03 :: _ => some (.trap 5, 2)
  | 0x0F :: 0x0B :: _ => some (.trap 4, 2)
  | 0xF4 :: _ => some (.trap 11, 1)
  | 0x9C :: _ => some (.pushfq, 1)
  | 0x9D :: _ => some (.popfq, 1)
  | _ => none

end Janus.Amd64

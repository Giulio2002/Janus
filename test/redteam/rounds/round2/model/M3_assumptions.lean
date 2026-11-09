import Janus
/-! M3: modelling assumptions that qemu `-cpu max` and Sail cannot see (they implement every
feature and one fixed DCZID_EL0). Each `#guard` shows what the model does; the comment says
what real hardware does. None of these is a wrong value for a valid instruction.
Run: lake env lean audit/round2/model/M3_assumptions.lean
Companion: feat.S (qemu `-cpu cortex-a53` vs `-cpu max`, see README.txt). -/
open Janus.Arm64

namespace Audit3
def base : Nat := 0x10000
def mkState (regs : List (Nat × Nat)) (dczid : BitVec 5 := 4) (ro : Bool := false) : State :=
  { regs := fun i => BitVec.ofNat 64 ((regs.lookup i).getD 0)
    sp := BitVec.ofNat 64 0x20000, pc := BitVec.ofNat 64 0x400000
    flags := ⟨false, false, false, false⟩
    mem := ⟨fun _ => 0xAA, [⟨base, 0x40000, !ro⟩]⟩
    dczid := dczid }
def byteAt (r : Except Fault State) (a : Nat) : Option Nat := match r with
  | .ok s => some (s.mem.bytes a).toNat | .error _ => none
def fault (r : Except Fault State) : Option Fault := match r with
  | .ok _ => none | .error e => some e

/-! ### A1. DC ZVA block size for reserved DCZID_EL0.BS values (10..15)
ARM ARM D23.2 DCZID_EL0.BS: "Log2 of the block size in words. The maximum size supported is
2KB (value == 9)." The model computes `4 * 2 ^ (BS % 16)` for every 4-bit BS, so BS = 15 zeroes
a 128 KiB block. No conforming CPU reports BS > 9, so these states are unreachable: theorems
that quantify over every `dczid` (ClearWords) merely prove extra, vacuous cases. BS is a 4-bit
field (`dczid % 16`), so there is no "BS = 31" (dczid = 31 is DZP = 1, BS = 15: trapped), and the
largest block, 2^17 bytes, is far below the 2^48 address bound. Severity: none (informational). -/
-- DC ZVA, x0 (0xd50b7420), BS = 9: 2 KiB block containing x0 = 0x20805 → [0x20800, 0x21000)
#guard byteAt (step 0xd50b7420 (mkState [(0, 0x20805)] 9)) 0x20fff = some 0
#guard byteAt (step 0xd50b7420 (mkState [(0, 0x20805)] 9)) 0x21000 = some 0xAA
-- BS = 15 (reserved): a 128 KiB block [0x20000, 0x40000) is zeroed.
#guard byteAt (step 0xd50b7420 (mkState [(0, 0x20805)] 15)) 0x3ffff = some 0
#guard byteAt (step 0xd50b7420 (mkState [(0, 0x20805)] 15)) 0x1ffff = some 0xAA
-- dczid = 31 (DZP = 1): trapped (SIGILL on Linux)
#guard fault (step 0xd50b7420 (mkState [(0, 0x20805)] 31)) = some (.trapped 0x400000)

/-! ### A2. DCZID_EL0 is one constant per run
`State.dczid` never changes. As far as I know Linux does not trap EL0 reads of DCZID_EL0 and
only warns ("SANITY CHECK: Unexpected variation in SYS_DCZID_EL0", FTR_STRICT) if CPUs differ, so on a
system whose cores report different BS a thread migrated between the `MRS` (or Go's global
`block_size` cache, filled on whichever core ran memclr first) and a `DC ZVA` zeroes a block of
a different size than the model says. The SOUNDNESS text should state the assumption
"DCZID_EL0 is the same on every CPU the process may run on". Severity: low (doc). -/
#guard (match step 0xd53b00e0 (mkState [] 4) with
        | .ok s => s.dczid == 4 && s.regs 0 == 4 | .error _ => false)   -- MRS x0, DCZID_EL0

/-! ### A3. Optional features accepted unconditionally (FEAT_LSE, FEAT_LRCPC, FEAT_AES)
The decoder has no feature input: these decode on every state. On a Cortex-A53/A72 (Armv8.0,
e.g. Raspberry Pi 3/4) LDADDAL and LDAPR are UNDEFINED (qemu -cpu cortex-a53: SIGILL; see
feat.S). AESE is optional on every core (BCM2711 has no Crypto extension). Shipped theorems:
only AtomicAdd (LDADDAL) and AtomicMax (CASAL) execute one, both behind `TBZ`/`CBZ` on
`runtime.arm64HasATOMICS` with the precondition "bit 0 set" (M0_feature_scan.lean). That flag
comes from HWCAP_ATOMICS (system-wide sanitised on mainline Linux; Go ignores it on android
because "the Samsung S9+ kernel reports support for atomics, but not all cores actually support
them", internal/cpu/cpu_arm64_hwcap.go, Go issue 28431). FP/AdvSIMD is also formally optional (ID_AA64PFR0_EL1.AdvSIMD = 0xF) and is used
unguarded by memequal/IndexByte (A64Equal64, A64IndexByte); SOUNDNESS lists only LSE/LRCPC/AES. -/
#guard (decode 0xf8e10002).isSome   -- LDADDAL x1, x2, [x0]
#guard (decode 0xf8bfc002).isSome   -- LDAPR x2, [x0]
#guard (decode 0x4e284820).isSome   -- AESE v0.16b, v1.16b

/-! ### A4. Conservative choices (model faults where some hardware succeeds) -/
-- LDAR x2, [x3] at 4 mod 8 (0xc8dffc62): model `unaligned`; qemu -cpu max (FEAT_LSE2) returns
-- normally, cortex-a53 SIGBUS (feat.S 'u'). Conservative.
#guard fault (step 0xc8dffc62 (mkState [(3, 0x20004)])) = some (.unaligned 0x20004 8)
-- CAS x1, x3, [x0] whose comparison fails on read-only memory: model `readOnly`. The ASL
-- performs the CAS access as a read-write access (write permission checked whatever the
-- comparison does), so the model matches it; and a fault is the conservative outcome anyway.
#guard fault (step 0xc8a17c03 (mkState [(0, 0x20000), (1, 1)] 4 true)) = some (.readOnly 0x20000 8)
end Audit3

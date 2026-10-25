import Janus.Amd64

/-!
# amd64 decoder and executor tests

Byte strings are taken from `go build` (Go 1.26, `GOARCH=amd64`) output of `examples/basic`
and from the Go standard library; the comment above each test is the `objdump -M intel`
disassembly. Decoding is checked by `decide` (kernel evaluation on the literal bytes), and the
executor by `simp`/`rfl` on concrete states. The differential oracle (`docs/ORACLE-AMD64.md`)
is the real test; these pin the reducibility the proof automation relies on.
-/

namespace JanusTests.Amd64
open Janus.Amd64

/-! ## Decoding -/

-- add rax, rbx
example : decode [0x48, 0x01, 0xd8] = some (.alu .add 64 (.reg 0) (.loc (.reg 3)), 3) := by decide
-- adc rax, rcx
example : decode [0x48, 0x11, 0xc8] = some (.alu .adc 64 (.reg 0) (.loc (.reg 1)), 3) := by decide
-- ret
example : decode [0xc3] = some (.ret 0, 1) := by decide
-- cmp rsp, QWORD PTR [r14+0x10]
example : decode [0x49, 0x3b, 0x66, 0x10] =
    some (.alu .cmp 64 (.reg 4) (.loc (.mem ⟨some 14, none, 0, 16, false, false⟩)), 4) := by decide
-- add rdx, QWORD PTR [rax+rcx*8]
example : decode [0x48, 0x03, 0x14, 0xc8] =
    some (.alu .add 64 (.reg 2) (.loc (.mem ⟨some 0, some 1, 3, 0, false, false⟩)), 4) := by decide
-- jg -0xc
example : decode [0x7f, 0xf4] = some (.jcc 15 (2 ^ 64 - 12), 2) := by decide
-- call rel32 (backwards)
example : decode [0xe8, 0xc8, 0xfe, 0xff, 0xff] = some (.call (2 ^ 64 - 0x138), 5) := by decide
-- lea rcx, [rip+0x22790]
example : decode [0x48, 0x8d, 0x0d, 0x90, 0x27, 0x02, 0x00] =
    some (.lea 64 1 ⟨none, none, 0, 0x22790, true, false⟩, 7) := by decide
-- movzx eax, BYTE PTR [rcx+rax*1]
example : decode [0x0f, 0xb6, 0x04, 0x01] =
    some (.movx false 32 8 0 (.mem ⟨some 1, some 0, 0, 0, false, false⟩), 4) := by decide
-- movups xmm14, XMMWORD PTR [rdx]
example : decode [0x44, 0x0f, 0x10, 0x32] =
    some (.sseMov false (.xmm 14) (.mem ⟨some 2, none, 0, 0, false, false⟩), 4) := by decide
-- nop DWORD PTR [rax]
example : decode [0x0f, 0x1f, 0x00] = some (.nop, 3) := by decide
-- xchg ax, ax (66 90) is a NOP; 41 90 is xchg r8d, eax
example : decode [0x66, 0x90] = some (.nop, 2) := by decide
example : decode [0x41, 0x90] = some (.xchg 32 (.reg 0) (.reg 8), 2) := by decide
-- mov ah, 1 (no REX: AH) vs mov spl, 1 (REX: SPL)
example : decode [0xb4, 0x01] = some (.mov 8 (.high 0) (.imm 1), 2) := by decide
example : decode [0x40, 0xb4, 0x01] = some (.mov 8 (.reg 4) (.imm 1), 3) := by decide

/-! ## Rejection (strict decoding) -/

-- int3, ud2, syscall
example : decode [0xcc] = none := by decide
example : decode [0x0f, 0x0b] = none := by decide
example : decode [0x0f, 0x05] = none := by decide
-- lock add eax, eax (register destination: #UD) ; fs: mov rax, [rax] ; addr32 mov eax, [eax]
example : decode [0xf0, 0x01, 0xc0] = none := by decide
-- FS-relative load (TLS): mov r14, fs:[-8]
example : decode [0x64, 0x4c, 0x8b, 0x34, 0x25, 0xf8, 0xff, 0xff, 0xff] =
    some (.mov 64 (.reg 14) (.loc (.mem ⟨none, none, 0, 0xfffffffffffffff8, false, true⟩)), 9) := by decide
example : decode [0x64, 0x48, 0x8b, 0x00] =
    some (.mov 64 (.reg 0) (.loc (.mem ⟨some 0, none, 0, 0, false, true⟩)), 4) := by decide
-- FS on LEA (segments are ignored), on a register form, and GS are rejected
example : decode [0x64, 0x48, 0x8d, 0x00] = none := by decide
example : decode [0x64, 0x48, 0x89, 0xc0] = none := by decide
example : decode [0x65, 0x48, 0x8b, 0x00] = none := by decide
-- VEX: vmovdqu ymm0, [rsi]; vpcmpeqb ymm4, ymm0, ymm1; vpmovmskb edx, ymm6; vzeroupper
example : decode [0xc5, 0xfe, 0x6f, 0x06] =
    some (.vmov false 256 (.xmm 0) (.mem ⟨some 6, none, 0, 0, false, false⟩), 4) := by decide
example : decode [0xc5, 0xfd, 0x74, 0xe1] = some (.vop .pcmpeqb 256 4 0 (.xmm 1), 4) := by decide
example : decode [0xc5, 0xfd, 0xd7, 0xd6] = some (.pmovmskb 256 2 6, 4) := by decide
example : decode [0xc5, 0xf8, 0x77] = some (.vzeroupper, 3) := by decide
-- vmovdqu ymm4, [r10] (3-byte VEX with VEX.B)
example : decode [0xc4, 0xc1, 0x7e, 0x7f, 0x22] =
    some (.vmov false 256 (.mem ⟨some 10, none, 0, 0, false, false⟩) (.xmm 4), 5) := by decide
-- VEX after a prefix, vvvv ≠ 1111 on a two-operand form, and VZEROALL are rejected
example : decode [0x66, 0xc5, 0xfe, 0x6f, 0x06] = none := by decide
example : decode [0xc5, 0xf6, 0x6f, 0x06] = none := by decide
example : decode [0xc5, 0xfc, 0x77] = none := by decide
example : decode [0x67, 0x8b, 0x00] = none := by decide
-- REX followed by a legacy prefix (the REX is ignored by hardware)
example : decode [0x48, 0x66, 0x01, 0xd8] = none := by decide
-- rcl eax, 1; rcr rbx, 1; rcl al, 1 (8/16-bit RCL/RCR not modelled)
example : decode [0xd1, 0xd0] = some (.rcx true 32 (.reg 0) (.imm 1), 2) := by decide
example : decode [0x48, 0xd1, 0xdb] = some (.rcx false 64 (.reg 3) (.imm 1), 3) := by decide
example : decode [0xd0, 0xd0] = none := by decide
-- VEX (mulx rax, rax, rbx: BMI2, decoded since the v3 extensions)
example : decode [0xc4, 0xe2, 0xfb, 0xf6, 0xc3] = some (.mulx 64 0 0 (.reg 3), 5) := by decide
-- truncated: add rax, [rip+disp32] with only two displacement bytes
example : decode [0x48, 0x03, 0x05, 0x00, 0x00] = none := by decide
-- 16 bytes: 15 prefixes + nop exceed the 15-byte limit
example : decode ((List.replicate 15 0x66) ++ [0x90]) = none := by decide

/-! ## Execution on concrete states -/

def s0 : State :=
  { regs := fun i => BitVec.ofNat 64 (i + 1), rip := 0x1000,
    flags := ⟨some false, some false, some false, some false, some false, some false⟩,
    xmm := fun _ => 0, mem := default }

/-- The fault of a result, if any (`State` has no decidable equality). -/
def faultOf : Except Fault State → Option Fault
  | .error e => some e
  | .ok _ => none

-- add rax, rbx: 1 + 4 = 5
example : (step [0x48, 0x01, 0xd8] s0).toOption.map (fun s => (s.regs 0, s.rip)) =
    some (5, 0x1003) := by decide
-- xor eax, eax clears the register and sets ZF, PF
example : (step [0x31, 0xc0] s0).toOption.map (fun s => (s.regs 0, s.flags.zf, s.flags.pf, s.flags.af)) =
    some (0, some true, some true, none) := by decide
-- mul rbx leaves SF, ZF, AF, PF undefined; reading ZF afterwards (je) faults
example : (step [0x48, 0xf7, 0xe3] s0).toOption.map (fun s => s.flags.zf) = some none := by decide
example : faultOf ((step [0x48, 0xf7, 0xe3] s0).bind (fun s => step [0x74, 0x00] s)) =
    some (.undefinedFlag 0x1003) := by decide
-- div by zero is #DE
example : faultOf (step [0x48, 0xf7, 0xf1] { s0 with regs := fun _ => 0 }) =
    some (.divideError 0x1000) := by decide
-- ret with no stack memory faults
example : faultOf (step [0xc3] s0) = some (.outsideAllocation 5 8) := by decide
-- 32-bit shift by 0 still zero-extends (found by the oracle)
example : (step [0xc1, 0xe0, 0x00] { s0 with regs := fun _ => 0xFFFFFFFF00000001 }).toOption.map
    (fun s => s.regs 0) = some 1 := by decide

/-! ## Atomics and string instructions -/

-- lock xadd [rax], ebx ; lock cmpxchg [rcx], rdx ; rep movsb ; rep stosq ; mfence
example : decode [0xf0, 0x0f, 0xc1, 0x18] = some (.locked (.xadd 32 (.mem ⟨some 0, none, 0, 0, false, false⟩) (.reg 3))
    ⟨some 0, none, 0, 0, false, false⟩ 4, 4) := by decide
example : decode [0xf0, 0x48, 0x0f, 0xb1, 0x11] = some (.locked (.cmpxchg 64 (.mem ⟨some 1, none, 0, 0, false, false⟩) (.reg 2))
    ⟨some 1, none, 0, 0, false, false⟩ 8, 5) := by decide
example : decode [0xf3, 0xa4] = some (.movs true 8, 2) := by decide
example : decode [0xf3, 0x48, 0xab] = some (.stos true 64, 3) := by decide
example : decode [0x0f, 0xae, 0xf0] = some (.nop, 3) := by decide
-- lock or [rax], ecx is the unlocked or, with the alignment check of a locked access
example : (decode [0xf0, 0x09, 0x08]).map (·.1) =
    (decode [0x09, 0x08]).map (fun x => Instr.locked x.1 ⟨some 0, none, 0, 0, false, false⟩ 4) := by decide
-- xchg [rax], ecx is locked implicitly
example : decode [0x87, 0x08] = some (.locked (.xchg 32 (.mem ⟨some 0, none, 0, 0, false, false⟩) (.reg 1))
    ⟨some 0, none, 0, 0, false, false⟩ 4, 2) := by decide
-- LOCK where it is #UD: register destination, CMP, MOV, a non-RMW string op; LOCK with F3
example : decode [0xf0, 0x48, 0x01, 0xc8] = none := by decide
example : decode [0xf0, 0x48, 0x39, 0x08] = none := by decide
example : decode [0xf0, 0x89, 0x08] = none := by decide
example : decode [0xf0, 0xa5] = none := by decide
example : decode [0xf0, 0xf3, 0x01, 0x08] = none := by decide
-- register-destination XADD/CMPXCHG are not modelled; REPNE MOVS and TPAUSE rejected
example : decode [0x0f, 0xc1, 0xd8] = none := by decide
example : decode [0xf2, 0xa4] = none := by decide
-- STD / CLD write the direction flag
example : decode [0xfd] = some (.setDF true, 1) := by decide
example : decode [0xfc] = some (.setDF false, 1) := by decide
example : decode [0x66, 0xfd] = none := by decide
example : decode [0x66, 0x0f, 0xae, 0xf0] = none := by decide

/-- A state with 64 writable bytes at `0x100` (byte `a` initially `a`). -/
def sm : State :=
  { s0 with mem := ⟨fun a => BitVec.ofNat 8 a, [⟨0x100, 64, true⟩]⟩,
            regs := fun i => if i = 0 then 0x0302 else if i = 1 then 3 else if i = 6 then 0x100
              else if i = 7 then 0x120 else BitVec.ofNat 64 (0x100 + i) }

-- lock cmpxchg [rsi], ax: AX = 0x0302 = [0x100..0x102) = 0x0100? no: unequal, AX ← 0x0100
example : (step [0xf0, 0x66, 0x0f, 0xb1, 0x06] sm).toOption.map (fun s => (s.regs 0, s.flags.zf)) =
    some (0x0100, some false) := by decide
-- equal: [0x102..0x104) = 0x0302 = AX, so it is replaced by CX = 3
example : (step [0xf0, 0x66, 0x0f, 0xb1, 0x4e, 0x02] sm).toOption.map
    (fun s => (s.mem.readLE 0x102 2, s.flags.zf, s.regs 0)) = some (3, some true, 0x0302) := by decide
-- lock xadd [rsi], cl: [0x100] = 0 → 3, CL ← 0
example : (step [0xf0, 0x0f, 0xc0, 0x0e] sm).toOption.map (fun s => (s.mem.readLE 0x100 1, s.regs 1)) =
    some (3, 0) := by decide
-- rep movsb with RCX = 3 copies 0x100..0x102 to 0x120..0x122 and leaves RCX = 0
example : (step [0xf3, 0xa4] sm).toOption.map (fun s => (s.mem.readLE 0x120 4, s.regs 1, s.regs 6, s.regs 7)) =
    some (0x23020100, 0, 0x103, 0x123) := by decide
-- movsb without REP: one byte, RCX unchanged
example : (step [0xa4] sm).toOption.map (fun s => (s.mem.readLE 0x120 2, s.regs 1)) =
    some (0x2100, 3) := by decide
-- rep stosw stores AX three times
example : (step [0xf3, 0x66, 0xab] sm).toOption.map (fun s => (s.mem.readLE 0x120 6, s.regs 7)) =
    some (0x030203020302, 0x126) := by decide
-- a REP run that leaves the region faults
example : faultOf (step [0xf3, 0xa4] { sm with regs := fun i => if i = 1 then 100 else sm.regs i }) =
    some (.outsideAllocation 0x140 1) := by decide
-- cmpxchg16b needs a 16-aligned operand
example : faultOf (step [0x48, 0x0f, 0xc7, 0x4e, 0x01] sm) = some (.misaligned 0x101) := by decide

/-! ## Specifications: return addresses and faults -/

section Spec
open Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `RET` alone at `0x1000`. -/
def retProg : Program := { segments := [⟨"f", 0x1000, [0xc3]⟩], stubs := [], exitAddr := 0 }

/-- Returns to every admissible return address read from `[RSP]`. -/
example (x : BitVec 64) :
    Ensures retProg 0x1000 [x] (fun s => StackWritable s 0 8) (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨hle, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run

example : RetAddr retProg 0x2000 := RetAddr.of_check (by decide)
example : ¬ RetAddr retProg 0x1000 := fun h => h.ne_of_fetch (pc := 0x1000) (w := [0xc3]) rfl rfl
example : ¬ RetAddr retProg (2 ^ 47) := fun h => by have := h.user; omega

/-- A `RET` with no readable stack faults: not "never panics". -/
example (ret : Nat) (s : State) (hs : CallSetup (retProg.withExit ret) 0x1000 [] s)
    (hm : s.mem.regions = []) (hr : ret ≠ 0x1000) : Faults (retProg.withExit ret) s := by
  have hpc : s.rip.toNat = 0x1000 := hs.rip_toNat (by decide)
  refine ⟨1, _, Program.run_succ_fault (w := [0xc3]) (e := .outsideAllocation (s.regs 4).toNat 8)
    (by rw [hpc]; exact Ne.symm hr) (by rw [hpc]; rfl) (by rw [hpc]; rfl) ?_, by simp⟩
  rw [step_of_decode (i := .ret 0) (len := 1) (by decide)]
  simp [exec, load, Janus.Arm64.Memory.accessible, hm]

end Spec


/-! ## Vector and FS execution -/

-- rcr rbx, 1 with CF = 1: 0x8000…0002 (rbx = 4 in s0, so 4 >> 1 with CF in the top bit)
example : (step [0x48, 0xd1, 0xdb] { s0 with flags := { s0.flags with cf := some true } }).toOption.map
    (fun s => (s.regs 3, s.flags.cf)) = some (0x8000000000000002, some false) := by decide
-- vzeroupper clears the upper halves
example : (step [0xc5, 0xf8, 0x77] { s0 with ymmHi := fun _ => 7 }).toOption.map
    (fun s => (s.ymmHi 3).toNat) = some 0 := by decide
-- vpxor xmm0, xmm0, xmm0 (VEX.128) zeroes ymm0 entirely; pxor xmm0, xmm0 keeps the upper half
example : (step [0xc5, 0xf9, 0xef, 0xc0] { s0 with ymmHi := fun _ => 7, xmm := fun _ => 5 }).toOption.map
    (fun s => (s.xmm 0, s.ymmHi 0)) = some (0, 0) := by decide
example : (step [0x66, 0x0f, 0xef, 0xc0] { s0 with ymmHi := fun _ => 7, xmm := fun _ => 5 }).toOption.map
    (fun s => (s.xmm 0, s.ymmHi 0)) = some (0, 7) := by decide
-- pcmpeqb xmm0, xmm1 then pmovmskb edx, xmm0: equal registers give 0xffff
example : ((step [0x66, 0x0f, 0x74, 0xc1] { s0 with xmm := fun _ => 0x1234 }).bind
    (fun s => step [0x66, 0x0f, 0xd7, 0xd0] s)).toOption.map (fun s => s.regs 2) = some 0xffff := by decide
-- vpmovmskb of a 256-bit value with only byte 31's top bit set
example : (step [0xc5, 0xfd, 0xd7, 0xd6] { s0 with ymmHi := fun _ => BitVec.ofNat 128 (2 ^ 127) }).toOption.map
    (fun s => s.regs 2) = some 0x80000000 := by decide
-- mov r14, fs:[-8] reads the TLS slot at fsBase - 8
def sTls : State :=
  { s0 with fsBase := 0x2008,
            mem := { bytes := fun a => if a = 0x2000 then 0x2a else 0, regions := [⟨0x2000, 8, false⟩] } }
example : (step [0x64, 0x4c, 0x8b, 0x34, 0x25, 0xf8, 0xff, 0xff, 0xff] sTls).toOption.map
    (fun s => s.regs 14) = some 0x2a := by decide
example : faultOf (step [0x64, 0x4c, 0x8b, 0x34, 0x25, 0xf8, 0xff, 0xff, 0xff] { sTls with fsBase := 0 }) =
    some (.outsideAllocation 0xfffffffffffffff8 8) := by decide

/-! ## Direction flag, split locks, BSF of zero (audit round 2) -/

/-- Audit round 2, MEDIUM-1 regression: `REP MOVSQ` with `RCX = 2` right after `STD`
(memmove's backward path). The words go to `RDI`, `RDI - 8` from `RSI`, `RSI - 8`, and both
pointers step down by 16, as on hardware; the forward claim of
`DFRepro.memmove_backward_rep_copies_forward` is false for every state with `df = true`. -/
def dfMem : Memory :=
  ⟨fun a => if a = 0x3000 then 0x11 else if a = 0x3008 then 0x22 else if a = 0x3010 then 0x33 else 0,
   [⟨0x2000, 0x40, true⟩, ⟨0x3000, 0x40, false⟩]⟩

def dfState : State :=
  { regs := fun i => if i = 1 then 2 else if i = 6 then 0x3008 else if i = 7 then 0x2008 else 0,
    rip := 0x47d6e9, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := dfMem, df := true }

example : (step [0xf3, 0x48, 0xa5] dfState).toOption.map (fun t =>
    (t.regs 6, t.regs 7, t.regs 1, t.mem.readLE 0x2008 8, t.mem.readLE 0x2000 8, t.mem.readLE 0x2010 8)) =
    some (0x2ff8, 0x1ff8, 0, 0x22, 0x11, 0) := by decide

/-- The forward-copy claim of the round-2 repro does not hold with `DF = 1`. -/
theorem df_backward_not_forward : ¬ ∃ t', step [0xf3, 0x48, 0xa5] dfState = .ok t' ∧
    t'.regs 6 = 0x3018 ∧ t'.regs 7 = 0x2018 := by
  rintro ⟨t', h, h6, -⟩
  have : (step [0xf3, 0x48, 0xa5] dfState).toOption.map (fun t => t.regs 6) = some 0x2ff8 := by decide
  rw [h] at this
  obtain ⟨a, ha, ha6⟩ := Option.map_eq_some_iff.1 this
  simp only [Except.toOption, Option.some.injEq] at ha
  subst ha
  rw [h6] at ha6
  exact absurd ha6 (by decide)

-- STD then STOSB stores at RDI and steps down
example : ((step [0xfd] { sm with df := false }).bind (fun s => step [0xaa] s)).toOption.map
    (fun t => (t.df, t.regs 7)) = some (true, 0x11f) := by
  decide

-- LOCK XADD on a misaligned qword faults; aligned it runs (split-lock policy)
example : faultOf (step [0xf0, 0x48, 0x0f, 0xc1, 0x07] { sm with regs := fun i => if i = 7 then 0x104 else 0 }) =
    some (.misaligned 0x104) := by decide
example : faultOf (step [0xf0, 0x48, 0x0f, 0xc1, 0x07] { sm with regs := fun i => if i = 7 then 0x108 else 0 }) =
    none := by decide

-- 64-bit BSF of zero: undefined destination, fault (vendor-neutral)
example : faultOf (step [0x48, 0x0f, 0xbc, 0xc1] { s0 with regs := fun _ => 0 }) =
    some (.undefinedResult 0x1000) := by decide

/-! ## GOAMD64=v3: BMI1/BMI2, MOVBE, scalar FMA, SSSE3 (encodings from the v3 std test binaries) -/

-- shlx rsi, rsi, rbx (internal/abi.Name.IsBlank)
example : decode [0xc4, 0xe2, 0xe1, 0xf7, 0xf6] = some (.shiftx .shl 64 6 (.reg 6) 3, 5) := by decide
-- shrx rsi, rax, rdx (internal/strconv.atof64exact)
example : decode [0xc4, 0xe2, 0xeb, 0xf7, 0xf0] = some (.shiftx .shr 64 6 (.reg 0) 2, 5) := by decide
-- sarx rcx, rcx, rdx (reflect.(*rtype).OverflowInt)
example : decode [0xc4, 0xe2, 0xea, 0xf7, 0xc9] = some (.shiftx .sar 64 1 (.reg 1) 2, 5) := by decide
-- andn rdi, rdi, r8 (internal/runtime/maps.(*table).Clear)
example : decode [0xc4, 0xc2, 0xc0, 0xf2, 0xf8] = some (.andn 64 7 7 (.reg 8), 5) := by decide
-- blsr rdx, rsi (internal/strconv.formatBits) ; blsi rcx, rsi (math/big.nat.itoa)
example : decode [0xc4, 0xe2, 0xe8, 0xf3, 0xce] = some (.blsx 1 64 2 (.reg 6), 5) := by decide
example : decode [0xc4, 0xe2, 0xf0, 0xf3, 0xde] = some (.blsx 3 64 1 (.reg 6), 5) := by decide
-- movbe QWORD PTR [rsp+0x28], rdx (runtime.randinit)
example : decode [0x48, 0x0f, 0x38, 0xf1, 0x54, 0x24, 0x28] =
    some (.movbe 64 (.mem ⟨some 4, none, 0, 0x28, false, false⟩) (.reg 2), 7) := by decide
-- vfmadd231sd xmm0, xmm2, xmm1 (runtime.fastexprand) ; vfmadd231ss (math/rand.ExpFloat64)
example : decode [0xc4, 0xe2, 0xe9, 0xb9, 0xc1] = some (.vfmas 64 231 false false 0 2 (.xmm 1), 5) := by decide
example : decode [0xc4, 0xe2, 0x69, 0xb9, 0xc1] = some (.vfmas 32 231 false false 0 2 (.xmm 1), 5) := by decide
-- pshufb xmm0, xmm15 ; psignb xmm0, xmm0 (the Swiss-table group match)
example : decode [0x66, 0x41, 0x0f, 0x38, 0x00, 0xc7] = some (.sseOp .pshufb 0 (.xmm 15), 6) := by decide
example : decode [0x66, 0x0f, 0x38, 0x08, 0xc0] = some (.sseOp .psignb 0 (.xmm 0), 5) := by decide
-- rejected: SHLX with VEX.L1 (#UD), MOVBE register form (#UD), MMX PSHUFB, CRC32,
-- VFMADD231PD (packed), RORX with VEX.vvvv ≠ 1111
example : decode [0xc4, 0xe2, 0xe5, 0xf7, 0xf6] = none := by decide
example : decode [0x48, 0x0f, 0x38, 0xf1, 0xc2] = none := by decide
example : decode [0x0f, 0x38, 0x00, 0xc1] = none := by decide
example : decode [0xf2, 0x0f, 0x38, 0xf0, 0xc1] = none := by decide
example : decode [0xc4, 0xe2, 0xe9, 0xb8, 0xc1] = none := by decide
example : decode [0xc4, 0xe3, 0xf3, 0xf0, 0xc1, 0x05] = none := by decide

-- WP-J: notrack jmp *%rax (gcc's CET jump-table dispatch); notrack call *%rdx; other segment
-- prefixes on indirect branches stay rejected
example : decode [0x3e, 0xff, 0xe0] = some (.jmpInd (.reg 0), 3) := by decide
example : decode [0x3e, 0xff, 0xd2] = some (.callInd (.reg 2), 3) := by decide
example : decode [0x2e, 0xff, 0xe0] = none := by decide
example : decode [0x3e, 0x66, 0xff, 0xe0] = none := by decide
-- the padded `call __tls_get_addr` (66 66 48 E8 rel32) and the `data16 lea` before it
example : decode [0x66, 0x66, 0x48, 0xe8, 0x10, 0, 0, 0] = some (.call 0x10, 8) := by decide
example : decode [0x66, 0xe8, 0x10, 0, 0, 0] = none := by decide
example : decode [0x66, 0x48, 0x8d, 0x3d, 0, 0, 0, 0] =
    some (.lea 64 7 ⟨none, none, 0, 0, true, false⟩, 8) := by decide
-- x87: fldt 0x10(%rbp); fld1; faddp; fmulp; fucomip; fnstcw/fldcw; fistpll; fsubrp (Intel: ST(1) ← ST(0) - ST(1))
example : decode [0xdb, 0x6d, 0x10] =
    some (.x87 (.ld (.mem .f80)) (some ⟨some 5, none, 0, 0x10, false, false⟩), 3) := by decide
example : decode [0xd9, 0xe8] = some (.x87 (.ldConst X87.one80) none, 2) := by decide
example : decode [0xde, 0xc1] = some (.x87 (.arithTo .add 1 true) none, 2) := by decide
example : decode [0xde, 0xc9] = some (.x87 (.arithTo .mul 1 true) none, 2) := by decide
example : decode [0xdf, 0xe9] = some (.x87 (.comi true 1 true) none, 2) := by decide
example : decode [0xde, 0xe1] = some (.x87 (.arithTo .subr 1 true) none, 2) := by decide
example : decode [0xd9, 0x7c, 0x24, 0x0e] =
    some (.x87 .nstcw (some ⟨some 4, none, 0, 0x0e, false, false⟩), 4) := by decide
example : decode [0xdf, 0x7c, 0x24, 0x08] =
    some (.x87 (.ist .i64 false true) (some ⟨some 4, none, 0, 8, false, false⟩), 4) := by decide
-- rejected: fnstenv, frstor, ffree, fsin, 66-prefixed fld, REX.W fld, prefixed register form
example : decode [0xd9, 0x30] = none := by decide
example : decode [0xdd, 0x20] = none := by decide
example : decode [0xdd, 0xc0] = none := by decide
example : decode [0xd9, 0xfe] = none := by decide
example : decode [0x66, 0xdb, 0x28] = none := by decide
example : decode [0x48, 0xdb, 0x28] = none := by decide
example : decode [0x40, 0xde, 0xc1] = none := by decide
-- 1.5 * 3 = 4.5, round to nearest at 64-bit precision; 1/3 at PC = 24 is rounded to 24 bits
example : (X87.binop .mul 64 .rne (X87.pack80 false 16383 0xC000000000000000)
    (X87.pack80 false 16384 0xC000000000000000)).res = X87.pack80 false 16385 0x9000000000000000 := by decide
example : (X87.binop .div 24 .rne X87.one80 (X87.pack80 false 16384 0xC000000000000000)).res =
    X87.pack80 false 16381 0xAAAAAB0000000000 := by decide
-- an unnormal operand is invalid even next to a NaN; two QNaNs of equal significand: the positive one
example : (X87.binop .add 64 .rne (X87.pack80 false 0x4000 0x4000000000000000)
    (X87.pack80 false 0x7FFF 0xC000000000000001)).res = X87.indefinite80 := by decide
example : (X87.binop .add 64 .rne (X87.pack80 true 0x7FFF 0xC000000000000001)
    (X87.pack80 false 0x7FFF 0xC000000000000001)).res = X87.pack80 false 0x7FFF 0xC000000000000001 := by decide

end JanusTests.Amd64

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
    some (.alu .cmp 64 (.reg 4) (.loc (.mem ⟨some 14, none, 0, 16, false⟩)), 4) := by decide
-- add rdx, QWORD PTR [rax+rcx*8]
example : decode [0x48, 0x03, 0x14, 0xc8] =
    some (.alu .add 64 (.reg 2) (.loc (.mem ⟨some 0, some 1, 3, 0, false⟩)), 4) := by decide
-- jg -0xc
example : decode [0x7f, 0xf4] = some (.jcc 15 (2 ^ 64 - 12), 2) := by decide
-- call rel32 (backwards)
example : decode [0xe8, 0xc8, 0xfe, 0xff, 0xff] = some (.call (2 ^ 64 - 0x138), 5) := by decide
-- lea rcx, [rip+0x22790]
example : decode [0x48, 0x8d, 0x0d, 0x90, 0x27, 0x02, 0x00] =
    some (.lea 64 1 ⟨none, none, 0, 0x22790, true⟩, 7) := by decide
-- movzx eax, BYTE PTR [rcx+rax*1]
example : decode [0x0f, 0xb6, 0x04, 0x01] =
    some (.movx false 32 8 0 (.mem ⟨some 1, some 0, 0, 0, false⟩), 4) := by decide
-- movups xmm14, XMMWORD PTR [rdx]
example : decode [0x44, 0x0f, 0x10, 0x32] =
    some (.sseMov false (.xmm 14) (.mem ⟨some 2, none, 0, 0, false⟩), 4) := by decide
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
example : decode [0x64, 0x48, 0x8b, 0x00] = none := by decide
example : decode [0x67, 0x8b, 0x00] = none := by decide
-- REX followed by a legacy prefix (the REX is ignored by hardware)
example : decode [0x48, 0x66, 0x01, 0xd8] = none := by decide
-- rcl eax, 1 (not modelled)
example : decode [0xd1, 0xd0] = none := by decide
-- VEX (mulx)
example : decode [0xc4, 0xe2, 0xfb, 0xf6, 0xc3] = none := by decide
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
example : decode [0xf0, 0x0f, 0xc1, 0x18] = some (.xadd 32 (.mem ⟨some 0, none, 0, 0, false⟩) (.reg 3), 4) := by decide
example : decode [0xf0, 0x48, 0x0f, 0xb1, 0x11] = some (.cmpxchg 64 (.mem ⟨some 1, none, 0, 0, false⟩) (.reg 2), 5) := by decide
example : decode [0xf3, 0xa4] = some (.movs true 8, 2) := by decide
example : decode [0xf3, 0x48, 0xab] = some (.stos true 64, 3) := by decide
example : decode [0x0f, 0xae, 0xf0] = some (.nop, 3) := by decide
-- lock or [rax], ecx is the unlocked or
example : (decode [0xf0, 0x09, 0x08]).map (·.1) = (decode [0x09, 0x08]).map (·.1) := by decide
-- LOCK where it is #UD: register destination, CMP, MOV, a non-RMW string op; LOCK with F3
example : decode [0xf0, 0x48, 0x01, 0xc8] = none := by decide
example : decode [0xf0, 0x48, 0x39, 0x08] = none := by decide
example : decode [0xf0, 0x89, 0x08] = none := by decide
example : decode [0xf0, 0xa5] = none := by decide
example : decode [0xf0, 0xf3, 0x01, 0x08] = none := by decide
-- register-destination XADD/CMPXCHG are not modelled; REPNE MOVS, STD and TPAUSE rejected
example : decode [0x0f, 0xc1, 0xd8] = none := by decide
example : decode [0xf2, 0xa4] = none := by decide
example : decode [0xfd] = none := by decide
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

end JanusTests.Amd64

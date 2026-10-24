import Janus

/-!
# Round 5 (item 6): hand-derived edge cases, checked against the model by the kernel

Each `example` evaluates `Janus.Arm64.step` / `Janus.Amd64.step` on a concrete state. The
expected value on the right is computed by hand from the Arm ARM (DDI 0487) ASL or the Intel
SDM pseudocode (the derivation is in the comment above it), not taken from the model or from
hardware. The same encodings are also run against hardware by `run-model.sh` (`gen.py`).
Compile with `lake env lean audit/round5/model/HandDerived.lean`.
-/

namespace Round5.A64
open Janus.Arm64

def st (x : Nat → Nat) (sp : Nat) (v : Nat → Nat) : State :=
  { regs := fun i => BitVec.ofNat 64 (x i), sp := BitVec.ofNat 64 sp, pc := 0x1000000800,
    flags := ⟨false, false, false, false⟩, mem := default,
    vregs := fun i => BitVec.ofNat 128 (v i) }

def nzcvOf (f : Flags) : Nat :=
  (if f.n then 8 else 0) + (if f.z then 4 else 0) + (if f.c then 2 else 0) + (if f.v then 1 else 0)

/-- [SP, pc, NZCV (N=8 Z=4 C=2 V=1), X0..X7, V0..V3] after one step, or `none` on a fault. -/
def obs (r : Except Fault State) : Option (List Nat) :=
  match r with
  | .ok s => some ([s.sp.toNat, s.pc.toNat, nzcvOf s.flags] ++
      (List.range 8).map (fun i => (s.regs i).toNat) ++ (List.range 4).map (fun i => (s.vregs i).toNat))
  | .error _ => none

def isFault (r : Except Fault State) : Bool := match r with | .error _ => true | .ok _ => false

-- ADD SP, X3, W7, SXTW #4 (0x8b27d07f). ASL: Rn = 3, so operand1 = X3 = 0x1000;
-- operand2 = LSL(SignExtend(X7<31:0>), 4) = 0xFFFFFFFF80000000 << 4 = 0xFFFFFFF800000000;
-- d = 31 and !setflags, so SP = 0xFFFFFFF800001000; X registers and flags unchanged.
example : obs (step 0x8b27d07f (st (fun i => if i = 3 then 0x1000 else if i = 7 then 0x80000000 else 0) 0x40 (fun _ => 0))) =
    some ([0xFFFFFFF800001000, 0x1000000804, 0] ++
      [0, 0, 0, 0x1000, 0, 0, 0, 0x80000000] ++ [0, 0, 0, 0]) := by decide

-- SUBS WZR, WSP, W7, UXTX (CMP WSP, W7; 0x6b2763ff). Rn = 31 is SP (W view: 0x10 of
-- SP = 0x100000010); ExtendReg reads X[m, 32] (len = Min(64, 32)), so X7 = 0x100000010 gives
-- 0x10; 0x10 - 0x10 = 0: N=0 Z=1 C=1 (no borrow) V=0. Rd = 31 with S = 1 is WZR: SP unchanged.
example : obs (step 0x6b2763ff (st (fun i => if i = 7 then 0x100000010 else 0) 0x100000010 (fun _ => 0))) =
    some ([0x100000010, 0x1000000804, 6] ++
      [0, 0, 0, 0, 0, 0, 0, 0x100000010] ++ [0, 0, 0, 0]) := by decide

-- ADD X5, X3, X7, UXTB #5 (0x8b271465): imm3 > 4 is UNDEFINED (ASL decode).
example : isFault (step 0x8b271465 (st (fun _ => 0) 0 (fun _ => 0))) = true := by decide

-- SSHR V0.2D, V1.2D, #64 (0x4f400420): immh:immb = 1000:000 = 64, esize = 64,
-- shift = 2*64 - 64 = 64: each lane becomes its sign: 0x8000.. -> all ones, 0x7fff.. -> 0.
example : obs (step 0x4f400420 (st (fun _ => 0) 0 (fun i => if i = 1 then 0x7fffffffffffffff8000000000000000 else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0xffffffffffffffff, 0x7fffffffffffffff8000000000000000, 0, 0]) := by decide

-- USHR V0.2D, V1.2D, #64 (0x6f400420): the same shift, unsigned: every lane is 0.
example : obs (step 0x6f400420 (st (fun _ => 0) 0 (fun i => if i = 0 then 5 else if i = 1 then (2 ^ 128 - 1) else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 2 ^ 128 - 1, 0, 0]) := by decide

-- SRI V2.8B, V1.8B, #8 (0x2f084422): esize = 8, shift = 16 - 8 = 8, mask = Ones(8) >> 8 = 0:
-- V2<63:0> unchanged; Q = 0 so V2<127:64> = 0.
example : obs (step 0x2f084422 (st (fun _ => 0) 0 (fun i => if i = 1 then 0x1234 else if i = 2 then 2 ^ 128 - 1 else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0x1234, 0xffffffffffffffff, 0]) := by decide

-- SLI V2.16B, V1.16B, #0 (0x6f085422): shift = 8 - 8 = 0, mask = Ones(8): V2 := V1.
example : obs (step 0x6f085422 (st (fun _ => 0) 0 (fun i => if i = 1 then 0x0123456789abcdeffedcba9876543210 else if i = 2 then 7 else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0x0123456789abcdeffedcba9876543210, 0x0123456789abcdeffedcba9876543210, 0]) := by decide

-- SSHR with Q = 0 and immh<3> = 1 (0x0f400420): reserved.
example : isFault (step 0x0f400420 (st (fun _ => 0) 0 (fun _ => 0))) = true := by decide

-- UADDLV H0, V1.16B (0x6e303820): 16 * 255 = 4080 = 0xff0, no wrap at 8 bits; V0 = 0xff0.
example : obs (step 0x6e303820 (st (fun _ => 0) 0 (fun i => if i = 1 then 2 ^ 128 - 1 else 9))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0xff0, 2 ^ 128 - 1, 9, 9]) := by decide

-- SMAXV / UMAXV B0, V1.16B on bytes 0x7f, 0x80, ...: signed max 0x7f, unsigned max 0x80.
example : obs (step 0x4e30a820 (st (fun _ => 0) 0 (fun i => if i = 1 then 0x807f807f807f807f807f807f807f807f else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0x7f, 0x807f807f807f807f807f807f807f807f, 0, 0]) := by decide
example : obs (step 0x6e30a820 (st (fun _ => 0) 0 (fun i => if i = 1 then 0x807f807f807f807f807f807f807f807f else 0))) =
    some ([0, 0x1000000804, 0] ++
      [0, 0, 0, 0, 0, 0, 0, 0] ++ [0x80, 0x807f807f807f807f807f807f807f807f, 0, 0]) := by decide

-- ADDV S0, V1.2S (0x0eb1b820): size = 10 with Q = 0 is reserved.
example : isFault (step 0x0eb1b820 (st (fun _ => 0) 0 (fun _ => 0))) = true := by decide

end Round5.A64

namespace Round5.X64
open Janus.Amd64

def s0 (r : Nat → Nat) : State :=
  { regs := fun i => BitVec.ofNat 64 (r i), rip := 0x1000,
    flags := ⟨some false, some false, some false, some false, some false, some false⟩,
    xmm := fun _ => 0, mem := default }

/-- [RAX, RCX, RDX, rip, CF, ZF] (flags: 0 false, 1 true, 2 undefined) after one step. -/
def ob : Option Bool → Nat
  | some false => 0 | some true => 1 | none => 2

def obs (r : Except Fault State) : Option (List Nat) :=
  match r with
  | .ok s => some [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, s.rip.toNat, ob s.flags.cf, ob s.flags.zf]
  | .error _ => none

def isFault (r : Except Fault State) : Bool := match r with | .error _ => true | .ok _ => false

-- BT EDX, ECX (0F A3 CA) with ECX = 33: register bit base, offset MOD 32 = 1; EDX = 2 -> CF = 1.
-- ZF is undefined in the model (Intel: unaffected, AMD: undefined); the register is not written.
example : obs (step [0x0f, 0xa3, 0xca] (s0 fun i => if i = 1 then 33 else if i = 2 then 2 else 0)) =
    some [0, 33, 2, 0x1003, 1, 2] := by decide

-- BTS RDX, imm8 200 (48 0F BA EA C8): 200 MOD 64 = 8: RDX = 0 -> 0x100, CF = 0.
example : obs (step [0x48, 0x0f, 0xba, 0xea, 0xc8] (s0 fun _ => 0)) =
    some [0, 0, 0x100, 0x1005, 0, 2] := by decide

-- SHLD DX, AX, 16 (66 0F A4 C2 10): COUNT = 16 = operand size: DX = AX = 0xabcd; CF = the
-- last bit shifted out = DEST[16 - 16] = DEST[0] = 1 (DX = 0x1235); ZF = 0. RDX<63:16> kept.
example : obs (step [0x66, 0x0f, 0xa4, 0xc2, 0x10] (s0 fun i => if i = 0 then 0xabcd else if i = 2 then 0x777700001235 else 0)) =
    some [0xabcd, 0, 0x77770000abcd, 0x1005, 1, 0] := by decide

-- SHLD DX, AX, 17: COUNT > operand size, result undefined (the model faults).
example : isFault (step [0x66, 0x0f, 0xa4, 0xc2, 0x11] (s0 fun _ => 1)) = true := by decide

-- SHRD EDX, EAX, 32 (0F AC C2 20): COUNT = 32 MOD 32 = 0: flags unchanged, but the 32-bit
-- destination is written, so RDX<63:32> is cleared.
example : obs (step [0x0f, 0xac, 0xc2, 0x20] (s0 fun i => if i = 2 then 0xffffffff00000005 else 0)) =
    some [0, 0, 5, 0x1004, 0, 0] := by decide

-- TZCNT EDX, EAX (F3 0F BC D0), EAX = 0: EDX = 32 (operand size), CF = 1, ZF = 0 (result /= 0).
example : obs (step [0xf3, 0x0f, 0xbc, 0xd0] (s0 fun i => if i = 2 then 0xffffffffffffffff else 0)) =
    some [0, 0, 32, 0x1004, 1, 0] := by decide

-- LZCNT RDX, RAX (F3 48 0F BD D0), RAX = 1: 63 leading zeros, CF = 0, ZF = 0.
example : obs (step [0xf3, 0x48, 0x0f, 0xbd, 0xd0] (s0 fun i => if i = 0 then 1 else 0)) =
    some [1, 0, 63, 0x1005, 0, 0] := by decide

-- POPCNT RDX, RAX (F3 48 0F B8 D0), RAX = 2^64 - 1: 64, ZF = 0, CF cleared.
example : obs (step [0xf3, 0x48, 0x0f, 0xb8, 0xd0] (s0 fun i => if i = 0 then 2 ^ 64 - 1 else 0)) =
    some [2 ^ 64 - 1, 0, 64, 0x1005, 0, 0] := by decide

-- BSF EDX, EAX with EAX = 0: destination undefined (Intel), so the model faults.
example : isFault (step [0x0f, 0xbc, 0xd0] (s0 fun _ => 0)) = true := by decide

-- BSR EDX, EAX with EAX = 0x80000000: index 31, ZF = 0; EDX zero-extended.
example : obs (step [0x0f, 0xbd, 0xd0] (s0 fun i => if i = 0 then 0x80000000 else if i = 2 then 2 ^ 64 - 1 else 0)) =
    some [0x80000000, 0, 31, 0x1003, 2, 0] := by decide

end Round5.X64

import Janus
open Janus.Amd64

/-! Executor probes on concrete states. Run: `lake env lean audit/round2/amd64/ExecProbe.lean`.
Compare with `host/probe` (same cases on the host CPU). -/

def mem0 : Memory := ⟨fun a => BitVec.ofNat 8 (a % 251), [⟨0x1000, 0x1000, true⟩]⟩
def st (regs : List (Nat × Nat)) (m : Memory := mem0) : State :=
  { regs := fun i => match regs.lookup i with | some v => BitVec.ofNat 64 v | none => 0,
    rip := 0x400000, flags := ⟨some false, some false, some false, some false, some false, some false⟩,
    xmm := fun _ => 0, mem := m }

def show1 (r : Except Fault State) (rs : List Nat) (addrs : List (Nat × Nat) := []) : String :=
  match r with
  | .error e => s!"FAULT {repr e}"
  | .ok s => s!"regs={rs.map (fun i => (i, Nat.toDigits 16 (s.regs i).toNat |> String.ofList))} flags=cf{repr s.flags.cf} zf{repr s.flags.zf} sf{repr s.flags.sf} of{repr s.flags.ovf} pf{repr s.flags.pf} af{repr s.flags.af} mem={addrs.map (fun (a, n) => Nat.toDigits 16 (s.mem.readLE a n) |> String.ofList)}"

def run1 (bs : List Nat) (s : State) := step bs s

#eval show IO Unit from do
  -- IMUL r/m64 one-operand, signed: RAX=-1 * RCX=3 -> RDX:RAX = -3 (RDX all ones)
  IO.println s!"imul1 -1*3: {show1 (run1 [0x48,0xF7,0xE9] (st [(0, 2^64-1), (1, 3)])) [0,2]}"
  -- RAX = -5 * RCX = 7 -> -35 ; RDX = -1
  IO.println s!"imul1 -5*7: {show1 (run1 [0x48,0xF7,0xE9] (st [(0, 2^64-5), (1, 7)])) [0,2]}"
  -- 8-bit IMUL CL: AL=0xFF(-1) * CL=0x03 -> AX = 0xFFFD
  IO.println s!"imul8: {show1 (run1 [0xF6,0xE9] (st [(0, 0xFF), (1, 3)])) [0]}"
  -- IDIV: RDX:RAX = -7, RCX = 2 -> q=-3, r=-1
  IO.println s!"idiv -7/2: {show1 (run1 [0x48,0xF7,0xF9] (st [(0, 2^64-7), (2, 2^64-1), (1, 2)])) [0,2]}"
  -- CMPXCHG [rbx], ecx 32-bit, success: RAX upper bits must be preserved
  let m1 : Memory := { mem0 with bytes := fun a => if a = 0x1000 then 0x44 else if a < 0x1004 ∧ 0x1000 < a then 0 else mem0.bytes a }
  IO.println s!"cmpxchg32 ok: {show1 (run1 [0x0F,0xB1,0x0B] (st [(0, 0xDEADBEEF00000044), (3, 0x1000), (1, 0x55)] m1)) [0] [(0x1000, 8)]}"
  IO.println s!"cmpxchg32 fail: {show1 (run1 [0x0F,0xB1,0x0B] (st [(0, 0xDEADBEEF00000045), (3, 0x1000), (1, 0x55)] m1)) [0] [(0x1000, 8)]}"
  -- CMPXCHG8B [rsi]: success leaves RAX/RDX alone; failure loads zero-extended
  IO.println s!"cmpxchg8b fail: {show1 (run1 [0x0F,0xC7,0x0E] (st [(0, 0xAAAA000000000001), (2, 0xBBBB000000000002), (6, 0x1000)])) [0,2] [(0x1000,8)]}"
  -- XADD [rbx], ah
  IO.println s!"xadd8 ah: {show1 (run1 [0x0F,0xC0,0x23] (st [(0, 0x1234), (3, 0x1000)])) [0] [(0x1000,1)]}"
  -- REP MOVSB rcx=0: nothing, rcx stays 0, flags untouched, even if RSI/RDI are unmapped
  IO.println s!"rep movsb rcx=0 unmapped: {show1 (run1 [0xF3,0xA4] (st [(1, 0), (6, 0xdead0000), (7, 0xbeef0000)])) [1,6,7]}"
  IO.println s!"rep stosq rcx=0 unmapped: {show1 (run1 [0xF3,0x48,0xAB] (st [(1, 0), (7, 0xbeef0000)])) [1,7]}"
  -- overlapping forward REP MOVSB, dst = src + 1, 4 bytes: pattern propagation
  IO.println s!"rep movsb overlap: {show1 (run1 [0xF3,0xA4] (st [(1, 4), (6, 0x1000), (7, 0x1001)])) [1,6,7] [(0x1000, 5)]}"
  -- REP MOVSQ crossing out of the region faults (partial progress is not a result)
  IO.println s!"rep movsq leaves region: {show1 (run1 [0xF3,0x48,0xA5] (st [(1, 3), (6, 0x1FF0), (7, 0x1000)])) [1]}"
  -- non-REP movsd (A5, 32-bit) leaves RCX alone
  IO.println s!"movsd: {show1 (run1 [0xA5] (st [(1, 77), (6, 0x1000), (7, 0x1800)])) [1,6,7] [(0x1800,4)]}"
  -- BSF 64 of zero: dst unchanged
  IO.println s!"bsf64 0: {show1 (run1 [0x48,0x0F,0xBC,0xC1] (st [(0, 0x1234), (1, 0)])) [0]}"
  IO.println s!"bsf32 0: {show1 (run1 [0x0F,0xBC,0xC1] (st [(0, 0x1234), (1, 0)])) [0]}"
  -- LZCNT / TZCNT
  IO.println s!"lzcnt64 1: {show1 (run1 [0xF3,0x48,0x0F,0xBD,0xC1] (st [(1, 1)])) [0]}"
  IO.println s!"tzcnt64 0: {show1 (run1 [0xF3,0x48,0x0F,0xBC,0xC1] (st [(1, 0)])) [0]}"
  -- MOVQ xmm0 <- rax / movq xmm1,xmm0 zeroing
  IO.println s!"movaps misaligned: {show1 (run1 [0x0F,0x28,0x00] (st [(0, 0x1008)])) []}"
  IO.println s!"movups misaligned: {show1 (run1 [0x0F,0x10,0x00] (st [(0, 0x1008)])) []}"
  IO.println s!"xorps m misaligned: {show1 (run1 [0x0F,0x57,0x00] (st [(0, 0x1008)])) []}"
  IO.println s!"cmpxchg16b misaligned: {show1 (run1 [0x48,0x0F,0xC7,0x08] (st [(0, 0x1008)])) []}"
  -- XCHG eax, eax via 87 C0 zero-extends RAX; 90 does not
  IO.println s!"87C0: {show1 (run1 [0x87,0xC0] (st [(0, 0xFFFFFFFF00000001)])) [0]}"
  IO.println s!"90: {show1 (run1 [0x90] (st [(0, 0xFFFFFFFF00000001)])) [0]}"

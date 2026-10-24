import Janus
/-! M2: values of the atomics / ordered / SIMD writes the audit brief asked about, on concrete
states (`#guard` = evaluated with the compiled model). Every check here PASSES, i.e. the model
matches the ARM ARM pseudocode (cited per case). Encodings checked with aarch64-linux-gnu-objdump.
Run: lake env lean audit/round2/model/M2_values.lean   (needs Common.lean next to it: it is
inlined below to keep the file standalone). -/
open Janus.Arm64

namespace Audit2
def base : Nat := 0x10000
def mkState (regs : List (Nat × Nat)) (mem : List (Nat × Nat) := []) (dczid : BitVec 5 := 4)
    (v : List (Nat × Nat) := []) : State :=
  { regs := fun i => BitVec.ofNat 64 ((regs.lookup i).getD 0)
    sp := BitVec.ofNat 64 0x20000, pc := BitVec.ofNat 64 0x400000
    flags := ⟨false, false, false, false⟩
    mem := ⟨fun a => BitVec.ofNat 8 ((mem.lookup a).getD 0xAA), [⟨base, 0x40000, true⟩, ⟨0x80000, 0x1000, false⟩]⟩
    dczid := dczid
    vregs := fun i => BitVec.ofNat 128 ((v.lookup i).getD 0) }
def reg (r : Except Fault State) (i : Nat) : Option Nat := match r with
  | .ok s => some (s.regs i).toNat | .error _ => none
def vreg (r : Except Fault State) (i : Nat) : Option Nat := match r with
  | .ok s => some (s.vregs i).toNat | .error _ => none
def memLE (r : Except Fault State) (a n : Nat) : Option Nat := match r with
  | .ok s => some (s.mem.readLE a n) | .error _ => none

/- LDSMAXB w1, w2, [x0] (0x38214002). ASL MemAtomic: comparison on SInt of the 8-bit values;
`X[t, regsize] = ZeroExtend(data)`: the old byte 0x80 comes back ZERO-extended (0x80, not
0xffffff80), the new byte is max(-128, 127) = 0x7f, and Rs's upper bits are ignored. -/
def r1 := step 0x38214002 (mkState [(0, base), (1, 0xffffffffffffff7f), (2, 0x1234567812345678)] [(base, 0x80)])
#guard reg r1 2 = some 0x80
#guard memLE r1 base 1 = some 0x7f
/- LDSMINH w1, w2, [x0] (0x78215002): min(1, -32768) = 0x8000; old 0x0001 zero-extended. -/
def r2 := step 0x78215002 (mkState [(0, base), (1, 0x8000), (2, 0xffffffffffffffff)] [(base, 1), (base+1, 0)])
#guard reg r2 2 = some 1
#guard memLE r2 base 2 = some 0x8000
/- LDADD w1, w2, [x0] (0xb8210002): 32-bit wrap, W-register write clears X2<63:32>. -/
def r3 := step 0xb8210002 (mkState [(0, base), (1, 1), (2, 0xffffffffffffffff)]
  [(base, 0xff), (base+1, 0xff), (base+2, 0xff), (base+3, 0xff)])
#guard reg r3 2 = some 0xffffffff
#guard memLE r3 base 4 = some 0
/- STADD w1, [x0] = LDADD w1, wzr (0xb821001f): Rt = 31 discards (XZR), memory updated. -/
def r4 := step 0xb821001f (mkState [(0, base), (1, 2)] [(base, 1), (base+1, 0), (base+2, 0), (base+3, 0)])
#guard memLE r4 base 4 = some 3
/- CAS w1, w3, [x0] (0x88a17c03): compare is on the low 32 bits of X1 only (datasize 32);
X1 receives ZeroExtend(old, 32). -/
def r5 := step 0x88a17c03 (mkState [(0, base), (1, 0xdeadbeef00000005), (3, 0x11223344)]
  [(base, 5), (base+1, 0), (base+2, 0), (base+3, 0)])
#guard memLE r5 base 4 = some 0x11223344
#guard reg r5 1 = some 5
/- CASB w1, w3, [x0] (0x08a17c03): 8-bit compare. -/
def r6 := step 0x08a17c03 (mkState [(0, base), (1, 0xffffff05), (3, 0x77)] [(base, 5)])
#guard memLE r6 base 1 = some 0x77
/- LDAPR w2, [x0] (0xb8bfc002): zero-extending 32-bit load. -/
def r7 := step 0xb8bfc002 (mkState [(0, base), (2, 0xffffffffffffffff)] [(base, 0x80), (base+1, 0), (base+2, 0), (base+3, 0x80)])
#guard reg r7 2 = some 0x80000080

/- Q = 0 writes zero V[d]<127:64> (ASL `V[d, 64] = result` zero-extends): ADD v0.8b, v1.8b, v2.8b
(0x0e228420) with V0 = all ones. -/
def ones128 : Nat := 2 ^ 128 - 1
def r8 := step 0x0e228420 (mkState [] [] 4 [(0, ones128), (1, ones128), (2, 0x0101010101010101)])
#guard vreg r8 0 = some 0
/- MOVI v0.2s, #1 (0x0f000420) and FMOV d0, x1 (0x9e670020), LDR d0 (0xfd400000), UMOV/DUP Q = 0. -/
#guard vreg (step 0x0f000420 (mkState [] [] 4 [(0, ones128)])) 0 = some 0x0000000100000001
#guard vreg (step 0x9e670020 (mkState [(1, 0x1122334455667788)] [] 4 [(0, ones128)])) 0 = some 0x1122334455667788
#guard vreg (step 0xfd400000 (mkState [(0, base)] [] 4 [(0, ones128)])) 0 = some 0xAAAAAAAAAAAAAAAA
#guard vreg (step 0x0e010c20 (mkState [(1, 0x7f)] [] 4 [(0, ones128)])) 0 = some 0x7f7f7f7f7f7f7f7f  -- DUP v0.8b, w1
/- INS v0.b[0], w1 (0x4e011c20) keeps the other 15 bytes (ASL reads and writes the full 128). -/
#guard vreg (step 0x4e011c20 (mkState [(1, 0x00)] [] 4 [(0, ones128)])) 0 = some (ones128 - 0xff)
/- XTN2 v0.16b, v1.8h (0x4e212820) writes only V0<127:64> (Vpart[d, 1]); XTN (Q = 0) zeroes it. -/
#guard vreg (step 0x4e212820 (mkState [] [] 4 [(0, ones128), (1, 0)])) 0 = some (2 ^ 64 - 1)
#guard vreg (step 0x0e212820 (mkState [] [] 4 [(0, ones128), (1, 0)])) 0 = some 0
/- SMOV w0, v1.b[0] (0x0e012c20): sign-extend to 32, then the W write zero-extends to 64. -/
#guard reg (step 0x0e012c20 (mkState [(0, 0xffffffffffffffff)] [] 4 [(1, 0x80)])) 0 = some 0xffffff80
/- SMOV x0, v1.b[0] (0x4e012c20): sign-extend to 64. -/
#guard reg (step 0x4e012c20 (mkState [] [] 4 [(1, 0x80)])) 0 = some 0xffffffffffffff80
/- UMOV w0, v1.h[7] (0x0e1e3c20): lane order little-endian, element 7 = bits 127:112. -/
#guard reg (step 0x0e1e3c20 (mkState [] [] 4 [(1, 0xbeef * 2 ^ 112 + 0x1234)])) 0 = some 0xbeef
/- LD1 {v0.8h}, [x0] (0x4c407400): element order = memory order (little-endian). -/
#guard vreg (step 0x4c407400 (mkState [(0, base)] [(base, 1), (base + 15, 2)])) 0 =
  some (0x02AAAAAAAAAAAAAAAAAAAAAAAAAAAA01)
/- LD1 {v31.16b, v0.16b}, [x0] (0x4c40a01f): register numbers wrap modulo 32. -/
#guard vreg (step 0x4c40a01f (mkState [(0, base)] [(base + 16, 7)])) 0 = some (0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA07)
/- LD1 {v0.16b}, [sp] (0x4c4073e0) uses SP, X31 never. -/
#guard vreg (step 0x4c4073e0 (mkState [] [(0x20000, 9)])) 0 = some (0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA09)
/- EXT v0.8b, v1.8b, v2.8b, #7 (0x2e023820): Q = 0 concatenation is V2<63:0>:V1<63:0>. -/
#guard vreg (step 0x2e023820 (mkState [] [] 4 [(1, 0x11 * 2 ^ 56), (2, 0x2233445566778899)])) 0 =
  some 0x3344556677889911
end Audit2

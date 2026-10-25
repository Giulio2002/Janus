import Janus

/-!
# Known-answer tests of the SSE packed instructions (WP-D)

Decoding (instruction and length) and the element semantics on literals, evaluated by the
kernel. The values are the documented results (Intel SDM examples, the CRC-32C check value) and
were also observed on the oracle host.
-/

namespace JanusTests.SSE

open Janus.Amd64 Janus.Amd64.ExecSSE

-- decoding
example : decode [0x66, 0x0f, 0xfe, 0xc1] = some (.sse (.pint (.add 32) 0 (.xmm 1)), 4) := by decide
example : decode [0x66, 0x0f, 0x73, 0xd8, 0x08] = some (.sse (.pshift .srldq 128 0 8), 5) := by decide
example : decode [0x0f, 0xc6, 0xc0, 0x55] = some (.sse (.pimm .shufps 0 (.xmm 0) 0x55), 4) := by decide
example : decode [0xf2, 0x48, 0x0f, 0x38, 0xf1, 0xc1] = some (.sse (.crc32 64 0 (.reg 1)), 6) := by decide
example : decode [0x66, 0x0f, 0x3a, 0x61, 0xc1, 0x0c] =
    some (.sse (.pcmpstr true true false 0 (.xmm 1) 0x0c), 6) := by decide
example : decode [0xf3, 0x0f, 0xe6, 0xc0] = some (.sse (.cvt .dq2pd 0 (.xmm 0)), 4) := by decide
example : decode [0x66, 0x0f, 0x38, 0x2a, 0x07] = some (.sseMov true (.xmm 0) (.mem ⟨some 7, none, 0, 0, false, false⟩), 5) := by decide
-- rejected: MMX PADDD, the memory form of PSRLDQ, CMPPS with imm8 ≥ 8, MASKMOVDQU, RCPPS,
-- PCMPESTRI with imm8<7>, DPPS
example : decode [0x0f, 0xfe, 0xc1] = none := by decide
example : decode [0x66, 0x0f, 0x73, 0x18, 0x08] = none := by decide
example : decode [0x0f, 0xc2, 0xc1, 0x08] = none := by decide
example : decode [0x66, 0x0f, 0xf7, 0xc1] = none := by decide
example : decode [0x0f, 0x53, 0xc1] = none := by decide
example : decode [0x66, 0x0f, 0x3a, 0x61, 0xc1, 0x8c] = none := by decide
example : decode [0x66, 0x0f, 0x3a, 0x40, 0xc1, 0xff] = none := by decide

-- packed integer
example : pintOp (.add 32) 0xFFFFFFFF_00000003_00000002_00000001 0x00000001_00000001_00000001_00000001 =
    0x00000000_00000004_00000003_00000002 := by decide
example : pintOp (.adds 8) 0x7F 0x01 = 0x7F := by decide
example : pintOp (.subus 8) 0x01 0x02 = 0 := by decide
example : pintOp (.packus 16) 0x0000_0100_FFFF_0080 0 = 0x00FF0080 := by decide
example : pintOp (.mulh false) 0x8000 0x8000 = 0x4000 := by decide
example : pintOp .sadbw 0x0102030405060708 0x0807060504030201 = 32 := by decide
example : pintOp (.sra 16) 0x8000 20 = 0xFFFF := by decide
example : pshiftOp .srldq 128 0x1122334455667788 3 = 0x1122334455 := by decide
example : pimmOp .palignr 0xAA 0xBB_CC 1 = 0xBB + 0xAA * 2 ^ 120 := by decide

-- CRC-32C: the check value of "123456789" (init and final XOR with FFFFFFFFH) is E3069283H
example : (List.foldl (fun c b => crc32c 8 c b) 0xFFFFFFFF [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) ^^^
    0xFFFFFFFF = 0xE3069283 := by decide +kernel

-- PCMPESTRI imm8 = 0CH (unsigned bytes, equal ordered): "lo" in "hello" at index 3
example : strIndex 0x0c (intRes2 0x0c 0x6f6c 0x6f6c6c6568 2 5) = 3 := by decide
-- PCMPISTRI imm8 = 00H (equal any): the first of "ou" in "xyzzyo" is at index 5
example : strIndex 0 (intRes2 0 0x756f 0x6f797a7a7978 2 6) = 5 := by decide

end JanusTests.SSE

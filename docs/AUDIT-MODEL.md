# Janus audit — ISA model and extractor (rt-model)

This is the ISA-model and extractor red team's round, independent of the auditor/verifier
rounds ([AUDIT.md](AUDIT.md) through [AUDIT-ROUND7.md](AUDIT-ROUND7.md)) and the floating-point
round. It attacks the three things those rounds take for granted: that the Lean decoders accept
only what hardware allows, that the Lean semantics match hardware on **sequences** (not just
single steps), and that the bytes the extractor copies are the bytes that execute.

Axes:

1. **Differential fuzzing beyond the oracle's instruction classes** — flag corners (shifts by 0
   or ≥ width, ADC/SBB chains), 32-bit zero-extension, partial-register (`AH`/`BH`) writes, with
   the existing host/qemu/Sail oracle harnesses.
2. **Multi-instruction straight-line blocks** (5–20 instructions) run on the model and the
   oracle, comparing the **full** final state (registers, flags, memory, vector/FP state). This
   reaches the state-threading bugs single steps cannot.
3. **Extractor and ELF** — can a binary make Janus prove a theorem about bytes that are not what
   executes?

Rows: `audit/rt-model/run.sh` (SEQ, CORNER, EX1), `cmd/janus/rtmodel_test.go`
(`TestSegmentMismatchRejected`). The model/decoder/runner infrastructure is built on the
existing oracles (`docs/ORACLE-AMD64.md`, `docs/ORACLE.md`, `docs/ORACLE-SAIL.md`); the
sequence mode added here is a new `seq`/`words` field in the oracle case format
(`oracle-amd64/layout`, `oracle/layout`) that both the native runners and the Lean models
(`Oracle.Amd64Main`, `Oracle.Main`) understand.

## Summary

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| EX1 | **medium** | **Section vs. program-header disagreement.** The extractor copies `.text` and read-only data by **section header** (vaddr + file offset), but the kernel loads the image by **program header** (`PT_LOAD`) and ignores section headers entirely. A binary whose `.text` section header points at a different file offset than its executable `PT_LOAD` runs the real code but is read differently by Janus, and `janus check` (which re-reads the same section headers) does not catch it. A theorem would then be about bytes that do not execute. | **BROKEN → fixed** (`validateSegments`) |
| SEQ | none | Straight-line blocks of 5–20 instructions, amd64 (host) and arm64 (qemu), full final state compared. | **0 mismatch** |
| CORNER | none | ADC/SBB chains (flags defined throughout), `AH`/`BH`/16-bit partial-register writes read back wide, shifts by 0 / 1 / ≥ width / CL. | **0 mismatch** |

Only **EX1** is BROKEN. It is fixed, with a regression row and a Go test. The model and decoders
survived every sequence and corner case thrown at them.

---

## EX1 (MEDIUM, BROKEN → fixed): the extractor trusts section headers, the kernel trusts program headers

### What happens

`cmd/janus/binary.go` finds `.text` with `f.Section(".text")` and copies its bytes with
`text.Data()` — i.e. from the **section header**'s file offset and virtual address. Read-only
data (`cmd/janus/data.go`) is copied the same way, from each allocated non-writable **section**.
The ELF program loader does the opposite: it maps the file into memory using the **program
headers** (`PT_LOAD`), and never consults the section-header table at all (it is optional for a
runnable ELF). The two are independent descriptions of the same file.

So if a binary's `.text` section header says "the code at virtual address `V` is at file offset
`O₁`" while the `PT_LOAD` that maps `V` says "map file offset `O₂` there", the CPU executes the
bytes at `O₂` and Janus reads the bytes at `O₁`. The trusted byte-copy (TCB item 2 in
[SOUNDNESS.md](SOUNDNESS.md)) then copies bytes that are not the ones that run, and every
downstream guarantee is about the wrong bytes. `janus check` re-runs the same section-header
copy and compares it to `Extracted.lean`, so it confirms the mismatch rather than detecting it;
the binary's SHA-256 pins exactly the tampered file.

### Reproduction (before the fix)

`audit/rt-model/ex1_tamper.py` takes a normal `go build` executable and advances **only** the
`.text` section header's `sh_offset` by `0x40`, leaving every program header untouched:

```
$ ./b_tamper ; echo $?        # runs the real main.Add (returns x+y)
1
$ janus extract b_tamper main.Add out
   def segments := [ { name := "main.Add", base := 0x489400, bytes := [0xcc,0xcc,0xcc,0xcc] } ]
$ janus check out
   Matched: binary SHA-256, extractor version, Extracted.lean SHA-256, regenerated words and data.
```

The function that executes is `48 01 d8 c3` (`ADD RAX,RBX ; RET`, returns `x+y`); Janus extracts
`0xCC 0xCC 0xCC 0xCC` (`INT3` padding). With a different shift the extracted bytes decode to a
different *valid* instruction, so the divergence runs both ways: a `Returns` theorem that is
true of the extracted bytes can be **false** of the bytes that execute. `janus check` passes in
every case.

### Why the earlier rounds miss it

[AUDIT.md](AUDIT.md) §4 reviewed the extractor and concluded the copy is faithful, but only
considered *section-internal* issues (overlapping symbols, trailing-zero padding, PIE
relocations) and took the section→file→vaddr mapping itself as ground truth. [AUDIT-ROUND7.md]
(AUDIT-ROUND7.md) G2 notes that entry/module names are "binary-carried labels" and that the
binary is the subject, not the adversary — but a section header that lies about *where the code
is* is not a label: it changes which bytes the trusted copy reads, and the loader's answer
(the program header) is authoritative and available in the same file. Nothing cross-checked the
two.

### Fix (applied)

`cmd/janus/binary.go`, `validateSegments`, called at the start of `loadBinary` (before any byte
is copied). For every allocated, file-backed section (`SHF_ALLOC`, not `SHT_NOBITS`, non-empty —
the sections the extractor ever reads: `.text`, `.rodata`, literal pools, `.gopclntab`, …) it
requires a `PT_LOAD` segment that covers the section with a **single consistent delta**:

```
p.Off   ≤ s.Offset  ∧  s.Offset + s.Size ≤ p.Off  + p.Filesz
p.Vaddr ≤ s.Addr    ∧  s.Addr   + s.Size ≤ p.Vaddr + p.Filesz
s.Offset − p.Off  =  s.Addr − p.Vaddr
```

(using `Filesz`, since only file bytes are read), and that the segment holding `.text` is
executable (`PF_X`). This makes the byte Janus reads at any virtual address equal to the byte
the kernel maps there. A disagreement — which a normal `go build` never produces — is rejected
with a `binary validation` diagnostic. The tampered binary above is now rejected; every normal
binary (internal link, `-linkmode=external` + cgo, stripped `-s -w`, `-trimpath`, `-race`, and
the `examples-amd64`/`examples-arm64` binaries) still loads and extracts. PIE (`ET_DYN`) is
still rejected earlier, as before.

### Residual

`validateSegments` accepts a section as long as *some* `PT_LOAD` maps it consistently. A
pathological binary with **overlapping** `PT_LOAD` segments that map the same virtual address to
two different file offsets could, in principle, satisfy the check on the first segment while the
kernel keeps the last mapping. The Go toolchain never emits overlapping `PT_LOAD`s, and this is
squarely in the "binary as adversary" region the threat model excludes; it is noted here rather
than handled. The check does close the realistic gap (a corrupted or hand-edited section header,
or an unusual external linker layout) and strictly strengthens the trusted copy.

---

## SEQ (axis 2): multi-instruction straight-line blocks

Single-step oracles (`docs/ORACLE-AMD64.md`, `docs/ORACLE.md`) prove each instruction in
isolation; they cannot catch a bug that only shows up when one instruction's output is another's
input — a flag written then read, a 32-bit write whose zero-extension a later instruction reads,
a partial-register merge a wide read observes, memory written then reloaded. Sequence mode runs a
random straight-line block (5–20 instructions) on the model and the oracle **from one shared
initial state** and compares the **entire** final state, memory and vector/FP registers included.

The oracle case format gained a `seq` (amd64, instruction byte strings laid contiguously at
`TestPC`) / `words` (arm64, words laid contiguously, falling through to the trailing `UDF`/`INT3`
so the captured state is the state after the whole block) field. The native runners single-step
through the block; the Lean models (`Oracle.Amd64Main.runSeq`, `Oracle.Main.runSeq`) thread their
own `State` through it. Generators and comparators are in `audit/rt-model/`.

The generators draw from the register/immediate and short memory forms of the accepted subset
(no control transfer, no RIP-relative, so a block is position-independent): on amd64 the full
integer ALU/`MOV`/`LEA`/shift/`SHLD`/`SHRD`/`RCL`/`RCR`/`IMUL`/`DIV`/`CMOV`/`SETcc`/`BT*`/bit-scan/
`BSWAP`/`XCHG`/`CBW`/`MOVZX`/`MOVSX` set plus 8/16-bit (`AH`/`BH`, `SPL`-family) partial forms; on
arm64 add/sub (imm/shifted/extended/carry), logical, move-wide, bitfield, `EXTR`, cond-sel/cond-cmp,
data-processing 1/2/3-source, buffer loads/stores, and an FP/SIMD variant (`FADD`…`FDIV`, `FABS`,
`FNEG`, `FCMP`, `FMOV` gen↔reg, vector three-same) that threads `FPSR` cumulative flags and the `V`
registers across steps.

Results (host Xeon for amd64, qemu-aarch64 `-cpu max` for arm64):

| batch | cases | agree | model-gap | MISMATCH |
|---|---:|---:|---:|---:|
| amd64 random blocks (3 seeds × 40k) | 120,000 | 91,444 | 28,556 | **0** |
| arm64 random blocks (seed 2, 40k) | 40,000 | 39,868 | 132 | **0** |
| arm64 FP/SIMD blocks (seed 3, 25k) | 25,000 | 18,079 | 6,921 | **0** |

Model-gaps are a later instruction reading a flag an earlier one left undefined (`CMOV`/`SETcc`/
`ADC` after `MUL`/`DIV`/a multi-bit shift → the model's `undefinedFlag` fault), a mid-block memory
access outside the buffer, or an undecoded (arm64 FP) neighbour — all conservative, never a wrong
value. Mid-block hardware faults are recovered as faults by the comparator (the arm64 runner
reports an escape with the faulting `pc` inside the block), so a model-success where hardware
faults cannot hide as "unobserved".

## CORNER (axis 1): the flag and partial-register corners, in chains

Three generators target the corners the task called out, as multi-instruction blocks so the
result of each corner is observed by the next instruction:

* **ADC/SBB chains** — `CLC`/`STC` to define `CF`, then a run of `ADC`/`SBB`/`ADD`/`SUB`/`NEG`/`MOV`
  keeping `CF` defined throughout (multi-precision arithmetic): **30,000 cases, 100% agree, 0 gap**.
* **Partial-register writes** — 8-bit `AH`/`CH`/`DH`/`BH` (no REX) and `SPL`-family (REX) and 16-bit
  (`66`) writes interleaved with 64-bit reads and `MOVZX`/`MOVSX` of the high-byte registers:
  **30,000 cases, 100% agree**.
* **Shifts by 0 / 1 / ≥ width / CL** — `SHL`/`SHR`/`SAR`/`ROL`/`ROR`/`SHLD`/`SHRD` with counts
  `0,1,8,16,31,32,63` and `CL` set to those values, exercising the masked-count-0 write
  (zero-extension), the undefined-`OF`/`CF`-at-0 rules and the 16-bit `SHLD`/`SHRD` undefined
  result: **30,000 cases, 100% agree**.

The count-0-still-writes bug the amd64 oracle originally found (`docs/ORACLE-AMD64.md`) is exactly
the kind of thing these chains stress; the current model handles it, and the chains confirm the
flag definedness tracking is consistent across steps.

## Probes with no issue

* **amd64 decoder over-acceptance.** The `rand`/`gen` oracle classes already fuzz random prefix /
  opcode / ModRM strings with 0 mismatch; the sequence and corner runs add 180k more accepted
  encodings with 0 mismatch. The strict prefix policy (REX placement, `LOCK` only on lockable
  memory forms, `66`/`F2`/`F3` handling, VEX reserved-field checks) was re-read against the SDM
  and the oracle results; no over-accepted encoding was found.
* **arm64 decoder.** Writeback with `Rn == Rt`, load-pair `Rt == Rt2`, store-exclusives, exclusive
  pairs (`LDXP`/`STXP`), odd-register `CASP`, `CCMP` `NZCV` immediate mapping and the bitfield
  aliases are all rejected or handled as the ARM ARM prescribes (`Janus/Arm64/Decode.lean`, and
  the 48 reserved-encoding facts of `audit/round2/model`). The sequence runs add 65k accepted
  blocks with 0 mismatch against both qemu and (via the same corpus) the semantics the Sail
  oracle validates.
* **Extractor, other ELF shapes.** PIE (`ET_DYN`) is rejected (E1/F6). Stripped (`-s -w`, pclntab
  path), `-trimpath`, `-race`, and `-linkmode=external` (cgo) binaries all extract the correct
  bytes (the pclntab path includes the function's `INT3` padding, which the model rejects, so it
  never executes as anything). A function jumped into mid-body is still copied whole by symbol
  range; a branch to an un-extracted address is `noCode`, a fault. None of these makes a false
  theorem provable; the only soundness-relevant ELF issue was EX1.

## Regression status

`audit/rt-model/run.sh` (SEQ, CORNER, EX1) passes. `cmd/janus/rtmodel_test.go`
(`TestSegmentMismatchRejected`) passes. The full suite — `scripts/verify-all-examples.sh`,
`audit/run-all.sh`, `audit/round2`–`round7`, `go test ./cmd/...`, and the amd64/arm64 oracles —
is run one job at a time before reporting.

## Reproduce

```
audit/rt-model/run.sh                       # quick (N=5000 per batch)
N=40000 AN=40000 CN=30000 SEEDS="1 2 3" audit/rt-model/run.sh   # full sweep
go test ./cmd/janus/ -run TestSegmentMismatchRejected
```

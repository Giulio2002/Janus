# Third oracle: the Sail x86 model (from ACL2 X86isa)

A cross-check of the Janus amd64 model (`Janus.Amd64.step`) against an independent formal
x86-64 semantics. The main question was which status flags each instruction leaves
**undefined**. The native oracle cannot answer that, because hardware only shows one
vendor's concrete values.

## What was used

The model is [rems-project/sail-x86-from-acl2](https://github.com/rems-project/sail-x86-from-acl2)
at commit `0c6c023` (Nov 2024). It is a Sail translation of the ACL2 X86isa model of
Goel, Hunt and Kaufmann, built with Sail 0.20.3 from opam into a C emulator. ACL2 X86isa
itself, Remill and the K semantics were not tried. This one ran on the first attempt, and
it has what this check needs:

* **Explicit undefined-flag masks.** Every flag-setting spec function returns
  `(result, flags, undefined_flags)`, and `write_user_rflags` draws each undefined flag from
  `undef_read()`. The patch in `build.sh` makes that source a config register, so
  `compare.py` runs every case twice (undefined values 0, then 1). A flag that differs
  between the two runs is undefined in the formal model. A result register that differs
  would be an undefined result; this never happened.
* **Single-step execution from a set state.** The patched `main` executes one instruction.
  `compare.py` sets the 16 GPRs, RFLAGS and RIP with `-C`, loads the code page and the data
  buffer with `-b`, and reads back registers, flags, RIP and the logged memory writes.
* **Application-level memory view** (`app_view=1`). All canonical memory exists, so the
  formal model never faults on unmapped addresses. Only cases where our model succeeds
  are compared.

## How to run

```
oracle-amd64-formal/build.sh WORKDIR    # m4 + GMP + private opam root + Sail 0.20.3 + model; ~10 min cold, ~1 min warm
python3 -I oracle-amd64-formal/compare.py WORKDIR/model-janus/x86_emulator artifacts/oracle-amd64 OUT.json --sample 20000 --jobs 20
```

Notes on the build:

* The host has neither GMP headers nor m4, and GCC 15 needs `-std=gnu17` for GMP 6.3.
  `build.sh` builds both in user space.
* The Sail C runtime parses `-C` values with `strtoll`, so `compare.py` passes register
  values of 2^63 and above as negative numbers.
* XMM state cannot be set through `-C`, so SSE classes are excluded.

## Sample

The run used 20,000 cases drawn from `artifacts/oracle-amd64` (seed 1). They are
stratified over the integer `gen/*`, `edge/*` and `harvest/*` classes, and every one is a
case our model executes successfully. It takes about 18 s with 20 jobs.

| | cases |
|---|---:|
| sampled | 20,000 |
| the formal model faults or does not implement the opcode | 2,313 |
| both models succeed | 17,687 |
| identical on every field both define (GPRs, RIP, defined flags, buffer bytes) | 17,538 |
| results differ | 149 |

## Final run (after the fixes below)

After the first run the Janus model was made stricter in the two places finding 2 lists:
SAR CF with an over-wide count, and ROL/ROR OF at masked count 0 are now undefined. The
oracle cases were then regenerated. Rerun with the same command (20,000 sampled cases):

| | cases |
|---|---:|
| the formal model faults or does not implement the opcode | 2,314 |
| both models succeed | 17,686 |
| identical on every field both define | 17,356 |
| **undefined in the formal model, defined in ours** | **0** |
| undefined in ours, defined in the formal model (BT ZF, deliberate) | 336 |
| results differ (every one is a case where ours equals the hardware) | 330 |

The 330 result differences are the same formal-model bugs as finding 4: `AL, imm8` with
REX.W (e.g. `4b 2c 16` `rex.WXB sub $0x16,%al`, 187 SUB cases plus the other ALU ops),
over-wide 8/16-bit rotates, and XMM-sourced RIP-relative stores the driver cannot
initialise. The native oracle classifies every one of these cases as `agree`.

## Findings of the first run

**1. Unimplemented in the formal model.**

* It has no translation for BSF/BSR/TZCNT/LZCNT (`0F BC`/`0F BD`), POPCNT, BSWAP or
  BTS/BTR/BTC. Those classes were not cross-checked; they are covered by the native oracle
  only.
* It also rejects INT3, which is correct. Every other sampled class ran.

**2. Flag definedness: undefined in the formal model, defined in ours (71 cases).**
Hardware agrees with our model in every one of them.

* **ROL/ROR OF with a masked count of 0** (32 cases).
  * Our model leaves every flag unchanged, so OF keeps its previous, defined value.
  * The formal model follows the SDM pseudocode line "IF (COUNT & COUNTMASK) = 1 THEN OF ←
    … ELSE OF is undefined", which also covers count 0.
  * The SDM prose ("If the masked count is 0, the flags are not affected") and the AMD
    manual both say unchanged, as does hardware.
  * This is a pseudocode artefact. Keeping OF defined is safe.
* **SAR CF when the masked count is at least the operand width (8/16-bit only)** (39 cases).
  * Our model sets CF to the sign bit. The formal model makes CF undefined.
  * The SDM's "CF undefined if count ≥ size" sentence names only SHL and SHR. Intel
    hardware gives the sign bit, as our model does.
  * This is the one place our model relies on a value that a formal model treats as
    undefined. The value is unconfirmed on AMD.
  * The strict fix is to make CF undefined (`none`) for SAR when `c ≥ w`. It costs nothing
    for Go code, which never shifts an 8/16-bit value by its width or more.

**3. Flag definedness: undefined in ours, defined in the formal model.**

* **BT ZF** (168 cases): the formal model leaves ZF unaffected, as the Intel SDM does. Ours
  is undefined on purpose, because AMD documents ZF as undefined. This is conservative.

**4. Result differences (149 cases).**

* In every case our model equals the hardware. The native oracle has 0 MISMATCH on these
  same cases, so each difference is the formal model disagreeing with the CPU:
  * ROL/ROR, 78 cases: wrong result, CF or OF. The inspected examples are 8-bit rotates
    with counts at or above the width.
  * ADD/ADC/SUB/SBB/AND/OR/XOR/CMP/TEST flags, 63 cases. The inspected examples (`4b 04 ea`,
    `3e 4b 14 37`, `4c a8 cb`, `4b 3c 7e`) are all `AL, imm8` forms with REX.W, and the
    formal model gets SF or CF wrong. It looks like REX.W is not ignored for byte operands.
  * 8 `edge/riprel` stores of XMM registers, which the driver cannot initialise (a driver
    limitation).
* No result is undefined in the formal model while our model produces a value.

## Conclusion

The formal model is usable as a third oracle for undefined flags and results on the
integer subset it implements. It found no case where our model defines a flag or result
that is undefined in both the SDM and the formal model, except SAR CF with an over-wide
count (finding 2). The native single-step oracle remains the reference for concrete values;
the formal model has its own bugs (finding 4).

## Atomics and string instructions

`compare.py --classes REGEX` restricts the run to case classes matching `REGEX`. `REP` string
instructions are run to completion: the formal model executes one iteration per step and
leaves `RIP` at the instruction, so the driver feeds registers, flags and the buffer back
(at most `RCX + 2` steps). On the `SEED=1` cases of the new classes that our model executes:

* `LOCK`-prefixed `ADD ADC SUB SBB AND OR XOR INC DEC NEG NOT XCHG`: 19,906 cases, all identical.
* `MOVS`/`STOS` without `REP`: 2,238 cases, all identical.
* `CMPXCHG`: 3,338 cases; registers, memory and `RIP` identical in all, flags differ in 2,592
  because the formal model computes them from `DEST - accumulator` instead of
  `accumulator - DEST` (the hardware sides with ours).
* `REP MOVS`/`REP STOS`: not comparable. The formal model does one iteration before testing
  the count (`RCX = 0` copies an element and wraps `RCX`), and ends an `F3` repetition on `ZF`
  as if it were `REPE`.
* `XADD`, `LOCK BTS/BTR/BTC`, `CMPXCHG8B/16B` and the fences are not implemented by the formal
  model.

No case has a flag the formal model leaves undefined and ours defines.

## FS, YMM and the vector/scalar-move classes

`build.sh` also patches the driver so that `-C fsbase=V` sets the FS base (`IA32_FS_BASE`,
`msrs[1]`, which 64-bit-mode FS addressing uses, and `seg_hidden_bases[4]`), `-C ymm{i}q{j}=V`
sets quadword `j` of `zmms[i]` (`i < 16`, `j < 4`), and `printState` prints `ymm0`..`ymm15`
(bits 255:0). `compare.py` passes each case's `fsbase`, `xmm` and `ymmh`, compares the YMM
registers too, no longer excludes the SSE classes, and `--fs 1` keeps only `64`-prefixed cases:

```
python3 -I oracle-amd64-formal/compare.py WORKDIR/model-janus/x86_emulator OUT_DIR fs.json --sample 1000000 --jobs 20 --fs 1
python3 -I oracle-amd64-formal/compare.py WORKDIR/model-janus/x86_emulator OUT_DIR new.json --sample 1000000 --jobs 20 \
  --classes '^(gen/(rcl|rcr|movss|movsd_xmm|movups|movaps|movupd|movapd|movdqu|movdqa|movq|movd|pxor|xorps|xorpd|pcmpeqb|pand|por|pmovmskb|pshufd|pshuflw|punpcklbw|prefetch.*|cld|v.*)|edge/(tls|sse-memmove|sse-align|vec-cmp|vec-align)|harvest/(rcr|movss|movsd_xmm|movups|movdqu|movq|movd|cld|v.*|p.*))$'
```

Results on the final `SEED=1` run are in `docs/ORACLE-AMD64.md` ("FS, YMM and the new
instructions"): every FS-relative case identical, 0 flags undefined there but defined by us,
and every result difference a formal-model bug in `MOVD/MOVQ xmm, r/m` (it does not
zero-extend to 128 bits). The formal model implements no VEX instruction and none of the
packed-integer ones. Cases with `DF = 1` are run with `DF = 0` there (the driver sets only the
status flags), so the string classes are not part of this comparison.

Round-2 audit, attack surface "arm64 instruction model" (Decode/Exec/State/Instr/Bits, and
Vector.lean on agent/arm64cov2 accb078). Written 2026-10-23.

Summary: no wrong value for a valid instruction and no accepted reserved/UNDEFINED encoding
was found. What remains are modelling assumptions that qemu -cpu max / Sail cannot see
(optional features accepted unconditionally, DCZID_EL0 uniform across CPUs, reserved
DCZID.BS values), and none of them affects a shipped example theorem. Details: M0-M3 headers.

How to run (never inside /srv/...; use a copy):
  cp -a /srv/janus-arm64cov2 $SCRATCH/a64 && cd $SCRATCH/a64
  mkdir -p audit/round2 && cp -a /srv/janus-rt2/audit/round2/model audit/round2/
  lake build Janus janus-decode
  lake env lean audit/round2/model/M0_feature_scan.lean    # features used by every shipped example
  lake env lean audit/round2/model/M1_decode_reserved.lean # 48 kernel-checked decode facts
  lake env lean audit/round2/model/M2_values.lean          # 27 #guard value checks (atomics, SIMD)
  lake env lean audit/round2/model/M3_assumptions.lean     # DC ZVA BS 10..15, DZP, features, conservative faults
  audit/round2/model/sweep_vs_objdump.sh 1500000 11        # decoder vs GNU objdump, new classes
  audit/round2/model/feat_qemu.sh                          # qemu cortex-a53/a72/neoverse-n1/max
A file that compiles without errors means every check in it holds. M1-M3 need the
arm64cov2 tree (SIMD decoder); on agent/redteam2 only the non-SIMD lines of M1/M3 apply.

Files:
  M0_feature_scan.lean   decodes all 678 words of artifacts/*/Extracted.lean (embedded) and lists
                         instructions needing LSE/LRCPC/AES/AdvSIMD, DC ZVA, MRS. Result: LSE only
                         in AtomicAdd (+12 LDADDAL) and AtomicMax (+28 CASAL), both behind the
                         arm64HasATOMICS test that their precondition fixes; no LRCPC, no AES;
                         AdvSIMD (unguarded, as Go requires) in A64Equal64/A64IndexByte;
                         DC ZVA/MRS DCZID in ClearWords (memclrNoHeapPointers).
  M1_decode_reserved.lean reserved neighbours of every class added (LDAR/LDAPR SBO fields, LDLAR,
                         CASP odd regs and Rt2, AES size, size:Q=110, EXT imm4<3>, DUP/UMOV/SMOV/
                         INS imm5 and Q, MOVI op=1 cmode=1111 Q=0, FP16 FMOV, immh<3> with Q=0,
                         SHRN/SSHLL immh<3>, ADDV .2S, LD1 single/replicate S/size, ST1R, LDR
                         scale>4, LDP Rt==Rt2, LDR literal opc=11, MSR TPIDR_EL0, DC CIVAC).
  M2_values.lean         LDSMAXB/LDSMINH zero-extension and signed compare, W-register
                         zero-extension, ST<op> alias, CAS/CASB compare width, LDAPR, Q=0 upper
                         zeroing (ADD/MOVI/FMOV/LDR D/DUP/XTN), INS and XTN2 keep the rest, SMOV
                         W/X, UMOV lane order, LD1 order and register wrap, SP as base, EXT Q=0.
  M3_assumptions.lean    A1 reserved BS 10..15 (128 KiB DC ZVA), A2 DCZID constant per run,
                         A3 features accepted unconditionally, A4 conservative faults.
  feat.S, feat_qemu.sh   real-CPU-model evidence for A3/A4 and the IMPLEMENTATION DEFINED DCZID.
  sweep_*.py, sweep_vs_objdump.sh  random words in the new classes: 0 accepted-but-invalid.

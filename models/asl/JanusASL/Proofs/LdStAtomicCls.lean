import JanusASL.Proofs.LdStAtomic
import JanusASL.Proofs.LdStDecodeA

/-! # Proved: the LSE atomics LD<op>{A}{L}{B,H} and SWP{A}{L}{B,H} (all sizes, acquire/release forms) -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_dec_at_ldadd_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldaddb_aarch64_instrs_memory_atomicops_ld Rt Rn 0#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ADD 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaddb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldadd_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldaddh_aarch64_instrs_memory_atomicops_ld Rt Rn 0#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ADD 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaddh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldadd_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn 0#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ADD 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldadd_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldadd_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn 0#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ADD 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldadd_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldclr_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldclrb_aarch64_instrs_memory_atomicops_ld Rt Rn 1#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_BIC 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldclrb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldclr_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldclrh_aarch64_instrs_memory_atomicops_ld Rt Rn 1#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_BIC 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldclrh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldclr_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn 1#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_BIC 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldclr_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldclr_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn 1#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_BIC 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldclr_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldeor_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldeorb_aarch64_instrs_memory_atomicops_ld Rt Rn 2#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_EOR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldeorb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldeor_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldeorh_aarch64_instrs_memory_atomicops_ld Rt Rn 2#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_EOR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldeorh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldeor_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn 2#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_EOR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldeor_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldeor_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn 2#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_EOR 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldeor_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldset_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsetb_aarch64_instrs_memory_atomicops_ld Rt Rn 3#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ORR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsetb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldset_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldseth_aarch64_instrs_memory_atomicops_ld Rt Rn 3#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ORR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldseth_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldset_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn 3#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ORR 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldset_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldset_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn 3#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_ORR 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldset_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmax_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld Rt Rn 4#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmax_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld Rt Rn 4#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmax_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn 4#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmax_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmax_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn 4#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMAX 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmax_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmin_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsminb_aarch64_instrs_memory_atomicops_ld Rt Rn 5#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsminb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmin_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsminh_aarch64_instrs_memory_atomicops_ld Rt Rn 5#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsminh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmin_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn 5#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmin_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldsmin_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn 5#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_SMIN 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldsmin_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumax_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumaxb_aarch64_instrs_memory_atomicops_ld Rt Rn 6#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumaxb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumax_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumaxh_aarch64_instrs_memory_atomicops_ld Rt Rn 6#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumaxh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumax_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn 6#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMAX 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumax_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumax_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn 6#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMAX 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumax_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumin_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_lduminb_aarch64_instrs_memory_atomicops_ld Rt Rn 7#3 Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 8 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_lduminb_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumin_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn 7#3 Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 16 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_lduminh_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumin_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn 7#3 Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 32 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMIN 32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumin_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_ldumin_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn 7#3 Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_ld (A == 1#1 && Rt != 31#5) 64 (Rt != 31#5) Rn.toNat
        .MemAtomicOp_UMIN 64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldumin_aarch64_instrs_memory_atomicops_ld
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_swp_0 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_swpb_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A 0#2).run st =
      (execute_aarch64_instrs_memory_atomicops_swp (A == 1#1 && Rt != 31#5) 8 Rn.toNat
        32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_swpb_aarch64_instrs_memory_atomicops_swp
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_swp_1 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_swph_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A 1#2).run st =
      (execute_aarch64_instrs_memory_atomicops_swp (A == 1#1 && Rt != 31#5) 16 Rn.toNat
        32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_swph_aarch64_instrs_memory_atomicops_swp
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_swp_2 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A 2#2).run st =
      (execute_aarch64_instrs_memory_atomicops_swp (A == 1#1 && Rt != 31#5) 32 Rn.toNat
        32 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_swp_aarch64_instrs_memory_atomicops_swp
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

theorem run_dec_at_swp_3 (Rt Rn Rs : BitVec 5) (R A : BitVec 1) {st : SState} (hc : LinuxEL0Config st) :
    (decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A 3#2).run st =
      (execute_aarch64_instrs_memory_atomicops_swp (A == 1#1 && Rt != 31#5) 64 Rn.toNat
        64 (R == 1#1) Rs.toNat Rt.toNat (Rn.toNat != 31)).run st := by
  unfold decode_swp_aarch64_instrs_memory_atomicops_swp
  cfg_simp [HaveAtomicExt, run_IsFeatureImplemented hc, cfgFeat, undefined_MemAtomicOp]
  all_goals rfl

open Janus.Arm64 in
theorem decode_atomicLd {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) :
    decode w = some (.atomic (bits w 31 30) (bit w 23) (bit w 22) (bits w 20 16) (AtomicOp.ofBits (bits w 14 12))
      (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bit w 21 = true := by simp only [bit_def]; simp; omega
  have e7 : bits w 11 10 = 0 := by simp only [bits_def]; omega
  have e8 : bit w 15 = false := by simp only [bit_def]; simp; omega
  have e14 : bits w 11 10 ≠ 2 := by omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, e14, Bool.false_eq_true, ite_false, ite_true,
    Bool.not_false, Bool.not_true, decodeAtomic, e8]
  simp

open Janus.Arm64 in
theorem decode_swp {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 1) (h12 : (w / 2 ^ 12) % 8 = 0) :
    decode w = some (.atomic (bits w 31 30) (bit w 23) (bit w 22) (bits w 20 16) .swp (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bit w 21 = true := by simp only [bit_def]; simp; omega
  have e7 : bits w 11 10 = 0 := by simp only [bits_def]; omega
  have e8 : bit w 15 = true := by simp only [bit_def]; simp; omega
  have e9 : bits w 14 12 = 0 := by simp only [bits_def]; omega
  have e14 : bits w 11 10 ≠ 2 := by omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, e14, Bool.false_eq_true, ite_false, ite_true,
    Bool.not_false, Bool.not_true, decodeAtomic, e8, e9]
  simp

set_option maxHeartbeats 16000000 in
/-- **LDADD{A}{L}{B,H}** (and the STADD aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 000 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldadd_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 0 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 526
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 526) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 526) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 527
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 527) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 527) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 526
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 526) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 526) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 527
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 527) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 527) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 526
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 526) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 526) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 527
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 527) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 527) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 526
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 526) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 526) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 527
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 527) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 527) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 525
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ADD 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 525) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_00_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 0#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldadd_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 525) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDCLR{A}{L}{B,H}** (and the STCLR aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 001 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldclr_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 1)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 1 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 529
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 529) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 529) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 530
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 530) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 530) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 529
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 529) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 529) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 530
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 530) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 530) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 529
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 529) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 529) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 530
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 530) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 530) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 529
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 529) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 529) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 530
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 530) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 530) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 528
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_BIC 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 528) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_01_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 1#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldclr_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 528) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDEOR{A}{L}{B,H}** (and the STEOR aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 010 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldeor_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 2)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 2 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 532
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 532) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 532) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 533
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 533) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 533) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 532
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 532) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 532) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 533
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 533) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 533) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 532
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 532) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 532) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 533
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 533) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 533) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 532
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 532) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 532) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 533
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 533) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 533) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 531
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_EOR 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 531) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_02_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 2#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldeor_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 531) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDSET{A}{L}{B,H}** (and the STSET aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 011 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldset_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 3)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 3 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 535
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 535) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 535) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 536
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 536) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 536) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 535
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 535) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 535) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 536
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 536) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 536) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 535
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 535) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 535) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 536
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 536) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 536) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 535
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 535) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 535) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 536
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 536) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 536) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 534
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_ORR 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 534) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_03_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 3#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldset_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 534) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDSMAX{A}{L}{B,H}** (and the STSMAX aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 100 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldsmax_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 4)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 4 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 538
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 538) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 538) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 539
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 539) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 539) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 538
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 538) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 538) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 539
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 539) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 539) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 538
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 538) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 538) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 539
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 539) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 539) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 538
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 538) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 538) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 539
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 539) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 539) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 537
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMAX 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 537) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_04_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 4#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 537) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDSMIN{A}{L}{B,H}** (and the STSMIN aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 101 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldsmin_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 5)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 5 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 541
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 541) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 541) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 542
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 542) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 542) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 541
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 541) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 541) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 542
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 542) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 542) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 541
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 541) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 541) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 542
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 542) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 542) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 541
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 541) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 541) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 542
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 542) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 542) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 540
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_SMIN 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 540) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_05_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 5#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldsmin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 540) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDUMAX{A}{L}{B,H}** (and the STUMAX aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 110 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldumax_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 6)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 6 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 544
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 544) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 544) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 545
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 545) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 545) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 544
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 544) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 544) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 545
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 545) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 545) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 544
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 544) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 544) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 545
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 545) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 545) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 544
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 544) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 544) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 545
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 545) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 545) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 543
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMAX 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 543) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_06_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 6#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumax_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 543) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **LDUMIN{A}{L}{B,H}** (and the STUMIN aliases, `Rt = 11111`): for every word
`size 111 0 00 A R 1 Rs 0 111 00 Rn Rt` and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word (an aligned read-modify-write) the generated ASL step
completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldumin_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) (h12 : (w / 2 ^ 12) % 8 = 7)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_atomicLd hw h0 h1 h2 h21 h10 h15)] at hj
  simp only [Janus.Arm64.exec] at hj
  rw [show Janus.Arm64.bits w 14 12 = 7 by simp only [bits_def]; omega] at hj
  simp only [Janus.Arm64.AtomicOp.ofBits] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 547
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 547) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 547) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 548
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 548) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 548) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 547
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 547) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 547) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 548
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 548) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 548) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (0#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 547
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 547) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 547) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 548
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 548) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 548) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 547
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 8 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 547) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 547) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 548
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 16 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 548) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 548) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 32 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 546
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_atomic64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (fld w 0 5 != 31#5) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_ld (1#1 == 1#1 && fld w 0 5 != 31#5) 64 (fld w 0 5 != 31#5)
          (Janus.Arm64.bits w 9 5) .MemAtomicOp_UMIN 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 546) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_07_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 12 3 = 7#3 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 12 3 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_ldumin_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 546) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- **SWP{A}{L}{B,H}**: for every word `size 111 0 00 A R 1 Rs 1 000 00 Rn Rt` and every related
pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the word (an aligned
swap) the generated ASL step completes in a related state, with Janus' memory related to the ASL's. -/
theorem swp_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 1) (h12 : (w / 2 ^ 12) % 8 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_swp hw h0 h1 h2 h21 h10 h15 h12)] at hj
  simp only [Janus.Arm64.exec] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrs : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hs32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with ha | ha <;>
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hr | hr <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- A 0, R 0, size 0
    have hF := entry_facts h hm hc w 1001
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 8
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1001) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_00_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1001) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 1
    have hF := entry_facts h hm hc w 1002
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 16
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1002) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_00_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1002) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 2
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 32
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_00_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 0, size 3
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 64
          (Janus.Arm64.bits w 9 5) 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_00_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 0
    have hF := entry_facts h hm hc w 1001
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 8
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1001) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_01_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1001) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 1
    have hF := entry_facts h hm hc w 1002
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 16
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1002) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_01_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1002) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 2
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 32
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_01_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 0, R 1, size 3
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (0#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (0#1 == 1#1 && fld w 0 5 != 31#5) 64
          (Janus.Arm64.bits w 9 5) 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_01_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 0
    have hF := entry_facts h hm hc w 1001
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 8
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1001) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_10_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1001) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 1
    have hF := entry_facts h hm hc w 1002
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 16
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1002) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_10_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1002) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 2
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 32
          (Janus.Arm64.bits w 9 5) 32 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_10_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 0, size 3
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (0#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 64
          (Janus.Arm64.bits w 9 5) 64 (0#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_10_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 0
    have hF := entry_facts h hm hc w 1001
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp8 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 8
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1001) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_11_0 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_0 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1001) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 1
    have hF := entry_facts h hm hc w 1002
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp16 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 16
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1002) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_11_1 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_1 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1002) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 2
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp32 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 32
          (Janus.Arm64.bits w 9 5) 32 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_11_2 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_2 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- A 1, R 1, size 3
    have hF := entry_facts h hm hc w 1000
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_swp64 hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2 hn32 ht32 hs32
      (1#1 == 1#1 && fld w 0 5 != 31#5) (1#1 == 1#1) (Janus.Arm64.bits w 9 5 != 31) hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_atomicops_swp (1#1 == 1#1 && fld w 0 5 != 31#5) 64
          (Janus.Arm64.bits w 9 5) 64 (1#1 == 1#1) (Janus.Arm64.bits w 20 16) (Janus.Arm64.bits w 4 0)
          (Janus.Arm64.bits w 9 5 != 31)).run (entrySt s w 1000) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_at_10_11_3 hw h0 h1 h2 h21 h10 h15 (by omega) ha hr e
        (see_entry s _),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 23 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 23 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact (run_dec_at_swp_3 _ _ _ _ _ hF.2.2.1).trans (by rw [hrn, hrt, hrs])
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 1000) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

end JanusASL.Proofs

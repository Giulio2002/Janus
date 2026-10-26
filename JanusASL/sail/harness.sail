/* =============================================================================
 * harness.sail: the Janus entry points into the sliced sail-arm model (docs/ASL.md).
 *
 * Appended after the sliced sail-arm sources. Everything here is a thin wrapper:
 * the instruction semantics, decode, the EL0 checks (SP alignment, alignment,
 * translation with page tables in memory) are all sail-arm's (Arm's ASL).
 *
 * The only replaced function is AArch64_TakeException (see janus_splice.sail):
 * exception *entry* (vector, ESR/FAR/ELR/SPSR writes, PSTATE changes) is not
 * executed; instead the exception record Arm's pseudocode built is stored in
 * the __janus_exc_* registers below and Error_ExceptionTaken is thrown, which
 * is what the real function ends with.
 * ===========================================================================*/

/* The __janus_exc_* registers are declared in janus_regs.sail (before v8_base's users). */

/* Outcome of janus_step, read back by the Lean driver. */
enum JanusOutcome = {
  Janus_OK,            /* the instruction completed; registers/PC/memory hold the result   */
  Janus_Exception,     /* a synchronous exception was taken (__janus_exc_* hold the record) */
  Janus_Undefined,     /* decode/execute threw Error_Undefined (UNDEFINED)                  */
  Janus_Unpredictable, /* Error_Unpredictable / Error_ConstrainedUnpredictable              */
  Janus_See,           /* Error_See escaped the single retry                                */
  Janus_ImpDef,        /* Error_ImplementationDefined (includes "janus-excluded ..." stubs)  */
  Janus_Other          /* Error_ReservedEncoding / Error_SError                             */
}

register __janus_impdef : string

/* Linux EL0 configuration (the same values as oracle-sail/src/main.rs, written directly
 * instead of by stepping MSR at EL3 / ERET). */
function janus_init() -> unit = {
    __InitSystem();
    __janus_excl_valid = false;                         /* monitor open (CLREX) */
    __janus_excl_addr = Zeros(56);
    __janus_excl_size = 0;
    SCR_EL3 = Mk_SCR_EL3_Type(0x0000_0240_0603_0401);   /* NS RW API APK ATA EnSCXT HXEn EnTP2 */
    HCR_EL2 = Mk_HCR_EL2_Type(0x0000_0300_8000_0000);   /* RW API APK */
    HCRX_EL2 = Mk_HCRX_EL2_Type(0x0000_0000_0000_0800); /* MSCEn */
    CPTR_EL2 = Mk_CPTR_EL2_Type(0x0000_0000_0000_22FF); /* RES1 only */
    MDCR_EL2 = Mk_MDCR_EL2_Type(ZeroExtend(0x0, 64));
    HSTR_EL2 = Mk_HSTR_EL2_Type(ZeroExtend(0x0, 64));
    SCTLR_EL2 = Mk_SCTLR_EL2_Type(0x0000_0000_30C5_0830);
    MAIR_EL1 = Mk_MAIR_EL1_Type(ZeroExtend(0xFF, 64));
    TCR_EL1 = Mk_TCR_EL1_Type(0x0000_0025_B590_3510);
    /* TTBR0_EL1's low half lives in the AArch32 TTBR0 storage: write through the accessor */
    TTBR0_EL1_write(Mk_TTBR0_EL1_Type(ZeroExtend(0x7000_0000, 128)));
    MDSCR_EL1 = Mk_MDSCR_EL1_Type(ZeroExtend(0x0, 64));
    CPACR_EL1 = Mk_CPACR_EL1_Type(ZeroExtend(0x0333_0000, 64));
    SCTLR_EL1 = Mk_SCTLR_EL1_Type(0x0200_0422_FCF4_F91D);
    /* FP/SIMD/SVE untrapped (the crate's init_harness at EL3, the oracle's CPACR/CPTR_EL2),
       SVE VL 512 as Linux/qemu-user; FPCR = FPSR = 0. */
    CPTR_EL3[EZ] = 0b1;
    CPTR_EL3[TFP] = 0b0;
    CPTR_EL3[ESM] = 0b1;
    ZCR_EL3[LEN] = 0b1111;
    ZCR_EL2 = Mk_ZCR_EL2_Type(ZeroExtend(0xF, 64));
    ZCR_EL1 = Mk_ZCR_EL1_Type(ZeroExtend(0x3, 64));
    FPCR = Mk_FPCR_Type(ZeroExtend(0x0, 64));
    FPSR = Mk_FPSR_Type(ZeroExtend(0x0, 64));
    /* ERET to EL0t with SPSR_EL3 = 0. */
    PSTATE.EL = EL0;
    PSTATE.SP = 0b0;
    PSTATE.nRW = 0b0;
    PSTATE.N = 0b0; PSTATE.Z = 0b0; PSTATE.C = 0b0; PSTATE.V = 0b0;
    PSTATE.D = 0b0; PSTATE.A = 0b0; PSTATE.I = 0b0; PSTATE.F = 0b0;
    PSTATE.SS = 0b0; PSTATE.IL = 0b0; PSTATE.BTYPE = 0b00;
    PSTATE.PAN = 0b0; PSTATE.UAO = 0b0; PSTATE.DIT = 0b0; PSTATE.TCO = 0b0;
    PSTATE.SSBS = 0b0; PSTATE.ALLINT = 0b0; PSTATE.PM = 0b0;
    ()
}

function janus_set_x(n : bits(5), v : bits(64)) -> unit = X_set(UInt(n), 64, v)
function janus_get_x(n : bits(5)) -> bits(64) = X_read(UInt(n), 64)
function janus_set_sp(v : bits(64)) -> unit = SP_set(v)
function janus_get_sp() -> bits(64) = SP_read()
function janus_set_pc(v : bits(64)) -> unit = { _PC = v }
function janus_get_pc() -> bits(64) = _PC
function janus_set_nzcv(f : bits(4)) -> unit = {
    PSTATE.N = [f[3]]; PSTATE.Z = [f[2]]; PSTATE.C = [f[1]]; PSTATE.V = [f[0]]
}
function janus_get_nzcv() -> bits(4) = PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V
/* V0-V31: the low 128 bits of the SVE Z registers (architectural storage, as the crate's
 * set_z_chunk); read back through Arm's V[] accessor. */
function janus_set_v(n : bits(5), v : bits(128)) -> unit = { _Z[UInt(n)] = ZeroExtend(v, MAX_VL) }
function janus_get_v(n : bits(5)) -> bits(128) = V_read(UInt(n), 128)
function janus_set_tpidr(v : bits(64)) -> unit = { TPIDR_EL0 = v }

/* One A64 instruction at _PC, opcode injected (as the crate's step_a64 and the model's
 * __InstructionExecute: SEE retry once, PC += 4 unless a branch was taken). */
function janus_step(opcode : bits(32)) -> JanusOutcome = {
    __janus_exc_taken = false;
    SEE = -1;
    __BranchTaken = false;
    __ExclusiveMonitorSet = false;
    __SetThisInstrDetails(__A64, opcode, __DefaultCond(__A64));
    res : JanusOutcome = Janus_OK;
    try {
        try {
            __DecodeA64(UInt(_PC), opcode)
        } catch {
            exn if IsSEE(exn) => __DecodeA64(UInt(_PC), opcode),
            exn => throw(exn)
        }
    } catch {
        Error_ExceptionTaken() => { res = Janus_Exception },
        Error_Undefined() => { res = Janus_Undefined },
        Error_Unpredictable() => { res = Janus_Unpredictable },
        Error_ConstrainedUnpredictable() => { res = Janus_Unpredictable },
        Error_See(_) => { res = Janus_See },
        Error_ImplementationDefined(s) => { __janus_impdef = s; res = Janus_ImpDef },
        _ => { res = Janus_Other }
    };
    if res == Janus_OK & not_bool(__BranchTaken) then {
        _PC = _PC + 4
    };
    res
}

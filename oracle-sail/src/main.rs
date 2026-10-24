//! `janus-oracle-sail`: execute Janus differential-test cases on the Sail arm-v9.4-a model
//! (rems-project/sail-arm, translated from Arm's ASL), embedded through the
//! `sail-aarch64-oracle` crate.
//!
//! Input: `layout.Case` JSON lines (oracle/layout/layout.go), stdin.
//! Output: `layout.HW` JSON lines (the same format the qemu runner writes), stdout, in input
//! order, plus a few extra fields (`el`, `esr`, `far`, `ec`, `flags`) that Go's decoder ignores.
//!
//! Per case the model is put, architecturally (by stepping MSR/ERET in the model itself), in a
//! Linux-like EL0 user state:
//!   * EL3 → EL2 (Non-secure, AArch64, no traps) → EL1 (AArch64) → ERET to EL0t at TestPC;
//!   * stage-1 translation ON with an identity map of exactly the code page (user RX, holding
//!     the word at TestPC, every other word 0 = UDF) and the data buffer (user RW, UXN),
//!     Normal write-back memory, 4K granule, 48-bit VA, TBI0 = 1 (Linux), EPD1 = 1;
//!   * SCTLR_EL1 = Linux's INIT_SCTLR_EL1_MMU_ON bits (A = 0, SA0 = 1, SA = 1, nAA = 0, ...);
//!   * FP/SIMD/SVE/SME untrapped (Linux enables them lazily, transparently), SVE VL 512,
//!     SME SVL 256 (Linux/qemu-user defaults).
//! Synchronous exceptions are taken to EL1; ESR_EL1/FAR_EL1/ELR_EL1/SPSR_EL1/SP_EL0 are read
//! back with MRS and mapped to the signal Linux would deliver (what the qemu runner observes).
//!
//! Modes:
//!   janus-oracle-sail [-j N]   supervisor: N worker processes, restarts a worker that dies
//!                              (a Sail runtime assertion aborts the process) and reports
//!                              that case as status "error".
//!   janus-oracle-sail --worker one-process worker (stdin cases → stdout results, flushed per
//!                              line).

use sail_aarch64_oracle::{Oracle, P_CHUNKS, Z_CHUNKS};

extern "C" {
    /// Added by instrument_model.py: CONSTRAINED UNPREDICTABLE events in the Sail model
    /// (ConstrainUnpredictable{,Bits,Integer} calls and thrown Error_Unpredictable).
    static janus_sail_unpredictable: u64;
    /// Added by instrument_model.py: Sail exceptions no handler on the A64 path catches
    /// (Error_ConstrainedUnpredictable/ImplementationDefined/ReservedEncoding/SError). The
    /// step then returns half-executed with the instance's have_exception flag set.
    static janus_sail_uncaught: u64;
}

fn unpredictable_count() -> u64 {
    // SAFETY: plain global in the linked model; workers are single-threaded.
    unsafe { std::ptr::read_volatile(std::ptr::addr_of!(janus_sail_unpredictable)) }
}

fn uncaught_count() -> u64 {
    // SAFETY: as above.
    unsafe { std::ptr::read_volatile(std::ptr::addr_of!(janus_sail_uncaught)) }
}
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{Arc, Mutex};

// ---- layout (must match oracle/layout/layout.go) ----
const CODE_PAGE: u64 = 0x10_0000_0000;
const TEST_PC: u64 = CODE_PAGE + 0x800;
const ENTRY_PAGE: u64 = CODE_PAGE - 0x7F0_0000;
const DATA_BASE: u64 = CODE_PAGE + 0x4_0000;
const DATA_SIZE: u64 = 4096;
const PAGE: u64 = 4096;

fn pattern(seed: u64, i: u64) -> u8 {
    ((i.wrapping_mul(157)
        .wrapping_add(seed.wrapping_mul(89))
        .wrapping_add((i / 256).wrapping_mul(41))
        .wrapping_add(7))
        % 256) as u8
}

#[derive(Deserialize)]
struct Case {
    id: i64,
    word: String,
    #[serde(default)]
    pc: String,
    x: Vec<String>,
    sp: String,
    nzcv: u32,
    seed: u64,
    /// V0..V31 as 128-bit hex (absent: all zero).
    #[serde(default)]
    v: Vec<String>,
    /// TPIDR_EL0 (absent: 0).
    #[serde(default)]
    tpidr: String,
    /// FPCR and FPSR (absent: 0), written by stepping `MSR FPCR/FPSR, Xt` at EL0.
    #[serde(default)]
    fpcr: String,
    #[serde(default)]
    fpsr: String,
    /// Sequence mode (docs/ORACLE.md): a block laid out from TestPC, run until the PC leaves
    /// it; `word` is then ignored.
    #[serde(default)]
    words: Vec<String>,
}

#[derive(Serialize, Default)]
struct Hw {
    id: i64,
    status: String,
    #[serde(skip_serializing_if = "is_zero")]
    sig: i64,
    #[serde(skip_serializing_if = "is_zero")]
    code: i64,
    #[serde(skip_serializing_if = "String::is_empty")]
    addr: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pc: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    x: Vec<String>,
    #[serde(skip_serializing_if = "String::is_empty")]
    sp: String,
    nzcv: u32,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    mem: Vec<[i64; 2]>,
    #[serde(skip_serializing_if = "String::is_empty")]
    note: String,
    /// V0..V31 after the instruction (the low 128 bits of Z0..Z31).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    v: Vec<String>,
    /// FPCR and FPSR after the instruction.
    #[serde(skip_serializing_if = "String::is_empty")]
    fpcr: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    fpsr: String,
    // Sail-only extras.
    #[serde(skip_serializing_if = "String::is_empty")]
    esr: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    far: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    ec: String,
    /// Number of CONSTRAINED UNPREDICTABLE events while executing the instruction (the
    /// result is then a stub's choice, not Arm's). Absent when 0.
    #[serde(skip_serializing_if = "is_zero")]
    unpredictable: i64,
}

fn is_zero(v: &i64) -> bool {
    *v == 0
}

fn hex(v: u64) -> String {
    format!("0x{v:x}")
}

fn parse_hex(s: &str) -> Result<u64, String> {
    let t = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
    u64::from_str_radix(t, 16).map_err(|e| format!("bad hex '{s}': {e}"))
}

/// A hex number of up to 128 bits as (low, high) halves.
fn parse_hex128(s: &str) -> Result<(u64, u64), String> {
    let t = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
    let v = u128::from_str_radix(t, 16).map_err(|e| format!("bad hex '{s}': {e}"))?;
    Ok((v as u64, (v >> 64) as u64))
}

fn hex128(lo: u64, hi: u64) -> String {
    format!("0x{:x}", (u128::from(hi) << 64) | u128::from(lo))
}

// ---- system-register access encodings ----
/// MSR/MRS (register) encoding. `op0` is 2 or 3.
const fn sysreg(op0: u32, op1: u32, crn: u32, crm: u32, op2: u32) -> u32 {
    ((op0 - 2) << 19) | (op1 << 16) | (crn << 12) | (crm << 8) | (op2 << 5)
}
const fn msr(reg: u32, rt: u32) -> u32 {
    0xD510_0000 | reg | rt
}
const fn mrs(reg: u32, rt: u32) -> u32 {
    0xD530_0000 | reg | rt
}

const SCTLR_EL1: u32 = sysreg(3, 0, 1, 0, 0);
const CPACR_EL1: u32 = sysreg(3, 0, 1, 0, 2);
const ZCR_EL1: u32 = sysreg(3, 0, 1, 2, 0);
const SMCR_EL1: u32 = sysreg(3, 0, 1, 2, 6);
const TTBR0_EL1: u32 = sysreg(3, 0, 2, 0, 0);
const TTBR1_EL1: u32 = sysreg(3, 0, 2, 0, 1);
const TCR_EL1: u32 = sysreg(3, 0, 2, 0, 2);
const SPSR_EL1: u32 = sysreg(3, 0, 4, 0, 0);
const ELR_EL1: u32 = sysreg(3, 0, 4, 0, 1);
const SP_EL0: u32 = sysreg(3, 0, 4, 1, 0);
const ESR_EL1: u32 = sysreg(3, 0, 5, 2, 0);
const FAR_EL1: u32 = sysreg(3, 0, 6, 0, 0);
const MAIR_EL1: u32 = sysreg(3, 0, 10, 2, 0);
const VBAR_EL1: u32 = sysreg(3, 0, 12, 0, 0);
const MDSCR_EL1: u32 = sysreg(2, 0, 0, 2, 2);
const SCTLR_EL2: u32 = sysreg(3, 4, 1, 0, 0);
const HCR_EL2: u32 = sysreg(3, 4, 1, 1, 0);
const MDCR_EL2: u32 = sysreg(3, 4, 1, 1, 1);
const CPTR_EL2: u32 = sysreg(3, 4, 1, 1, 2);
const HSTR_EL2: u32 = sysreg(3, 4, 1, 1, 3);
const ZCR_EL2: u32 = sysreg(3, 4, 1, 2, 0);
const HCRX_EL2: u32 = sysreg(3, 4, 1, 2, 2);
const SMCR_EL2: u32 = sysreg(3, 4, 1, 2, 6);
const SCR_EL3: u32 = sysreg(3, 6, 1, 1, 0);
const SPSR_EL3: u32 = sysreg(3, 6, 4, 0, 0);
const ELR_EL3: u32 = sysreg(3, 6, 4, 0, 1);

const FPCR: u32 = sysreg(3, 3, 4, 4, 0);
const FPSR: u32 = sysreg(3, 3, 4, 4, 1);

const ERET: u32 = 0xD69F_03E0;
const SVC0: u32 = 0xD400_0001;
const SMC0: u32 = 0xD400_0003;
const CLREX: u32 = 0xD503_305F;

// ---- configuration values ----
fn bits(list: &[u32]) -> u64 {
    list.iter().fold(0, |a, b| a | 1u64 << b)
}

/// SCR_EL3: NS, RW (lower ELs AArch64), API/APK (PAuth untrapped), ATA (MTE tag access),
/// EnSCXT, HXEn (HCRX_EL2 live: MOPS needs HCRX_EL2.MSCEn), EnTP2. SMD = 0 (we use SMC
/// to get back to EL3 between cases), HCE = 0 (HVC UNDEFINED as at Linux EL0), FGTEn = 0.
fn scr_el3() -> u64 {
    bits(&[0, 10, 16, 17, 25, 26, 38, 41])
}
/// HCR_EL2: RW (EL1 AArch64), APK/API (PAuth not trapped to EL2, as on a Linux host); no
/// stage 2, no other traps, TGE = 0, E2H = 0.
fn hcr_el2() -> u64 {
    bits(&[31, 40, 41])
}
/// HCRX_EL2: MSCEn (FEAT_MOPS at EL1/EL0).
fn hcrx_el2() -> u64 {
    bits(&[11])
}
/// CPTR_EL2 (E2H = 0 layout): RES1 bits 13, 9, 7:0; TZ (8) = TFP (10) = TSM (12) = TTA (20) = 0.
fn cptr_el2() -> u64 {
    bits(&[13, 9, 7, 6, 5, 4, 3, 2, 1, 0])
}
/// SCTLR_EL1: Linux INIT_SCTLR_EL1_MMU_ON (M C SA SA0 SED EOS I DZE UCT nTWE TSCXT IESB EIS
/// SPAN UCI nTLSMD LSMAOE ITFSB EPAN) + EnIA/EnIB/EnDA/EnDB (Linux enables PAuth keys for
/// user tasks) + ATA0 (MTE tag access, TCF0 = 0: no tag-check faults) + MSCEn (MOPS).
/// A = 0 (no general alignment checking), nAA = 0, WXN = 0, E0E = 0 (little-endian).
fn sctlr_el1() -> u64 {
    bits(&[
        0, 2, 3, 4, 8, 11, 12, 13, 14, 15, 18, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 33, 37, 42,
        57,
    ])
}
/// CPACR_EL1: ZEN = 3, FPEN = 3, SMEN = 3, TTA = 0.
fn cpacr_el1() -> u64 {
    (3 << 16) | (3 << 20) | (3 << 24)
}
/// TCR_EL1 (Linux, 48-bit VA, 4K pages): T0SZ = T1SZ = 16, IRGN/ORGN = WBWA, SH = inner,
/// TG0 = 4K, TG1 = 4K, IPS = 48-bit, TBI0 = 1, TBI1 = 0, AS = 0, HA = HD = 0. EPD1 = 1: no
/// TTBR1 walks (the kernel half is not modelled; EL0 accesses there fault either way).
fn tcr_el1() -> u64 {
    let half = 16 | (1 << 8) | (1 << 10) | (3 << 12); // TxSZ, IRGNx, ORGNx, SHx
    half | (half << 16) | (1 << 23) | (2u64 << 30) | (5u64 << 32) | (1u64 << 37)
}
/// MAIR_EL1: Attr0 = Normal, inner/outer write-back non-transient RW-allocate.
const MAIR: u64 = 0xFF;
/// SVE: ZCR_ELx.LEN; VL = (LEN + 1) * 128. Linux default VL = 64 bytes.
const ZCR_LEN_EL1: u64 = 3;
/// SME: SMCR_ELx.LEN | FA64 (31) | EZT0 (30). Linux default SVL = 32 bytes.
const SMCR_EL1_VAL: u64 = 1 | (1 << 30) | (1 << 31);
const SMCR_EL2_VAL: u64 = 15 | (1 << 30) | (1 << 31);

// ---- translation tables (physical, outside every mapped VA) ----
const TT_L0: u64 = 0x7000_0000;
const TT_L1: u64 = TT_L0 + PAGE;
const TT_L2: u64 = TT_L0 + 2 * PAGE;
const TT_L3: u64 = TT_L0 + 3 * PAGE;
const TABLE: u64 = 0b11;
/// Level-3 page: valid|page, AttrIndx 0, AP = 01 (EL1+EL0 RW), SH = inner, AF, nG.
const PAGE_RW_USER: u64 = 0b11 | (1 << 6) | (3 << 8) | (1 << 10) | (1 << 11);
const PXN: u64 = 1 << 53;
const UXN: u64 = 1 << 54;

struct Cpu {
    o: Oracle,
    /// Discard this instance before the next case.
    poisoned: bool,
}

#[derive(Debug)]
struct SetupError(#[allow(dead_code)] String);

impl Cpu {
    fn new() -> Result<Self, SetupError> {
        let mut c = Cpu { o: Oracle::new(), poisoned: false };
        c.install_tables();
        c.to_el3_and_configure()?;
        Ok(c)
    }

    fn el(&self) -> u64 {
        (self.o.get_pstate() >> 11) & 3
    }

    fn write_sys(&mut self, reg: u32, v: u64) {
        self.o.set_x(0, v);
        self.o.step(msr(reg, 0));
    }

    fn read_sys(&mut self, reg: u32) -> u64 {
        self.o.step(mrs(reg, 0));
        self.o.get_x(0)
    }

    fn install_tables(&mut self) {
        for t in [TT_L0, TT_L1, TT_L2, TT_L3] {
            self.o.write_mem(t, &[0u8; PAGE as usize]);
        }
        let l0 = (CODE_PAGE >> 39) & 511;
        let l1 = (CODE_PAGE >> 30) & 511;
        let l2 = (CODE_PAGE >> 21) & 511;
        assert_eq!((DATA_BASE >> 21) & 511, l2, "code and data share an L3 table");
        self.o.write_mem_u64(TT_L0 + 8 * l0, TT_L1 | TABLE);
        self.o.write_mem_u64(TT_L1 + 8 * l1, TT_L2 | TABLE);
        self.o.write_mem_u64(TT_L2 + 8 * l2, TT_L3 | TABLE);
        let i_code = (CODE_PAGE >> 12) & 511;
        let i_data = (DATA_BASE >> 12) & 511;
        // Code page: user-executable (and, as in the qemu runner's RWX mmap, writable).
        self.o.write_mem_u64(TT_L3 + 8 * i_code, CODE_PAGE | PAGE_RW_USER | PXN);
        // Data buffer: user RW, never executable.
        self.o.write_mem_u64(TT_L3 + 8 * i_data, DATA_BASE | PAGE_RW_USER | PXN | UXN);
    }

    /// Get back to EL3 (EL0 --SVC--> EL1 --SMC--> EL3), then configure and ERET to EL0.
    fn to_el3_and_configure(&mut self) -> Result<(), SetupError> {
        if self.el() == 0 {
            self.o.step(SVC0);
        }
        if self.el() == 1 {
            self.o.step(SMC0);
        }
        if self.el() == 2 {
            self.o.step(SMC0);
        }
        if self.el() != 3 {
            return Err(SetupError(format!("could not return to EL3 (EL{})", self.el())));
        }
        if self.o.svcr() != 0 {
            return Err(SetupError("PSTATE.SM/ZA set".into()));
        }
        self.write_sys(SCR_EL3, scr_el3());
        self.write_sys(HCR_EL2, hcr_el2());
        self.write_sys(HCRX_EL2, hcrx_el2());
        self.write_sys(CPTR_EL2, cptr_el2());
        self.write_sys(MDCR_EL2, 0);
        self.write_sys(HSTR_EL2, 0);
        self.write_sys(SCTLR_EL2, bits(&[4, 5, 11, 16, 18, 22, 23, 28, 29])); // RES1, MMU off
        self.write_sys(ZCR_EL2, 15);
        self.write_sys(SMCR_EL2, SMCR_EL2_VAL);
        self.write_sys(MAIR_EL1, MAIR);
        self.write_sys(TCR_EL1, tcr_el1());
        self.write_sys(TTBR0_EL1, TT_L0);
        self.write_sys(TTBR1_EL1, 0);
        self.write_sys(VBAR_EL1, 0);
        self.write_sys(MDSCR_EL1, 0);
        self.write_sys(CPACR_EL1, cpacr_el1());
        self.write_sys(ZCR_EL1, ZCR_LEN_EL1);
        self.write_sys(SMCR_EL1, SMCR_EL1_VAL);
        self.write_sys(SCTLR_EL1, sctlr_el1());
        self.write_sys(SPSR_EL3, 0); // EL0t, AArch64, DAIF = 0, NZCV = 0
        self.write_sys(ELR_EL3, TEST_PC);
        self.o.step(CLREX);
        // Architectural registers that survive between cases.
        self.o.set_fpcr(0);
        self.o.set_fpsr(0);
        self.o.set_tpidr_el0(0);
        self.o.set_tpidrro_el0(0);
        let z = [0u64; Z_CHUNKS];
        let p = [0u64; P_CHUNKS];
        for n in 0..32 {
            self.o.set_z(n, &z);
        }
        for n in 0..16 {
            self.o.set_p(n, &p);
        }
        self.o.set_ffr(&p);
        self.o.step(ERET);
        if self.el() != 0 || self.o.get_pc() != TEST_PC {
            return Err(SetupError(format!(
                "ERET did not reach EL0 at TestPC (EL{}, pc {:#x})",
                self.el(),
                self.o.get_pc()
            )));
        }
        Ok(())
    }

    fn run(&mut self, c: &Case) -> Hw {
        let mut r = Hw { id: c.id, ..Default::default() };
        let err = |r: &mut Hw, n: String| {
            r.status = "error".into();
            r.note = n;
        };
        let word = match parse_hex(&c.word) {
            Ok(w) if w <= 0xffff_ffff => w as u32,
            _ => {
                err(&mut r, "bad word".into());
                return r;
            }
        };
        let pc = if c.pc.is_empty() { Ok(TEST_PC) } else { parse_hex(&c.pc) };
        if pc != Ok(TEST_PC) {
            err(&mut r, "pc must be layout.TestPC".into());
            return r;
        }
        if c.x.len() != 31 {
            err(&mut r, "x must have 31 entries".into());
            return r;
        }
        let mut x = [0u64; 31];
        for i in 0..31 {
            match parse_hex(&c.x[i]) {
                Ok(v) => x[i] = v,
                Err(e) => {
                    err(&mut r, e);
                    return r;
                }
            }
        }
        let sp = match parse_hex(&c.sp) {
            Ok(v) => v,
            Err(e) => {
                err(&mut r, e);
                return r;
            }
        };

        // Memory: code page = word (or the block) at TestPC, zeros (UDF #0) elsewhere;
        // data = pattern.
        let mut block: Vec<u32> = Vec::new();
        for w in &c.words {
            match parse_hex(w) {
                Ok(v) if v <= 0xffff_ffff => block.push(v as u32),
                _ => {
                    err(&mut r, "bad words entry".into());
                    return r;
                }
            }
        }
        let mut code = vec![0u8; PAGE as usize];
        let off = (TEST_PC - CODE_PAGE) as usize;
        if block.is_empty() {
            code[off..off + 4].copy_from_slice(&word.to_le_bytes());
        } else {
            if block.len() > 0x180 {
                err(&mut r, "words too long".into());
                return r;
            }
            for (i, w) in block.iter().enumerate() {
                code[off + 4 * i..off + 4 * i + 4].copy_from_slice(&w.to_le_bytes());
            }
        }
        self.o.write_mem(CODE_PAGE, &code);
        let data: Vec<u8> = (0..DATA_SIZE).map(|i| pattern(c.seed, i)).collect();
        self.o.write_mem(DATA_BASE, &data);

        let mut vregs = [(0u64, 0u64); 32];
        if !c.v.is_empty() {
            if c.v.len() != 32 {
                err(&mut r, "v must have 32 entries".into());
                return r;
            }
            for i in 0..32 {
                match parse_hex128(&c.v[i]) {
                    Ok(p) => vregs[i] = p,
                    Err(e) => {
                        err(&mut r, e);
                        return r;
                    }
                }
            }
        }
        let tpidr = if c.tpidr.is_empty() {
            0
        } else {
            match parse_hex(&c.tpidr) {
                Ok(v) => v,
                Err(e) => {
                    err(&mut r, e);
                    return r;
                }
            }
        };

        let fpcr = if c.fpcr.is_empty() { Ok(0) } else { parse_hex(&c.fpcr) };
        let fpsr = if c.fpsr.is_empty() { Ok(0) } else { parse_hex(&c.fpsr) };
        let (fpcr, fpsr) = match (fpcr, fpsr) {
            (Ok(a), Ok(b)) if a <= 0xffff_ffff && b <= 0xffff_ffff => (a, b),
            _ => {
                err(&mut r, "bad fpcr/fpsr".into());
                return r;
            }
        };

        // EL0 state. FPCR/FPSR first: they are written by stepping real MSRs at EL0 (which
        // use X0 and advance the PC; both are set afterwards).
        self.write_sys(FPCR, fpcr);
        self.write_sys(FPSR, fpsr);
        if self.el() != 0 || self.o.get_fpcr() != fpcr || self.o.get_fpsr() != fpsr {
            self.poisoned = true;
            err(&mut r, format!(
                "fpcr {fpcr:#x} / fpsr {fpsr:#x} not kept by the model (got {:#x} / {:#x}, EL{})",
                self.o.get_fpcr(), self.o.get_fpsr(), self.el()));
            return r;
        }
        for (i, v) in x.iter().enumerate() {
            self.o.set_x(i as u32, *v);
        }
        // V0..V31 are the low 128 bits of Z0..Z31 (the upper bits stay zero, as after any
        // Advanced SIMD write on hardware).
        for (n, (lo, hi)) in vregs.iter().enumerate() {
            let mut z = [0u64; Z_CHUNKS];
            z[0] = *lo;
            z[1] = *hi;
            self.o.set_z(n as u32, &z);
        }
        self.o.set_tpidr_el0(tpidr);
        self.o.set_sp(sp); // SP_EL0 (PSTATE.EL = 0)
        self.o.set_nzcv(c.nzcv & 15);
        self.o.set_pc(TEST_PC);

        let (cu0, un0) = (unpredictable_count(), uncaught_count());
        if block.is_empty() {
            self.o.step(word);
        } else {
            // Step the block until the PC leaves it (falling through to the UDF after it, a
            // branch out, or an exception to EL1), at most 4·n+1 instructions (the Lean side's
            // fuel, Oracle.runSeq).
            let end = TEST_PC + 4 * block.len() as u64;
            for _ in 0..4 * block.len() + 1 {
                let pc = self.o.get_pc();
                if self.el() != 0 || pc < TEST_PC || pc >= end || pc % 4 != 0 {
                    break;
                }
                self.o.step(block[((pc - TEST_PC) / 4) as usize]);
                if uncaught_count() != un0 {
                    break;
                }
            }
        }
        r.unpredictable = (unpredictable_count() - cu0) as i64;
        if uncaught_count() != un0 {
            self.poisoned = true;
            r.status = "error".into();
            r.note = "uncaught Sail exception (Error_ConstrainedUnpredictable or \
                      ImplementationDefined/ReservedEncoding/SError): no authoritative result"
                .into();
            r.pc = hex(self.o.get_pc());
            return r;
        }
        if r.unpredictable != 0 {
            self.poisoned = true; // a stub's choice may leave odd state behind: start afresh
        }

        let el = self.el();
        if std::env::var_os("SAIL_DEBUG").is_some() {
            eprintln!("after step: EL{el} pc {:#x} esr_el3 {:#x}", self.o.get_pc(), self.o.esr_el3());
        }
        let snap = self.o.snapshot();
        r.x = snap.x.iter().map(|v| hex(*v)).collect();
        r.fpcr = hex(self.o.get_fpcr());
        r.fpsr = hex(self.o.get_fpsr());
        let mut after = vec![0u8; DATA_SIZE as usize];
        self.o.read_mem(DATA_BASE, &mut after);
        for i in 0..DATA_SIZE as usize {
            if after[i] != data[i] {
                r.mem.push([i as i64, after[i] as i64]);
            }
        }
        match el {
            0 => {
                let npc = snap.pc;
                r.pc = hex(npc);
                r.sp = hex(self.o.get_sp());
                r.nzcv = snap.nzcv;
                r.v = (0..32).map(|n| {
                    let z = self.o.get_z(n);
                    hex128(z[0], z[1])
                }).collect();
                // What the qemu runner would see next: the fetch at the new PC faults.
                let (status, sig, code, note) = next_fetch(npc);
                r.status = status.into();
                r.sig = sig;
                r.code = code;
                r.addr = hex(npc);
                r.note = note.into();
            }
            1 => {
                let esr = self.read_sys(ESR_EL1);
                let far = self.read_sys(FAR_EL1);
                let elr = self.read_sys(ELR_EL1);
                let spsr = self.read_sys(SPSR_EL1);
                let sp0 = self.read_sys(SP_EL0);
                r.esr = hex(esr);
                r.far = hex(far);
                let ec = (esr >> 26) & 0x3f;
                r.ec = format!("0x{ec:02x}");
                r.pc = hex(elr);
                r.sp = hex(sp0);
                r.nzcv = ((spsr >> 28) & 15) as u32;
                if ec == 0x01 && esr & 3 == 0 {
                    // WFI at EL0 traps (Linux leaves SCTLR_EL1.nTWI = 0) and the kernel's
                    // wfi_handler skips it: user-visibly a NOP.
                    let npc = elr.wrapping_add(4);
                    let (status, sig, code, _) = next_fetch(npc);
                    r.status = status.into();
                    r.sig = sig;
                    r.code = code;
                    r.addr = hex(npc);
                    r.pc = hex(npc);
                    r.note = "WFI trapped to EL1 and skipped (Linux wfi_handler)".into();
                    r.fpcr = hex(self.o.get_fpcr());
                    r.fpsr = hex(self.o.get_fpsr());
                    r.v = (0..32).map(|n| {
                        let z = self.o.get_z(n);
                        hex128(z[0], z[1])
                    }).collect();
                    return r;
                }
                let (sig, code, addr, note) = linux_signal(esr, far, elr, sp0);
                r.status = "fault".into();
                r.sig = sig;
                r.code = code;
                r.addr = hex(addr);
                r.note = note;
            }
            e => {
                r.status = "error".into();
                r.note = format!("instruction left the model at EL{e}");
                r.pc = hex(snap.pc);
            }
        }
        r
    }
}

/// Status the qemu runner assigns when the instruction completed and the next fetch (at
/// `pc`) traps: (status, signal, si_code, note).
fn next_fetch(pc: u64) -> (&'static str, i64, i64, &'static str) {
    const SIGILL: i64 = 4;
    const SIGBUS: i64 = 7;
    const SIGSEGV: i64 = 11;
    const SIGALRM: i64 = 14;
    if pc == TEST_PC {
        return ("selfloop", SIGALRM, 0, "");
    }
    if pc % 4 != 0 {
        return ("ok", SIGBUS, 1, "");
    }
    if (CODE_PAGE..CODE_PAGE + PAGE).contains(&pc) {
        return ("ok", SIGILL, 1, "");
    }
    if (ENTRY_PAGE..ENTRY_PAGE + 2 * PAGE).contains(&pc) {
        return ("escaped", SIGSEGV, 0, "target is mapped executable memory in the qemu runner");
    }
    if (DATA_BASE..DATA_BASE + DATA_SIZE).contains(&pc) {
        return ("ok", SIGSEGV, 2, "");
    }
    ("ok", SIGSEGV, 1, "")
}

/// Map an EL0 synchronous exception to the Linux signal: (signal, si_code, si_addr, note).
fn linux_signal(esr: u64, far: u64, elr: u64, sp: u64) -> (i64, i64, u64, String) {
    let ec = (esr >> 26) & 0x3f;
    // Linux reports si_addr as untagged_addr(FAR): bits 63:56 := bit 55 (sign_extend64(a, 55)).
    let untag = |a: u64| (((a << 8) as i64) >> 8) as u64;
    match ec {
        0x00 => (4, 1, elr, "undefined".into()),
        0x01 => (4, 1, elr, "WFx trap".into()),
        0x0d => (4, 1, elr, "BTI".into()),
        0x0a => (4, 1, elr, "LD64B/ST64B trap (not enabled at EL0 by Linux)".into()),
        0x0e => (4, 1, elr, "illegal execution state".into()),
        0x15 => (0, 0, elr, "svc".into()),
        0x18 => (4, 1, elr, "MSR/MRS/system trap".into()),
        0x1c => (4, 2, elr, "PAC authentication failure (FPAC)".into()),
        0x22 => (7, 1, far, "PC alignment".into()),
        0x26 => (7, 1, sp, "SP alignment".into()),
        0x27 => (4, 1, elr, "MOPS exception".into()),
        0x2c => (8, 0, elr, "trapped floating-point exception".into()),
        0x3c => (5, 1, elr, "brk".into()),
        0x24 => {
            let dfsc = esr & 0x3f;
            let wnr = if esr & (1 << 6) != 0 { "write" } else { "read" };
            match dfsc {
                0x04..=0x07 => (11, 1, untag(far), format!("translation fault ({wnr})")),
                0x08..=0x0b => (11, 2, untag(far), format!("access flag fault ({wnr})")),
                0x0c..=0x0f => (11, 2, untag(far), format!("permission fault ({wnr})")),
                0x00..=0x03 => (11, 1, untag(far), format!("address size fault ({wnr})")),
                0x11 => (11, 9, untag(far), "MTE tag check fault".into()),
                0x21 => (7, 1, untag(far), format!("alignment fault ({wnr})")),
                d => (11, 0, untag(far), format!("data abort dfsc {d:#x}")),
            }
        }
        e => (0, 0, elr, format!("unmapped EC {e:#x}")),
    }
}

fn worker() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let mut cpu: Option<Cpu> = None;
    let fresh = std::env::var("SAIL_FRESH").map(|v| v == "1").unwrap_or(false);
    for line in stdin.lock().lines() {
        let line = line.expect("stdin");
        let l = line.trim();
        if l.is_empty() {
            continue;
        }
        let res = match serde_json::from_str::<Case>(l) {
            Err(e) => {
                serde_json::json!({"status": "error", "note": format!("bad case: {e}")}).to_string()
            }
            Ok(c) => {
                // Reuse the CPU (return to EL3 + full reconfiguration); fall back to a fresh one.
                // SAIL_FRESH=1: a brand-new model instance per case (validation of the reuse path).
                let ready = !fresh
                    && !cpu.as_ref().map(|p| p.poisoned).unwrap_or(true)
                    && matches!(cpu.as_mut().map(|p| p.to_el3_and_configure()), Some(Ok(())));
                if !ready {
                    cpu = Some(Cpu::new().unwrap_or_else(|e| {
                        eprintln!("janus-oracle-sail: setup failed: {e:?}");
                        std::process::exit(3)
                    }));
                }
                let r = cpu.as_mut().unwrap().run(&c);
                serde_json::to_string(&r).unwrap()
            }
        };
        writeln!(out, "{res}").unwrap();
        out.flush().unwrap();
    }
}

struct Proc {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    /// Last line the worker wrote to stderr (a Sail runtime assertion message).
    last_err: Arc<Mutex<String>>,
}

fn spawn() -> Proc {
    let exe = std::env::current_exe().expect("current_exe");
    let mut child = Command::new(exe)
        .arg("--worker")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn worker");
    let stdin = child.stdin.take().unwrap();
    let stdout = BufReader::new(child.stdout.take().unwrap());
    let last_err = Arc::new(Mutex::new(String::new()));
    let (err, le) = (child.stderr.take().unwrap(), last_err.clone());
    std::thread::spawn(move || {
        for l in BufReader::new(err).lines().map_while(Result::ok) {
            eprintln!("janus-oracle-sail worker: {l}");
            *le.lock().unwrap() = l;
        }
    });
    Proc { child, stdin, stdout, last_err }
}

fn case_id(line: &str) -> serde_json::Value {
    serde_json::from_str::<serde_json::Value>(line)
        .ok()
        .and_then(|v| v.get("id").cloned())
        .unwrap_or(serde_json::Value::Null)
}

fn supervisor(jobs: usize, as_model: bool) {
    let lines: Vec<String> = std::io::stdin()
        .lock()
        .lines()
        .map(|l| l.expect("stdin"))
        .filter(|l| !l.trim().is_empty())
        .collect();
    let n = lines.len();
    let lines = Arc::new(lines);
    let results: Arc<Mutex<Vec<Option<String>>>> = Arc::new(Mutex::new(vec![None; n]));
    let next = Arc::new(Mutex::new(0usize));
    let done = Arc::new(Mutex::new(0usize));
    let mut handles = vec![];
    for _ in 0..jobs.max(1).min(n.max(1)) {
        let (lines, results, next, done) =
            (lines.clone(), results.clone(), next.clone(), done.clone());
        handles.push(std::thread::spawn(move || {
            let mut p = spawn();
            loop {
                let i = {
                    let mut g = next.lock().unwrap();
                    if *g >= n {
                        break;
                    }
                    *g += 1;
                    *g - 1
                };
                let line = &lines[i];
                let mut resp = String::new();
                let ok = writeln!(p.stdin, "{line}").and_then(|_| p.stdin.flush()).is_ok()
                    && p.stdout.read_line(&mut resp).map(|k| k > 0).unwrap_or(false);
                let out = if ok {
                    resp.trim_end().to_string()
                } else {
                    let _ = p.child.kill();
                    let status = p.child.wait().ok();
                    std::thread::sleep(std::time::Duration::from_millis(20));
                    let msg = p.last_err.lock().unwrap().clone();
                    p = spawn();
                    serde_json::json!({"id": case_id(line), "status": "error",
                        "note": format!("sail model aborted ({}): {msg}",
                            status.map(|s| s.to_string()).unwrap_or_default())})
                    .to_string()
                };
                results.lock().unwrap()[i] = Some(out);
                let mut d = done.lock().unwrap();
                *d += 1;
                if *d % 100000 == 0 {
                    eprintln!("janus-oracle-sail: {}/{}", *d, n);
                }
            }
            drop(p.stdin);
            let _ = p.child.wait();
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    for r in results.lock().unwrap().iter() {
        let line = r.as_deref().unwrap_or("{\"status\":\"error\"}");
        if as_model {
            writeln!(out, "{}", to_model(line)).unwrap();
        } else {
            writeln!(out, "{line}").unwrap();
        }
    }
}

/// Re-shape one HW result line as a `layout.Model` line (status ok | fault | error, `fault` =
/// signal + cause), so the existing comparator can diff qemu (as hardware) against Sail.
fn to_model(line: &str) -> String {
    use serde_json::{json, Value};
    let v: Value = serde_json::from_str(line).unwrap_or(json!({"status": "error"}));
    let st = v.get("status").and_then(|s| s.as_str()).unwrap_or("error");
    let mut m = serde_json::Map::new();
    m.insert("id".into(), v.get("id").cloned().unwrap_or(Value::Null));
    match st {
        "ok" | "selfloop" | "escaped" => {
            m.insert("status".into(), json!("ok"));
            for k in ["pc", "x", "sp", "nzcv", "mem", "v", "fpcr", "fpsr"] {
                if let Some(x) = v.get(k) {
                    m.insert(k.into(), x.clone());
                }
            }
            if !m.contains_key("nzcv") {
                m.insert("nzcv".into(), json!(0));
            }
        }
        "fault" => {
            let sig = v.get("sig").and_then(|s| s.as_i64()).unwrap_or(0);
            let name = match sig {
                4 => "SIGILL",
                5 => "SIGTRAP",
                7 => "SIGBUS",
                8 => "SIGFPE",
                11 => "SIGSEGV",
                0 => "nosignal",
                _ => "sig?",
            };
            let note = v.get("note").and_then(|s| s.as_str()).unwrap_or("");
            m.insert("status".into(), json!("fault"));
            m.insert("fault".into(), json!(format!("sail:{name}:{note}")));
            m.insert("nzcv".into(), v.get("nzcv").cloned().unwrap_or(json!(0)));
        }
        _ => {
            m.insert("status".into(), json!("error"));
            m.insert("nzcv".into(), json!(0));
        }
    }
    Value::Object(m).to_string()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("usage: janus-oracle-sail [-j N] [--format hw|model] < cases.jsonl > sail.jsonl");
        println!("  --format hw     layout.HW lines (default; what the qemu runner writes)");
        println!("  --format model  layout.Model lines (what janus-oracle writes)");
        println!("  --to-model      convert HW lines on stdin to Model lines (no execution)");
        println!("  env: JANUS_SAIL_JOBS (default workers), SAIL_FRESH=1 (new model instance per case)");
        return;
    }
    if args.iter().any(|a| a == "--to-model") {
        // Convert HW lines (a previous run's output) on stdin to Model lines.
        let stdout = std::io::stdout();
        let mut out = BufWriter::new(stdout.lock());
        for line in std::io::stdin().lock().lines() {
            let line = line.expect("stdin");
            if !line.trim().is_empty() {
                writeln!(out, "{}", to_model(line.trim())).unwrap();
            }
        }
        return;
    }
    if args.iter().any(|a| a == "--worker") {
        worker();
        return;
    }
    // Default: JANUS_SAIL_JOBS, else every core. (`oracle run` shards in parallel itself, so
    // scripts/oracle-sail.sh sets JANUS_SAIL_JOBS=1 when this binary stands in for the runner.)
    let mut jobs = std::env::var("JANUS_SAIL_JOBS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1));
    if let Some(i) = args.iter().position(|a| a == "-j") {
        jobs = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(jobs);
    }
    let as_model = args.windows(2).any(|w| w[0] == "--format" && w[1] == "model");
    supervisor(jobs, as_model);
}

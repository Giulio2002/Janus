/* =============================================================================
 * harness.sail: the Janus entry points into the sliced Sail x86 model (docs/X86FORMAL.md).
 *
 * Appended after the sliced sail-x86-from-acl2 sources. Everything here is a thin wrapper:
 * prefix/ModRM/SIB decoding, the dispatch, the instruction semantics, the flag computations,
 * effective addresses and the application-level memory view are all the model's (ACL2 X86isa,
 * translated to Sail).
 *
 * The state set up by janus_x86_init is the one of oracle-amd64-formal/compare.py (the C
 * emulator's `-C cr4=512 -C set64bit=1 -C app_view=1`), written directly, plus CPL 3
 * (CS.RPL = 3) and every other control/segment register zeroed instead of left undefined.
 * ===========================================================================*/

enum JanusOutcome = {
  Janus_OK,       /* the instruction completed; registers/RIP/RFLAGS/memory hold the result    */
  Janus_Fault,    /* an architectural fault: x86_fault(msg), thrown as Efault(msg) by the slice (#UD, #GP, #DE, ...) */
  Janus_Error     /* x86_model_error(msg) (Emsg): unimplemented in x86isa, or janus-excluded by the slice */
}

register __janus_msg : string

function janus_x86_init() -> unit = {
    /* every register the 64-bit application-level path reads */
    ms_reg = false;
    fault_reg = false;
    app_view = true;
    marking_view = false;
    log_register_writes = false;
    janus_undef = 0;
    foreach (i from 0 to 6) { msrs[i] = 0x0000000000000000 };
    foreach (i from 0 to 16) { ctrs[i] = 0x0000000000000000 };
    foreach (i from 0 to 5) {
        seg_visibles[i] = 0x0000;
        seg_hidden_attrs[i] = 0x0000;
        seg_hidden_bases[i] = 0x0000000000000000;
        seg_hidden_limits[i] = 0x00000000
    };
    /* CR4.OSFXSR (SSE enabled), as compare.py's `-C cr4=512` */
    ctrs[4] = 0x0000000000000200;
    /* 64-bit mode: IA32_EFER.LMA = 1 and CS.L = 1 (main.sail's initialise_64_bit_mode) */
    let msr0 = msrs[0];
    let efer = Mk_ia32_eferbits(msr0[11 .. 0]);
    msrs[0] = [msr0 with 11 .. 0 = [efer with lma = 0b1].bits];
    seg_hidden_attrs[1] = [Mk_code_segment_descriptor_attributesbits(seg_hidden_attrs[1]) with l = 0b1].bits;
    /* CPL 3: CS.RPL = 3 */
    seg_visibles[1] = 0x0003;
    rflags = Mk_rflagsbits(0x00000002);
    ()
}

function janus_set_gpr(i : bits(4), v : bits(64)) -> unit = write_gpr(unsigned(i), v)
function janus_get_gpr(i : bits(4)) -> bits(64) = read_gpr(unsigned(i))
function janus_set_rip(v : bits(64)) -> unit = { rip = v }
function janus_get_rip() -> bits(64) = rip
function janus_set_rflags(v : bits(32)) -> unit = { rflags = Mk_rflagsbits(v) }
function janus_get_rflags() -> bits(32) = rflags.bits
function janus_set_undef(v : nat) -> unit = { janus_undef = v }
/* bits 255:0 of ZMMn (n < 16): XMMn and the upper YMM half */
function janus_set_ymm(i : bits(4), v : bits(256)) -> unit = {
    zmms[unsigned(i)] = [zmms[unsigned(i)] with 255 .. 0 = v]
}
function janus_get_ymm(i : bits(4)) -> bits(256) = zmms[unsigned(i)][255 .. 0]
/* FS base: 64-bit-mode FS-relative addressing reads IA32_FS_BASE (msrs[1]) */
function janus_set_fsbase(v : bits(64)) -> unit = { msrs[1] = v; seg_hidden_bases[4] = v }

/* One instruction at RIP, fetched from memory (x86_fetch_decode_execute). */
function janus_x86_step() -> JanusOutcome = {
    res : JanusOutcome = Janus_OK;
    try {
        x86_fetch_decode_execute()
    } catch {
        Efault(msg) => { __janus_msg = msg; res = Janus_Fault },
        Emsg(msg) => { __janus_msg = msg; res = Janus_Error },
        _ => { __janus_msg = "other exception"; res = Janus_Error }
    };
    res
}

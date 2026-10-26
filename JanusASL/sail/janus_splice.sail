/* Spliced over sail-arm's AArch64_TakeException (sail --splice). Records the exception
 * Arm's pseudocode raised and ends like the original: by throwing Error_ExceptionTaken.
 * Exception entry itself (vectoring, ESR/FAR/ELR/SPSR, PSTATE) is not executed: Janus
 * models EL0 only, and the driver classifies the fault from this record. */
function AArch64_TakeException (target_el, exception_in, preferred_exception_return, vect_offset_in) = {
    __janus_exc_taken = true;
    __janus_exc_target_el = target_el;
    __janus_exc_type = exception_in.exceptype;
    __janus_exc_syndrome = exception_in.syndrome;
    __janus_exc_vaddress = exception_in.vaddress;
    throw(Error_ExceptionTaken())
}

/* The local exclusive monitor (Arm ARM B2.9). sail-arm stubs it (impdefs.sail: IsExclusiveLocal
 * is TRUE, MarkExclusiveLocal and ClearExclusiveLocal do nothing), so every store-exclusive
 * passed, also in the Open Access state, where the architecture requires it to fail. These
 * replacements record the bytes the last load-exclusive marked; a store-exclusive passes the
 * local check only for exactly those bytes, and AArch64_ExclusiveMonitorsPass then clears the
 * monitor (as before, IsExclusiveGlobal and AArch64_IsExclusiveVA stay TRUE: one PE, and the
 * whole address is the reservation). Janus compares against this monitor in the Open Access
 * state, where both fail. */
function MarkExclusiveLocal (paddress, processorid, size) = {
    __janus_excl_valid = true;
    __janus_excl_addr = paddress.address;
    __janus_excl_size = size
}

function IsExclusiveLocal (paddress, processorid, size) =
    __janus_excl_valid & __janus_excl_addr == paddress.address & __janus_excl_size == size

function ClearExclusiveLocal processorid = {
    __janus_excl_valid = false
}

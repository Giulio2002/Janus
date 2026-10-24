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

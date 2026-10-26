/* Registers written by the spliced AArch64_TakeException (janus_splice.sail); placed right
 * after v8_base.sail, which declares the Exception type. */
register __janus_exc_taken : bool
register __janus_exc_target_el : bits(2)
register __janus_exc_type : Exception
register __janus_exc_syndrome : bits(25)
register __janus_exc_vaddress : bits(64)

/* The local exclusive monitor of the spliced MarkExclusiveLocal / IsExclusiveLocal /
 * ClearExclusiveLocal (janus_splice.sail): valid = Exclusive Access state, marking `size`
 * bytes at physical address `addr`. janus_init leaves it open (the native runner's CLREX). */
register __janus_excl_valid : bool
register __janus_excl_addr : bits(56)
register __janus_excl_size : int

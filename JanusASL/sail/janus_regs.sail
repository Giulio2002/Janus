/* Registers written by the spliced AArch64_TakeException (janus_splice.sail); placed right
 * after v8_base.sail, which declares the Exception type. */
register __janus_exc_taken : bool
register __janus_exc_target_el : bits(2)
register __janus_exc_type : Exception
register __janus_exc_syndrome : bits(25)
register __janus_exc_vaddress : bits(64)

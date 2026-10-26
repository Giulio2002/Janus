import JanusASL.Proofs.Config

/-! # The configuration's IMPLEMENTATION DEFINED choices for floating point

Evaluated (`rfl`) from the generated `ImpDefBool`: every FP exception's trap is implemented, and
FPSCR.LEN/STRIDE are not RAZ (they are RES0 in AArch64 FPCR anyway). -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxRecDepth 100000 in
theorem impdef_fp_io (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_dz (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_of (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_uf (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_ix (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_id (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions").run s = .ok true s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_len (s : SState) : (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ").run s = .ok false s := rfl

set_option maxRecDepth 100000 in
theorem impdef_fp_sup (s : SState) : (__IMPDEF_boolean "Support trapping of floating-point exceptions").run s = .ok true s := rfl

end JanusASL.Proofs

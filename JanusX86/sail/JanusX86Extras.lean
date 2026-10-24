/- Lean definitions imported by the generated Sail x86 model (`--lean-import-file`,
docs/X86FORMAL.md). Only a `decreasing_trivial` extension: the measures of
termination_measures.sail decrease by integer arithmetic on the model's own helpers
(`lognot_int`, `Int.shiftr`, `floor2`), which `omega` (or, after a case split, `grind`) decides once they are unfolded. This
is a proof search only (no axiom, no `sorry`): a goal it cannot prove fails the build. -/
import Sail
import THE_MODULE_NAME.Defs
import THE_MODULE_NAME.SpecializationV1

open Sail

-- logcount_int (defined before floor2): its measure decreases through lognot_int / Int.shiftr
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (simp only [$(Lean.mkIdent `THE_MODULE_NAME.Functions.lognot_int):ident, Int.shiftr,
      Sail.Nat.iterate, beq_iff_eq, decide_eq_true_eq] at *
   omega))

-- logand_int: |floor2 i 2| < |i| for i ∉ {0, -1}
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (simp only [$(Lean.mkIdent `THE_MODULE_NAME.Functions.floor2):ident, Sail.Int.intAbs,
      beq_iff_eq, decide_eq_true_eq, Int.tdiv_eq_ediv, Int.tmod_eq_emod] at *
   split <;> grind))

namespace THE_MODULE_NAME.Functions

/-! The model's memory interface is Sail's old `regfp.sail` one (`__read_mem`, `__write_mem_ea`,
`__write_mem`, bound by name to `read_mem`, `write_mem_ea`, `write_mem`), which lean-sail does not
implement. The model only uses it from `memi`/`bang_memi`, one byte at a time. These are the
sequential-memory versions on lean-sail's byte map (`readBytes`/`writeBytes`, as
`sail_mem_read`/`sail_mem_write` of the newer interface): a read of a byte that is not in the
map throws `OutOfMemoryRange`. -/

def read_mem (_ : THE_MODULE_NAME.read_kind) (_ : Nat) (addr : BitVec w) (len : Nat) :
    THE_MODULE_NAME.SailM (BitVec (8 * len)) := do
  let (v, _) ← Sail.ConcurrencyInterfaceV1.PreSail.readBytes len addr.toNat
  pure v

def write_mem_ea (_ : THE_MODULE_NAME.write_kind) (_ : Nat) (_ : BitVec w) (_ : Nat) :
    THE_MODULE_NAME.SailM Unit := pure ()

def write_mem (_ : THE_MODULE_NAME.write_kind) (_ : Nat) (addr : BitVec w) (len : Nat)
    (v : BitVec (8 * len)) : THE_MODULE_NAME.SailM Bool :=
  Sail.ConcurrencyInterfaceV1.PreSail.writeBytes addr.toNat v

/-- Sail's `print_bits` (lean-sail has `prerr_bits` but not `print_bits`): output is not
modelled, as for lean-sail's `print_endline`. -/
def print_bits (_ : String) (_ : BitVec n) : Unit := ()

end THE_MODULE_NAME.Functions

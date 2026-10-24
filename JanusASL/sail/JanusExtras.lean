/- Lean definitions the sail-arm model binds by name (`--lean-import-file`). Adapted from
sail-arm's arm-v9.4-a/lean/ArmExtras.lean, minus its `decreasing_trivial` macro (whose last
resort was `sorry`): no generated definition needs a termination proof (docs/ASL.md). -/
import Sail
import THE_MODULE_NAME.Defs
import THE_MODULE_NAME.SpecializationV1

open Sail

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

def dec_str (x : Int) := x.repr
def hex_str (x : Int) := x.toHex

def putchar (_ : Int) : Unit := ()

def sleep_request (_ : Unit) : THE_MODULE_NAME.SailM Unit := pure ()
def wakeup_request (_ : Unit) : THE_MODULE_NAME.SailM Unit := pure ()

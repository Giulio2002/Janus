#!/usr/bin/env python3
"""Replace `integer_update_subrange` in the generated ArmASL.lean (scripts/asl.sh gen).

    sail_int_fix.py ARMASL_LEAN

Sail's library defines `integer_update_subrange(i, hi, lo, x)` (bits hi..lo of the integer i,
two's complement, replaced by x) through `set_slice_int(len, i, lo, x)`, and the Lean library's
`set_slice_int` (Sail.Common) first converts `i` to a bit vector of width `len`, the width of
`x`: every bit of `i` outside `lo .. lo+len-1`, and the bits below `lo`, are lost. Sail's C and
OCaml libraries update the integer in place. The only use in the Janus slice is FPRoundBase's
round-to-odd (`int_mant<0> = '1'`, FCVTXN), where the Lean result was 0 or -1 instead of the
mantissa with bit 0 set. The replacement is the arithmetic definition, with `/`, `%` the floor
division and the non-negative remainder of `Int` (so negative integers behave as infinite two's
complement):

    i - ((i / 2^lo) % 2^len) * 2^lo + x * 2^lo,   len = hi - lo + 1

janus-asl-check compares it on every FCVTXN case of the corpus.
"""
import sys

OLD = '''def integer_update_subrange (i : Int) (hi : Nat) (lo : Nat) (x : (BitVec (hi - lo + 1))) : Int :=
  (set_slice_int ((hi -i lo) +i 1) i lo x)
'''
NEW = '''-- JanusASL (JanusASL/sail/sail_int_fix.py): the Lean library's `set_slice_int` truncates `i` to
-- the width of `x`; update bits hi..lo of the two's-complement integer arithmetically instead.
def integer_update_subrange (i : Int) (hi : Nat) (lo : Nat) (x : (BitVec (hi - lo + 1))) : Int :=
  i - ((i / 2 ^ lo) % 2 ^ (hi - lo + 1)) * 2 ^ lo + (x.toNat : Int) * 2 ^ lo
'''
p = sys.argv[1]
t = open(p).read()
if t.count(OLD) != 1:
    sys.exit(f"sail_int_fix.py: expected one integer_update_subrange definition in {p}, found {t.count(OLD)}")
open(p, 'w').write(t.replace(OLD, NEW))

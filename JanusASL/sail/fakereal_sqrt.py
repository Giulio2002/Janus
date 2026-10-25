#!/usr/bin/env python3
"""Replace `sqrt_real` in the generated ArmASL/FakeReal.lean (scripts/asl.sh gen).

    fakereal_sqrt.py FAKEREAL_LEAN

The Sail toolchain's FakeReal.lean (sail-0.20.3-janus-lean-fixes.patch) defines `real` as `Rat`
and `sqrt_real` through `Float`, which is wrong for FSQRT once the scalar floating-point
instructions are in the slice. The square root of a rational is in general not rational; the
replacement is the round-to-odd approximation at absolute precision 2^-1100:

    sqrt_real x = m / 2^1100            if m^2 = x * 4^1100 (exact root)
                = (2m + 1) / 2^1101      otherwise
    where m = floor(sqrt(x * 4^1100))  (Nat.sqrt of floor(num * 4^1100 / den)), and 0 for x <= 0.

ASL's FPSqrt only calls `Sqrt` on positive finite values and passes the result to `FPRound`.
Every rounding boundary FPRound can test for binary16/32/64 (half-ULP multiples down to
2^-1075, the normal/subnormal thresholds, the overflow thresholds) is a multiple of 2^-1100, and
an inexact root lies strictly between m/2^1100 and (m+1)/2^1100, as does (2m+1)/2^1101; so
FPRound returns the same encoding and raises the same exceptions (inexact, underflow) as on
the exact root. This is how Janus' own FP core rounds square roots (round to odd).
"""
import re, sys

NEW = '''-- val sqrt = pure "sqrt_real" : real -> real
-- JanusASL (JanusASL/sail/fakereal_sqrt.py): round-to-odd at absolute precision 2^-1100, so
-- that FPRound of it equals FPRound of the exact square root for binary16/32/64.
def sqrt_real (x : real) : real :=
  if x ≤ 0 then 0 else
  let k : Nat := 1100
  let y : Nat := (x.num.toNat * 4 ^ k) / x.den
  let m : Nat := Nat.sqrt y
  if m * m * x.den = x.num.toNat * 4 ^ k then (m : Rat) / (2 ^ k : Nat)
  else ((2 * m + 1 : Nat) : Rat) / (2 ^ (k + 1) : Nat)
'''

p = sys.argv[1]
t = open(p).read()
pat = re.compile(r'-- val sqrt = pure "sqrt_real"[^\n]*\ndef sqrt_real \(x : real\) : real :=\n(?:  [^\n]*\n)+')
t2, n = pat.subn(NEW, t)
if n != 1:
    sys.exit(f"fakereal_sqrt.py: expected one sqrt_real definition in {p}, found {n}")
old_note = "Only `sqrt_real` has no exact\n   rational meaning; it is not reached by the Janus slice and is defined via Float."
if old_note in t2:
    t2 = t2.replace(old_note, "`sqrt_real` is the round-to-odd\n   approximation below (JanusASL/sail/fakereal_sqrt.py).")
open(p, 'w').write(t2)

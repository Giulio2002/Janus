#!/usr/bin/env python3
"""Instrument a sail-aarch64-oracle model.cpp to count CONSTRAINED UNPREDICTABLE events.

usage: instrument_model.py IN/model.cpp OUT/model.cpp

sail-arm stubs ConstrainUnpredictable*() with __UNKNOWN_*() (deterministically the first
enum value / false), and the crate's step_a64 turns a thrown Error_Unpredictable into an
UNDEFINED exception. Neither is the architecture, so a case that reaches either is not an
authoritative Sail answer. This adds one process-global counter

    extern "C" unsigned long long janus_sail_unpredictable;

incremented on entry to Model::zConstrainUnpredictable{,Bits,Integer} and in the
Error_Unpredictable exception constructor, and a second one

    extern "C" unsigned long long janus_sail_uncaught;

incremented in the Error_ConstrainedUnpredictable, Error_ImplementationDefined,
Error_ReservedEncoding and Error_SError constructors: these Sail exceptions are caught
by no handler on the A64 path (neither the model's nor the crate's step_a64), so the step
returns early with the instruction half-executed and the instance's have_exception flag set.
The driver reports such cases as errors and discards the instance. No other change:
semantics are untouched.
(ConstrainUnpredictableBool/Procedure are inlined away by Sail's optimiser and cannot be
counted; in A64 they occur only in SVE, debug and translation-table code.)
"""
import re
import sys

src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
n = 0
s = ('extern "C" { unsigned long long janus_sail_unpredictable = 0; '
     'unsigned long long janus_sail_uncaught = 0; }\n') + s
pat = re.compile(r'(static void zError_ConstrainedUnpredictable\(struct zexception \*rop, unit op\) \{\n)')
s, k = pat.subn(r'\1  ::janus_sail_unpredictable++;\n  ::janus_sail_uncaught++;\n', s)
assert k == 1, k
n += k
for kind, arg in (("ImplementationDefined", "const_sail_string"), ("ReservedEncoding", "unit"),
                  ("SError", "bool")):
    pat = re.compile(r'(static void zError_%s\(struct zexception \*rop, %s op\) \{\n)' % (kind, arg))
    s, k = pat.subn(r'\1  ::janus_sail_uncaught++;\n', s)
    assert k == 1, (kind, k)
    n += k
pat = re.compile(r'(static void zError_Unpredictable\(struct zexception \*rop, unit op\) \{\n)')
s, k = pat.subn(r'\1  ::janus_sail_unpredictable++;\n', s)
assert k == 1, k
n += k
# (Some Sail builds open function bodies with a GCC `__label__` declaration, which must stay first.)
pat = re.compile(r'(\n[^\n]*Model::zConstrainUnpredictable(?:Bits|Integer)?\([^\n]*\)\n\{\n(?:  __label__[^\n]*\n)?)')
s, k = pat.subn(r'\1  ::janus_sail_unpredictable++;\n', s)
assert k == 3, k
n += k
open(dst, "w").write(s)
print(f"instrumented {n} sites -> {dst}")

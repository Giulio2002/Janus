#!/usr/bin/env bash
# Test the runtime's software floating point (runtime.fadd64, fsub64, fmul64, fdiv64) against IEEE 754
# binary64 hardware arithmetic, on random operands of every class (zeros, subnormals, exponents
# near both ends of the range, infinities, NaNs), to justify the preconditions of the contracts
# Janus.Contracts.SoftFloat / SoftFloatAmd64 (docs/RUNTIME-CONTRACTS.md, "Soft float and
# KeepAlive"): outside the "tiny exact result" cases the runtime's result is the IEEE one (NaN for
# NaN), and inside them Go's addition is known not to be (it is checked that it differs).
#
#   SOFTCHECK_N   operand pairs per operation (default 400000; the measurement in the docs used 5000000)
#   GOTOOLCHAIN   default go1.26.0 (the release of scripts/build-examples*.sh)
#
# The functions are the runtime's own, reached by //go:linkname (-ldflags=-checklinkname=0).
# Usage: scripts/softfloat-check.sh
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export GOTOOLCHAIN="${GOTOOLCHAIN:-${JANUS_GO_TOOLCHAIN:-go1.26.0}}"
export PATH="$PATH:/usr/local/go/bin"
cd "$root/examples/rtmisc"
exec go test -count=1 -ldflags=-checklinkname=0 -v ./softcheck

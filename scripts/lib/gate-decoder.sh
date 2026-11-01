#!/usr/bin/env bash
# The janus-decode executable for a row script (audit/round10).
# Janus.Tools.Decode is not a framework module: every `janus ... --janus-root <checkout>` run drops its build outputs
# (changedModules, cmd/janus/framework.go - an extra module output in the pinned framework build is not trusted), and after the
# gate's pin lake is --no-build, so a row cannot `lake build janus-decode` in the gate. The gate's pre-lake therefore saves the
# decoder it has just built (gate_save_decoder -> audit/bin/janus-decode-gate, exactly as pre-rounds-bin saves janus), and a row
# under JANUS_GATE_PREBUILT=1 must use that exact binary and FAILS when it is missing (never a decoder of unknown age).
# Outside the gate a row builds it (lake build janus-decode).
#   gate_save_decoder ROOT        (gate pre-lake)   copy ROOT/.lake/build/bin/janus-decode to ROOT/audit/bin/janus-decode-gate
#   gate_decoder ROOT             print the path of the decoder to use; rc 1 + message on stderr if there is none
gate_save_decoder() {
  local root=$1 src="$1/.lake/build/bin/janus-decode"
  [ -x "$src" ] || { echo "gate: $src was not built" >&2; return 1; }
  mkdir -p "$root/audit/bin" && cp -f "$src" "$root/audit/bin/janus-decode-gate.new" && mv -f "$root/audit/bin/janus-decode-gate.new" "$root/audit/bin/janus-decode-gate"
}
gate_decoder() {
  local root=$1
  if [ "${JANUS_GATE_PREBUILT:-}" = 1 ]; then
    [ -x "$root/audit/bin/janus-decode-gate" ] || { echo "JANUS_GATE_PREBUILT=1 but audit/bin/janus-decode-gate (saved by the gate's pre-lake) is missing" >&2; return 1; }
    echo "$root/audit/bin/janus-decode-gate"
  else
    local lb; lb="$(cd "$root" && lake build janus-decode 2>&1)" || { echo "lake build janus-decode failed:" >&2; tail -30 <<<"$lb" >&2; return 1; }
    echo "$root/.lake/build/bin/janus-decode"
  fi
}

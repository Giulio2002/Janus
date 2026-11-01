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
# The copy is bound to the build and to the run: gate_save_decoder first REMOVES any earlier copy (and its stamp), copies, and
# writes audit/bin/janus-decode-gate.stamp = "<sha256 of the copy> <JANUS_GATE_RUN_ID>". gate_decoder (PREBUILT) accepts the copy only if
# the stamp's sha256 is the file's, the stamp's run id is this run's (JANUS_GATE_RUN_ID, exported by scripts/gate.sh; a copy left by an
# earlier gate run, of this or another commit, in the same tree has another id), and, while .lake/build/bin/janus-decode exists, it
# is byte-identical to it (janus runs may drop that file: then the stamp alone binds).
_gd_sha() { sha256sum "$1" | cut -d' ' -f1; }
gate_save_decoder() {
  local root=$1 src="$1/.lake/build/bin/janus-decode" d="$1/audit/bin"
  rm -f "$d/janus-decode-gate" "$d/janus-decode-gate.stamp" "$d/janus-decode-gate.new" 2>/dev/null
  [ -x "$src" ] || { echo "gate: $src was not built" >&2; return 1; }
  mkdir -p "$d" && cp -f "$src" "$d/janus-decode-gate.new" && mv -f "$d/janus-decode-gate.new" "$d/janus-decode-gate" &&
    printf '%s %s\n' "$(_gd_sha "$d/janus-decode-gate")" "${JANUS_GATE_RUN_ID:-norun}" > "$d/janus-decode-gate.stamp"
}
gate_decoder() {
  local root=$1
  if [ "${JANUS_GATE_PREBUILT:-}" = 1 ]; then
    local d="$root/audit/bin" want_sha want_run
    [ -x "$d/janus-decode-gate" ] || { echo "JANUS_GATE_PREBUILT=1 but audit/bin/janus-decode-gate (saved by the gate's pre-lake) is missing" >&2; return 1; }
    read -r want_sha want_run < "$d/janus-decode-gate.stamp" 2>/dev/null || { echo "audit/bin/janus-decode-gate has no stamp (not saved by this gate's pre-lake)" >&2; return 1; }
    [ "$want_sha" = "$(_gd_sha "$d/janus-decode-gate")" ] || { echo "audit/bin/janus-decode-gate does not match its stamp (replaced after it was saved)" >&2; return 1; }
    [ "$want_run" = "${JANUS_GATE_RUN_ID:-norun}" ] || { echo "audit/bin/janus-decode-gate is from another gate run ($want_run, this is ${JANUS_GATE_RUN_ID:-norun})" >&2; return 1; }
    if [ -e "$root/.lake/build/bin/janus-decode" ]; then
      cmp -s "$d/janus-decode-gate" "$root/.lake/build/bin/janus-decode" || { echo "audit/bin/janus-decode-gate differs from the current .lake/build/bin/janus-decode" >&2; return 1; }
    fi
    echo "$d/janus-decode-gate"
  else
    local lb; lb="$(cd "$root" && lake build janus-decode 2>&1)" || { echo "lake build janus-decode failed:" >&2; tail -30 <<<"$lb" >&2; return 1; }
    echo "$root/.lake/build/bin/janus-decode"
  fi
}

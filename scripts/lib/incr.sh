# shellcheck shell=bash
# The incremental merge gate, shell side (docs/TESTING.md "Incremental gate"). Sourced by the verify-*
# scripts and by scripts/gate.sh. The decision and the records are `bin/janus incr` (cmd/janus/incr.go).
#
# An item is SKIPPED only when `janus incr check` finds the record of a PASS whose key (a content hash
# of every input of the item: its extraction, proof file(s), the transitive import closure of its
# modules with their compiled data, the Lean toolchain, the verifier identity, the auditor and
# leanchecker, the pins, these scripts, the item's arguments and the relevant environment) equals the
# key of this run. Anything else -- no record, a damaged or foreign record, an input that cannot be
# hashed, any error -- runs the item.
#
#   JANUS_GATE_INCREMENTAL=1   skip items that have such a record (the default is a FULL run: nothing is
#                              skipped; the cold gate is mandatory before every push to main and nightly)
#   JANUS_INCR_RECORD=1        record the PASS of every item that runs (scripts/gate.sh and
#                              scripts/verify-all-examples.sh set it; implied by JANUS_GATE_INCREMENTAL=1)
#   JANUS_INCR_EXPLAIN=1       print the key components of each item and run nothing (gate.sh --explain)
#
#   incr_begin ID KIND SPEC...   returns 0 if the item must NOT run (skipped, or explain-only), with INCR_MSG
#                                the line(s) to print (it contains " skipped (unchanged", which the pool
#                                counts as a skipped item); 1 if it runs. Sets INCR_KEY. SPEC is `bin/janus incr` flags (--proof, --art, --pkg,
#                                --fw, --arg, ...); the gate scripts and libraries of KIND are added.
#   incr_end ID KIND RC SECS SPEC...   after the item ran: record a PASS (RC 0 and the inputs unchanged
#                                since incr_begin) or drop the record of a failed one.

incr_enabled() { [ "${JANUS_GATE_INCREMENTAL:-}" = 1 ]; }
incr_recording() { [ "${JANUS_INCR_RECORD:-}" = 1 ] || incr_enabled; }
incr_explaining() { [ "${JANUS_INCR_EXPLAIN:-}" = 1 ]; }
# JANUS_INCR_PRECHECK=1 (scripts/verify-all-examples.sh --incremental): the script is run only to find out
# whether its item is skipped; an item that is not exits with status 90 before running anything
incr_prechecking() { [ "${JANUS_INCR_PRECHECK:-}" = 1 ]; }
incr_active() { incr_enabled || incr_recording || incr_explaining; }

# the framework mode of the items that use the embedded framework (JANUS_ROOT selects a checkout)
incr_fw_embedded() { if [ -n "${JANUS_ROOT:-}" ]; then echo "--fw dir:$JANUS_ROOT"; else echo "--fw embedded"; fi; }

# the scripts and libraries that run an item of KIND, as --script flags (hashed by content)
incr_script_flags() {
  local kind=$1 f
  local -a fs=(scripts/gate.sh scripts/lib/incr.sh scripts/lib/pool.sh scripts/lib/parallel.sh scripts/lib/memguard.sh
    scripts/lib/itemtimeout.sh scripts/lib/theorems.sh scripts/verify-all-examples.sh scripts/example-contracts.sh
    scripts/example-targets.sh)
  case "$kind" in
    arm64) fs+=(scripts/verify-examples.sh scripts/build-examples.sh scripts/break-demo.sh) ;;
    amd64) fs+=(scripts/verify-amd64-examples.sh scripts/build-examples-amd64.sh) ;;
    asm) fs+=(scripts/verify-asm-examples.sh scripts/build-examples-asm.sh) ;;
    rtmisc) fs+=(scripts/verify-rtmisc-examples.sh scripts/build-examples-rtmisc.sh) ;;
    sys) fs+=(scripts/verify-sys-examples.sh scripts/build-examples-sys.sh) ;;
    print) fs+=(scripts/verify-print-examples.sh scripts/build-examples-print.sh scripts/gen-print-code.py scripts/gen-print-examples.py) ;;
    cgo) fs+=(scripts/verify-cgo-examples.sh scripts/build-examples-cgo.sh) ;;
    lane) fs+=(scripts/gotest-shards.sh scripts/ci-axiom-guard.sh scripts/x86formal.sh scripts/asl.sh audit/run-rounds.sh audit/rt-asl/run.sh) ;;
  esac
  for f in "${fs[@]}"; do printf '%s\n' --script "$f"; done
}

# the pins: the stub pins (also compiled into the verifier) and their generator
incr_pin_flags() { printf '%s\n' --pin cmd/janus/stubpins_gen.go --pin scripts/gen-stubpins.sh --pin scripts/stubpins/main.go; }

INCR_KEY=""
INCR_STARTED=""
INCR_MSG=""

incr_begin() { # ID KIND SPEC...
  local id=$1 kind=$2 out rc=0
  shift 2
  INCR_KEY=""; INCR_MSG=""; INCR_STARTED=$(date +%s.%N)
  if ! incr_active || [ ! -x bin/janus ]; then ! incr_prechecking || exit 90; return 1; fi
  local -a flags=()
  mapfile -t flags < <(incr_script_flags "$kind"; incr_pin_flags)
  if incr_explaining; then
    INCR_MSG="$(bin/janus incr explain --id "$id" --kind "$kind" "$@" "${flags[@]}" 2>&1 || true)
$id  skipped (unchanged: --explain only; nothing was verified)"
    return 0
  fi
  out="$(bin/janus incr check --id "$id" --kind "$kind" "$@" "${flags[@]}" 2>/dev/null)" || rc=$?
  if [ "$rc" != 0 ]; then ! incr_prechecking || exit 90; return 1; fi
  local verdict key f3 f4 f5 f6
  IFS=$'\t' read -r verdict key f3 f4 f5 f6 <<<"$out"
  case "$key" in [0-9a-f]*) INCR_KEY=$key ;; esac
  [ "${#INCR_KEY}" = 64 ] || INCR_KEY=""
  if [ "$verdict" = SKIP ] && [ -n "$INCR_KEY" ] && incr_enabled; then
    # ' skipped (unchanged' is the marker scripts/lib/pool.sh counts as a skipped (not run) item
    local this=""
    # a PASS recorded since this gate run began was recorded by its own prebuild warm-up (a verification of Add
    # with the freshly built binary): legitimate, and labelled
    if [ -n "${JANUS_GATE_T0:-}" ] && [ "$(date -u -d "$f3" +%s 2>/dev/null || echo 0)" -ge "${JANUS_GATE_T0%.*}" ]; then
      this="recorded this run by prebuild; "
    fi
    printf -v INCR_MSG '%s  skipped (unchanged: incremental; %srecorded PASS of %s on %s at %s, %ss then; key %s)' \
      "$id" "$this" "$f3" "$f4" "$f5" "$f6" "${INCR_KEY:0:12}"
    return 0
  fi
  ! incr_prechecking || exit 90
  return 1
}

incr_end() { # ID KIND RC SECS SPEC...
  local id=$1 kind=$2 rc=$3 secs=$4
  shift 4
  incr_recording || return 0
  [ -x bin/janus ] || return 0
  local -a flags=()
  mapfile -t flags < <(incr_script_flags "$kind"; incr_pin_flags)
  bin/janus incr record --id "$id" --kind "$kind" --rc "$rc" --wall "$secs" --pre-key "$INCR_KEY" \
    --started "${INCR_STARTED:-}" "$@" "${flags[@]}" 2>/dev/null | sed -n 's/^NOTRECORDED\t/incr: not recorded: /p' || true
  return 0
}

# incr_report POOLDIR ITEM...: one line per item, RAN (with its wall time) or SKIPPED (with the time, host
# and commit of the PASS it replays), then the totals. An item is SKIPPED if its log holds the marker line.
incr_report() {
  local dir=$1 it f ran=0 skipped=0 failed=0 line secs w
  shift
  echo "---- incremental report: every item RAN or was SKIPPED ----"
  for it in "$@"; do
    f="${it//\//_}"; f="${f//:/_}"
    line="$(grep -m1 ' skipped (unchanged' "$dir/$f.log" 2>/dev/null || true)"
    if [ -n "$line" ]; then
      skipped=$((skipped + 1))
      printf 'SKIPPED %-34s %s\n' "$it" "${line#*skipped (unchanged: }"
    elif [ -f "$dir/$f.rc" ]; then
      ran=$((ran + 1)); secs="$(cat "$dir/$f.secs" 2>/dev/null || echo 0)"
      w="$(awk -v s="$secs" 'BEGIN { printf "%.1f", s }')"
      if [ "$(cat "$dir/$f.rc")" = 0 ]; then printf 'RAN     %-34s %ss\n' "$it" "$w"
      else failed=$((failed + 1)); printf 'RAN     %-34s %ss  (FAILED, rc %s)\n' "$it" "$w" "$(cat "$dir/$f.rc")"; fi
    else
      printf 'NOT RUN %-34s (no result: counted as a failure by the pool)\n' "$it"
    fi
  done
  echo "incremental totals: $# items, $ran RAN ($failed failed), $skipped SKIPPED$([ "${JANUS_GATE_INCREMENTAL:-}" = 1 ] || echo '  (full run: nothing is skipped)')"
}

# incr_lane NAME CODE [SPEC...]: a whole gate lane (go test, the audit rounds, x86formal, a rt-asl group). Its key is
# every non-documentation file of the working tree, the toolchain, the full verifier identity (Go and Lean), the
# machine, the relevant environment, the prebuilt example binaries and the lane's arguments (SPEC). CODE is shell
# code (eval'd here); a lane is skipped only on the record of a PASS with that key, and recorded when it passes.
incr_lane() {
  local name=$1 code=$2 rc=0 t0 secs f
  shift 2
  if ! incr_active; then eval "$code"; return $?; fi
  local -a spec=(--no-fw --full-verifier --host --tree . --tree-exclude docs/ --tree-exclude assets/ --tree-exclude '*.md'
    --tree-exclude LICENSE --tree-exclude artifacts/ "$@" --arg "lane:$name" --arg "go:$(go version 2>/dev/null)" --file docs/SOUNDNESS.md)
  # the prebuilt binaries every lane reads
  for f in artifacts/examples-*; do [ ! -f "$f" ] || spec+=(--file "$f"); done
  if incr_begin "lane:$name" lane "${spec[@]}"; then echo "$INCR_MSG"; return 0; fi
  t0=$(date +%s.%N)
  ( eval "$code" ) || rc=$?
  secs=$(echo "$(date +%s.%N) - $t0" | bc)
  incr_end "lane:$name" lane "$rc" "$secs" "${spec[@]}"
  return $rc
}

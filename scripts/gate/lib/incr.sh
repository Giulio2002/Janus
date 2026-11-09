# shellcheck shell=bash
# The incremental merge gate, shell side (docs/TESTING.md "Incremental gate"). Sourced by the verify-*
# scripts and by scripts/gate/gate.sh. The decision and the records are `bin/janus incr` (cmd/janus/incr.go).
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
#   JANUS_INCR_RECORD=1        record the PASS of every item that runs (scripts/gate/gate.sh and
#                              scripts/verify/verify-all-examples.sh set it; implied by JANUS_GATE_INCREMENTAL=1)
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
# JANUS_INCR_PRECHECK=1 (scripts/verify/verify-all-examples.sh --incremental): the script is run only to find out
# whether its item is skipped; an item that is not exits with status 90 before running anything
incr_prechecking() { [ "${JANUS_INCR_PRECHECK:-}" = 1 ]; }
incr_active() { incr_enabled || incr_recording || incr_explaining; }

# the framework mode of the items that use the embedded framework (JANUS_ROOT selects a checkout)
incr_fw_embedded() { if [ -n "${JANUS_ROOT:-}" ]; then echo "--fw dir:$JANUS_ROOT"; else echo "--fw embedded"; fi; }

# the scripts and libraries that run an item of KIND, as --script flags (hashed by content)
incr_script_flags() {
  local kind=$1 f
  local -a fs=(scripts/gate/gate.sh scripts/gate/lib/incr.sh scripts/gate/lib/pool.sh scripts/gate/lib/parallel.sh scripts/gate/lib/incr-host.sh scripts/gate/lib/memguard.sh
    scripts/gate/lib/itemtimeout.sh scripts/gate/lib/theorems.sh scripts/verify/verify-all-examples.sh scripts/verify/example-contracts.sh
    scripts/verify/example-targets.sh)
  case "$kind" in
    arm64) fs+=(scripts/verify/verify-examples.sh scripts/build/build-examples.sh scripts/archive/break-demo.sh) ;;
    amd64) fs+=(scripts/verify/verify-amd64-examples.sh scripts/build/build-examples-amd64.sh) ;;
    asm) fs+=(scripts/verify/verify-asm-examples.sh scripts/build/build-examples-asm.sh) ;;
    rtmisc) fs+=(scripts/verify/verify-rtmisc-examples.sh scripts/build/build-examples-rtmisc.sh) ;;
    sys) fs+=(scripts/verify/verify-sys-examples.sh scripts/build/build-examples-sys.sh) ;;
    print) fs+=(scripts/verify/verify-print-examples.sh scripts/build/build-examples-print.sh scripts/dev/gen-print-code.py scripts/dev/gen-print-examples.py) ;;
    cgo) fs+=(scripts/verify/verify-cgo-examples.sh scripts/build/build-examples-cgo.sh) ;;
    lane) fs+=(scripts/gate/gotest-shards.sh scripts/gate/ci-axiom-guard.sh scripts/build/x86formal.sh scripts/build/asl.sh test/redteam/run-rounds.sh test/redteam/rounds/rt-asl/run.sh) ;;
  esac
  for f in "${fs[@]}"; do printf '%s\n' --script "$f"; done
}

# the pins: the stub pins (also compiled into the verifier) and their generator
incr_pin_flags() { printf '%s\n' --pin cmd/janus/stubpins_gen.go --pin scripts/dev/gen-stubpins.sh --pin scripts/dev/stubpins/main.go; }

# ---- the tree pin: records are written only for a run of a CLEAN tree that did not change while it ran.
# A key is computed from the live tree, but some items verify a copy made earlier (the print snapshot, the
# isolated lake trees of the lane copies): an edit between the copy and the key would record a PASS of
# content that was never verified. So a record needs (a) a clean git tree (no tracked change, no untracked
# non-ignored file) when the gate started, and (b) the same tree stamp (path, size, mtime, ctime, inode of every
# non-ignored file, and HEAD) when the record is written. Skipping does not need it (a skip is for the exact
# content the key names).
incr_tree_stamp() {
  {
    git rev-parse HEAD 2>/dev/null
    git ls-files -z -c -o --exclude-standard 2>/dev/null | grep -zv -e '\.pyc$' -e '__pycache__/' |
      xargs -0 -r stat -c '%n %s %.9Y %.9Z %i' 2>/dev/null
  } | sha256sum | cut -d' ' -f1
}
incr_tree_clean() {
  git rev-parse --git-dir >/dev/null 2>&1 || return 1
  [ -z "$(git status --porcelain --untracked-files=all 2>/dev/null | grep -v -e '\.pyc$' -e '__pycache__/')" ]
}
# _incr_is_gate_proc PID: PID is a real gate: its executable is a shell (readlink /proc/PID/exe), it has the uid of this process, argv is
# <shell> [options without -c/-s/--command] <script> ..., and the FIRST non-option argument, resolved against that process's cwd and symlinks, is
# exactly <this checkout>/scripts/gate/gate.sh (the checkout that holds the incr.sh that is running: a gate.sh anywhere else, text inside a `bash -c`
# string, `bash -s gate.sh`, a later argument, another user's process: all rejected).
_incr_is_gate_proc() {
  local pid=$1 exe uid av=() i a want sp
  exe="$(readlink -f "/proc/$pid/exe" 2>/dev/null)" || return 1
  [[ "$exe" =~ /(bash|sh|dash)$ ]] || return 1
  uid="$(stat -c %u "/proc/$pid" 2>/dev/null)" || return 1
  [ "$uid" = "$(id -u)" ] || return 1
  want="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." 2>/dev/null && pwd -P)/scripts/gate/gate.sh"
  mapfile -d '' -t av < "/proc/$pid/cmdline" 2>/dev/null || true
  [ "${#av[@]}" -ge 2 ] || return 1
  for ((i = 1; i < ${#av[@]}; i++)); do
    a="${av[i]}"
    case "$a" in
      --) i=$((i + 1)); a="${av[i]-}"; break ;;
      -c|-s|-[!-]*c*|-[!-]*s*|--command) return 1 ;;
      -o|-O|--rcfile|--init-file) i=$((i + 1)) ;;
      -*) ;;
      *) break ;;
    esac
  done
  [ -n "${a:-}" ] && [ "${a#-}" = "$a" ] || return 1
  case "$a" in /*) sp="$(readlink -f -- "$a" 2>/dev/null)" ;; *) sp="$(readlink -f -- "/proc/$pid/cwd/$a" 2>/dev/null)" ;; esac
  [ "$sp" = "$want" ]
}
# incr_under_gate: true only when the real scripts/gate/gate.sh of THIS checkout is an ancestor PROCESS of this shell.
# JANUS_GATE_TREE0 is the stamp the gate takes at its start: only scripts/gate/gate.sh may set it. An operator with a dirty tree who exported a
# matching stamp would make incr_tree_ok true and get PASS records written for content that was never verified, so
# scripts/verify/verify-all-examples.sh run by itself clears it (and pins the tree itself); under the gate it keeps the gate's. An environment
# variable cannot say who set it, a process ancestry (verified by exe, uid, cwd-resolved script path) can.
incr_under_gate() {
  local pid=$$ i
  for i in $(seq 1 64); do
    [ "$pid" -gt 1 ] 2>/dev/null || return 1
    _incr_is_gate_proc "$pid" && return 0
    pid="$(sed 's/^.*) //' "/proc/$pid/stat" 2>/dev/null | awk '{ print $2 }')" || return 1  # (the comm field may hold spaces)
  done
  return 1
}
# incr_tree_pin: call once, at the start of a gate (scripts/gate/gate.sh, scripts/verify/verify-all-examples.sh); idempotent
incr_tree_pin() {
  [ -z "${JANUS_GATE_TREE0:-}" ] || return 0
  if incr_tree_clean; then JANUS_GATE_TREE0=$(incr_tree_stamp); else JANUS_GATE_TREE0=dirty; fi
  export JANUS_GATE_TREE0
}
incr_tree_ok() {
  [ -n "${JANUS_GATE_TREE0:-}" ] && [ "$JANUS_GATE_TREE0" != dirty ] && [ "$(incr_tree_stamp)" = "$JANUS_GATE_TREE0" ]
}

INCR_KEY=""
INCR_STARTED=""
INCR_MSG=""

incr_begin() { # ID KIND SPEC...
  local id=$1 kind=$2 out rc=0
  shift 2
  INCR_KEY=""; INCR_MSG=""; INCR_STARTED=$(date +%s.%N)
  if ! incr_active || [ ! -x bin/janus ]; then ! incr_prechecking || exit 90; return 1; fi
  # an item that compiles at run time (cgo) is keyed by the host compiler/linker/libc too (incr_hosttools); the value is kept for incr_end
  INCR_HT=""
  if [ "$kind" = cgo ]; then INCR_HT="$(incr_hosttools)"; set -- "$@" --arg "hosttools:$INCR_HT"; fi
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
    # ' skipped (unchanged' is the marker scripts/gate/lib/pool.sh counts as a skipped (not run) item
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
  if [ "$kind" = cgo ] && [ -n "${INCR_HT:-}" ]; then set -- "$@" --arg "hosttools:$INCR_HT"; fi
  # a record needs a clean tree that did not change since the gate started (see incr_tree_pin)
  if [ "$rc" = 0 ] && ! incr_tree_ok; then
    echo "incr: not recorded: the working tree was dirty when the gate started or changed while it ran (a record must describe what was verified)"
    return 0
  fi
  # B5: the host-tool digest is recomputed from scratch (no cache) and must equal the value the key was computed with, else nothing is recorded
  local ha now
  for ha in "$@"; do
    case "$ha" in hosttools:*) now="hosttools:$(incr_hosttools --nocache)"
      if [ "$ha" != "$now" ] || ! [[ "$now" =~ ^hosttools:tools=[0-9a-f]{64} ]]; then echo "incr: not recorded: the host build tools changed (or could not be hashed) while the run was in progress"; return 0; fi ;;
    esac
  done
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
# incr_lane_spec NAME [SPEC...]: the key arguments of a lane, one per line (incr_lane, scripts/gate/lib/test-incr-liveness.sh). An argument
# is one line (`janus incr` refuses a newline): multi-line values (go env -json, the GOENV file) have each newline replaced by \001,
# which is injective (_incr_oneline escapes \\001 and \\002 first). `go env -json` also holds GOGCCFLAGS with a RANDOM directory (-ffile-prefix-map=/tmp/go-build<random>=...), different on every
# call: only the value of GOGCCFLAGS is normalised (a random directory, /go-build<digits>), or every gate run would key its lanes differently. (Until this was fixed `go env -json` made every lane's `janus incr check` fail: no lane was ever skipped or recorded.)
. "$(dirname "${BASH_SOURCE[0]}")/incr-host.sh"
# _incr_oneline: a value as ONE line, injectively: \002 -> \002 2, \001 -> \002 1, newline -> \001 (the three never collide)
_incr_oneline() { local v; v="$(cat)"; v="${v//$'\002'/$'\0022'}"; v="${v//$'\001'/$'\0021'}"; printf '%s' "${v//$'\n'/$'\001'}"; }
incr_lane_spec() {
  local name=$1 gw f
  shift
  local -a spec=(--no-fw --full-verifier --host --tree . --tree-exclude docs/ --tree-exclude assets/ --tree-exclude '*.md'
    --tree-exclude LICENSE --tree-exclude artifacts/ "$@" --arg "lane:$name" --arg "go:$(go version 2>/dev/null | _incr_oneline)" --file docs/SOUNDNESS.md
    # the Go configuration the lane builds under: GOENV/GOMODCACHE are not in the environment part of the key,
    # so its settings (the go env file can set GOFLAGS, tags, GOEXPERIMENT...), the file and go.work are keyed here
    --arg "goenv:$(go env -json 2>/dev/null | sed -E '/"GOGCCFLAGS"/ s#/go-build[0-9]+#/go-build#g' | _incr_oneline)" --arg "goenvfile:$(cat "$(go env GOENV 2>/dev/null)" 2>/dev/null | _incr_oneline)"
    # the host C/C++ compiler, linker, loader and libc the lane compiles and links with (every lane: conservative, ~0.3 s once per gate run)
    --arg "hosttools:$(incr_hosttools)")
  gw="$(go env GOWORK 2>/dev/null)"
  if [ -n "$gw" ] && [ "$gw" != off ]; then spec+=(--file "$gw"); [ ! -f "$gw.sum" ] || spec+=(--file "$gw.sum"); fi
  # the prebuilt binaries every lane reads
  for f in artifacts/examples-*; do [ ! -f "$f" ] || spec+=(--file "$f"); done
  printf '%s\n' "${spec[@]}"
}
incr_lane() {
  local name=$1 code=$2 rc=0 t0 secs
  shift 2
  # lane-level skipping/recording is OFF unless JANUS_INCR_LANES=1 (an explicit opt-in until the lane key is cleared by a further red team):
  # by default every lane always runs, no record is read or written for it
  if ! incr_active || [ "${JANUS_INCR_LANES:-}" != 1 ]; then eval "$code"; return $?; fi
  local -a spec=()
  mapfile -t spec < <(incr_lane_spec "$name" "$@")
  if incr_begin "lane:$name" lane "${spec[@]}"; then echo "$INCR_MSG"; return 0; fi
  t0=$(date +%s.%N)
  INCR_NORECORD_FILE="$(mktemp "${TMPDIR:-/tmp}/incr-norecord.XXXXXX")" && export INCR_NORECORD_FILE || unset INCR_NORECORD_FILE
  ( eval "$code" ) || rc=$?
  secs=$(echo "$(date +%s.%N) - $t0" | bc)
  if [ -n "${INCR_NORECORD_FILE:-}" ] && [ -s "$INCR_NORECORD_FILE" ]; then
    echo "incr: lane $name not recorded: $(head -c 300 "$INCR_NORECORD_FILE")"; rm -f "$INCR_NORECORD_FILE"; unset INCR_NORECORD_FILE
    return $rc
  fi
  rm -f "${INCR_NORECORD_FILE:-}"; unset INCR_NORECORD_FILE
  incr_end "lane:$name" lane "$rc" "$secs" "${spec[@]}"
  return $rc
}

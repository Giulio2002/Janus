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
# _incr_argv_is_gate PID: argv is <shell> [options without -c] <script>.gate.sh ...: the FIRST non-option argument is the script (text inside a
# `bash -c '...'` string, or a later argument, does not count: an operator cannot fake the ancestry by naming gate.sh somewhere in a command line)
_incr_argv_is_gate() {
  local -a av=(); local i a
  mapfile -d '' -t av < "/proc/$1/cmdline" 2>/dev/null || true
  [ "${#av[@]}" -ge 2 ] || return 1
  [[ "${av[0]}" =~ (^|/)(bash|sh|dash)$ ]] || return 1
  for ((i = 1; i < ${#av[@]}; i++)); do
    a="${av[i]}"
    case "$a" in
      --) i=$((i + 1)); a="${av[i]-}"; [[ "$a" =~ (^|/)gate\.sh$ ]]; return ;;
      -c|-[!-]*c*|--command) return 1 ;;
      -o|-O|--rcfile|--init-file) i=$((i + 1)) ;;
      -*) ;;
      *) [[ "$a" =~ (^|/)gate\.sh$ ]]; return ;;
    esac
  done
  return 1
}
# incr_under_gate: true only when scripts/gate.sh is an ANCESTOR process of this shell (its argv names a script called gate.sh run by a shell).
# JANUS_GATE_TREE0 is the stamp the gate takes at its start: only scripts/gate.sh may set it. An operator with a dirty tree who exported a
# matching stamp would make incr_tree_ok true and get PASS records written for content that was never verified, so
# scripts/verify-all-examples.sh run by itself clears it (and pins the tree itself); under the gate it keeps the gate's. An environment
# variable cannot say who set it, a process ancestry can.
incr_under_gate() {
  local pid=$$ i a
  for i in $(seq 1 64); do
    [ "$pid" -gt 1 ] 2>/dev/null || return 1
    if [ -r "/proc/$pid/cmdline" ] && _incr_argv_is_gate "$pid"; then return 0; fi
    pid="$(sed 's/^.*) //' "/proc/$pid/stat" 2>/dev/null | awk '{ print $2 }')" || return 1  # (the comm field may hold spaces)
  done
  return 1
}
# incr_tree_pin: call once, at the start of a gate (scripts/gate.sh, scripts/verify-all-examples.sh); idempotent
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
  # a record needs a clean tree that did not change since the gate started (see incr_tree_pin)
  if [ "$rc" = 0 ] && ! incr_tree_ok; then
    echo "incr: not recorded: the working tree was dirty when the gate started or changed while it ran (a record must describe what was verified)"
    return 0
  fi
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
# incr_lane_spec NAME [SPEC...]: the key arguments of a lane, one per line (incr_lane, scripts/lib/test-incr-liveness.sh). An argument
# is one line (`janus incr` refuses a newline): multi-line values (go env -json, the GOENV file) have each newline replaced by \001,
# which is injective. `go env -json` also holds GOGCCFLAGS with a RANDOM directory (-ffile-prefix-map=/tmp/go-build<random>=...), different on every
# call: it is normalised, or every gate run would key its lanes differently. (Until this was fixed `go env -json` made every lane's `janus incr check` fail: no lane was ever skipped or recorded.)
# incr_hosttools: ONE line naming the host build tools and the dynamic loader a lane's C/C++ compile and link (and every tool it starts) run
# with: SHA-256 of each resolved (symlinks followed) binary of cc gcc g++ c++ clang clang++ ld ld.bfd ld.gold ld.lld as ar, of $CC/$CXX/go env CC CXX,
# of what the compiler itself names (-print-prog-name: cc1 cc1plus as ld collect2 lto-wrapper), the `--version` texts, the SHA-256 of the dynamic
# loader (/lib*/ld-linux-*) and of the libc it resolves, found via the same PATH the lane uses. A tool that is not found is recorded as absent
# (that IS a difference). LD_PRELOAD / LD_LIBRARY_PATH are NOT cached and are conservative: a non-empty value is keyed with the SHA-256 of
# every file it names (LD_LIBRARY_PATH: of every regular file below each directory, names included); anything unreadable keys a random value, i.e. a
# forced miss. The binary part is computed once per gate run (INCR_HOSTTOOLS_CACHE, a private file set by scripts/gate.sh; stamped with PATH/CC/CXX).
_incr_h() { # PATH-of-file: "<sha256>" of the file with symlinks resolved, or "absent"
  local f r
  f="$1"; r="$(readlink -f -- "$f" 2>/dev/null)" || { echo absent; return; }
  [ -f "$r" ] && sha256sum -- "$r" 2>/dev/null | cut -c1-64 || echo absent
}
_incr_hosttools_bins() {
  local n p ccw cxw out cc0 cx0
  cc0="${CC-}"; cx0="${CXX-}"
  ccw="$(go env CC 2>/dev/null)"; cxw="$(go env CXX 2>/dev/null)"
  for n in cc gcc g++ c++ clang clang++ ld ld.bfd ld.gold ld.lld as ar "${cc0%% *}" "${cx0%% *}" "${ccw%% *}" "${cxw%% *}"; do
    [ -n "$n" ] || continue
    p="$(type -P -- "$n" 2>/dev/null)" || p=""
    if [ -n "$p" ]; then echo "tool $n $(readlink -f -- "$p") $(_incr_h "$p")"; else echo "tool $n absent"; fi
  done
  for n in gcc g++ clang; do
    p="$(type -P -- "$n" 2>/dev/null)" || continue
    for q in cc1 cc1plus as ld collect2 lto-wrapper; do
      out="$("$p" -print-prog-name=$q 2>/dev/null)"; [ -n "$out" ] || continue
      [ "${out#/}" != "$out" ] || out="$(type -P -- "$out" 2>/dev/null)"
      echo "prog $n $q $(readlink -f -- "$out" 2>/dev/null) $(_incr_h "${out:-/nonexistent}")"
    done
    echo "ver $n $("$p" --version 2>&1 | tr '\n' ' ')"
  done
  for n in ld as ar; do p="$(type -P -- "$n" 2>/dev/null)" && echo "ver $n $("$p" --version 2>&1 | head -n 1)"; done
  for p in /lib64/ld-linux-*.so.* /lib/ld-linux-*.so.* /lib/*-linux-gnu/ld-linux-*.so.* /lib/*-linux-gnu/libc.so.6 /lib64/libc.so.6; do
    [ -e "$p" ] && echo "ldso $(readlink -f -- "$p") $(_incr_h "$p")"
  done
  p="$(type -P -- janus 2>/dev/null || echo bin/janus)"
  ldd "$p" 2>/dev/null | awk '$1 ~ /libc\.so|ld-linux/ { print $(NF-1) }' | while read -r q; do [ -e "$q" ] && echo "ldd $(readlink -f -- "$q") $(_incr_h "$q")"; done
}
incr_hosttools() {
  local envh c line="" w q f
  envh="$(printf '%s\0' "$PATH" "${CC-}" "${CXX-}" | sha256sum | cut -c1-64)"
  c="${INCR_HOSTTOOLS_CACHE:-}"
  if [ -n "$c" ] && [ -s "$c" ] && [ "$(head -n 1 "$c")" = "$envh" ]; then line="$(sed -n 2p "$c")"; fi
  if [ -z "$line" ]; then
    line="$(_incr_hosttools_bins 2>/dev/null | LC_ALL=C sort | sha256sum | cut -c1-64)"
    [ -z "$c" ] || [ ! -w "$c" ] || printf '%s\n%s\n' "$envh" "$line" > "$c"
  fi
  w=""
  if [ -n "${LD_PRELOAD:-}" ]; then
    w+="preload=${LD_PRELOAD}"
    for q in ${LD_PRELOAD//:/ }; do
      if [ -f "$q" ] && [ -r "$q" ]; then w+=" $(_incr_h "$q")"; else w+=" unresolved-$RANDOM$RANDOM$RANDOM"; fi
    done
  fi
  if [ -n "${LD_LIBRARY_PATH:-}" ]; then
    w+=" libpath=${LD_LIBRARY_PATH}"
    for q in ${LD_LIBRARY_PATH//:/ }; do
      if [ -d "$q" ]; then w+=" $(cd "$q" 2>/dev/null && find . -type f -print0 2>/dev/null | LC_ALL=C sort -z | xargs -0 -r sha256sum 2>/dev/null | sha256sum | cut -c1-16)"
      elif [ -e "$q" ]; then w+=" unresolved-$RANDOM$RANDOM$RANDOM"; else w+=" nodir"; fi
    done
  fi
  printf 'tools=%s%s\n' "$line" "$w"
}
incr_lane_spec() {
  local name=$1 gw f
  shift
  local -a spec=(--no-fw --full-verifier --host --tree . --tree-exclude docs/ --tree-exclude assets/ --tree-exclude '*.md'
    --tree-exclude LICENSE --tree-exclude artifacts/ "$@" --arg "lane:$name" --arg "go:$(go version 2>/dev/null | tr '\n' '\001')" --file docs/SOUNDNESS.md
    # the Go configuration the lane builds under: GOENV/GOMODCACHE are not in the environment part of the key,
    # so its settings (the go env file can set GOFLAGS, tags, GOEXPERIMENT...), the file and go.work are keyed here
    --arg "goenv:$(go env -json 2>/dev/null | sed -E 's#/go-build[0-9]+#/go-build#g' | tr '\n' '\001')" --arg "goenvfile:$(cat "$(go env GOENV 2>/dev/null)" 2>/dev/null | tr '\n' '\001')"
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
  if ! incr_active; then eval "$code"; return $?; fi
  local -a spec=()
  mapfile -t spec < <(incr_lane_spec "$name" "$@")
  if incr_begin "lane:$name" lane "${spec[@]}"; then echo "$INCR_MSG"; return 0; fi
  t0=$(date +%s.%N)
  ( eval "$code" ) || rc=$?
  secs=$(echo "$(date +%s.%N) - $t0" | bc)
  incr_end "lane:$name" lane "$rc" "$secs" "${spec[@]}"
  return $rc
}

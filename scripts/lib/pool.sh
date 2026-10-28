# shellcheck shell=bash
# One global work queue with streamed results, shared by the gate (scripts/gate.sh), the example
# runner (scripts/verify-all-examples.sh) and anything else that has a list of independent items.
# Source it AFTER scripts/lib/parallel.sh (admission by memory) and, for per-item cgroup memory
# limits, scripts/lib/memguard.sh.
#
#   pool_init NAME JOBS STATEDIR   NAME labels the pool in progress lines and the timeline; JOBS is the
#                                  number of items at once; STATEDIR receives <id>.log / .rc / .secs
#                                  (full per-item logs are kept there).
#   pool_times FILE                longest-first order from the walls recorded in FILE ("ID<TAB>seconds");
#                                  an item without a recorded wall goes first (it may be the longest).
#   pool_add ID CODE [COSTKEY]     queue an item: CODE is shell code run in a subshell (it sees the
#                                  functions and variables defined so far); its exit status is the
#                                  item's verdict. COSTKEY (default ID) is the key into the times file.
#   pool_run                       run the queue to the end. Each item's result line (PASS / FAIL /
#                                  TIMEOUT / MISSING + wall seconds) is printed the moment it finishes, a
#                                  progress line (done/total, the running items with elapsed time) every
#                                  $POOL_PROGRESS_SECS (default 60) seconds. Returns 1 if any item did
#                                  not pass (a missing result counts as a failure); POOL_FAILED holds the ids.
#
# Environment: POOL_TIMELINE=FILE appends one JSON line per finished item (and one per pool);
# POOL_PROGRESS_SECS; POOL_MEM_HEADROOM_KB / POOL_JOB_MEM_KB (admission, default as parallel.sh).
# A finished item whose log has a line starting "TIMEOUT:" (scripts/lib/itemtimeout.sh) or whose status
# is 124 is reported as TIMEOUT. An item whose log contains " skipped (unchanged" is reported SKIP
# (a pass that did not run: --changed) and does not update the times.

pool_init() {
  POOL_NAME="$1"; POOL_JOBS="$2"; POOL_DIR="$3"
  POOL_IDS=(); POOL_CODES=(); POOL_KEYS=(); POOL_FAILED=()
  declare -gA POOL_SECS=()
  mkdir -p "$POOL_DIR"
  POOL_PROGRESS_SECS="${POOL_PROGRESS_SECS:-60}"
}

pool_times() { # FILE
  [ -f "$1" ] || return 0
  local k v
  while IFS=$'\t' read -r k v; do POOL_SECS[$k]=$v; done < "$1"
}

pool_add() { # ID CODE [COSTKEY]
  POOL_IDS+=("$1"); POOL_CODES+=("$2"); POOL_KEYS+=("${3:-$1}")
}

_pool_file() { local f="${1//\//_}"; echo "${f//:/_}"; }
_pool_now() { date +%s.%N; }
_pool_fmt() { # seconds -> 1h02m03s / 5m07s / 12.3s
  awk -v s="$1" 'BEGIN { if (s >= 3600) printf "%dh%02dm%02ds", s/3600, (s%3600)/60, s%60;
    else if (s >= 60) printf "%dm%02ds", s/60, s%60; else printf "%.1fs", s }'
}
_pool_json() { # minimal JSON string escape
  local s=${1//\\/\\\\}; s=${s//\"/\\\"}; printf '%s' "$s"
}

_pool_spawn() { # INDEX
  local i=$1 id f log rc
  id="${POOL_IDS[$i]}"; f="$(_pool_file "$id")"
  log="$POOL_DIR/$f.log"; rc="$POOL_DIR/$f.rc"
  rm -f "$rc" "$POOL_DIR/$f.secs"
  POOL_T0[$i]=$(_pool_now)
  (
    s=$(_pool_now)
    st=0
    if [ "${POOL_GUARD:-1}" != 0 ] && type memguard_run >/dev/null 2>&1; then
      # the item runs in a child bash under a cgroup memory limit (scripts/lib/memguard.sh);
      # functions and shell variables are handed over as parallel.sh's par_run does
      export POOL_BLOCK="${POOL_CODES[$i]}"
      POOL_PRELUDE="$(declare -f); $(declare -p 2>/dev/null | grep -vE '^declare -[a-zA-Z]*[rx]')"
      memguard_run -l "${JANUS_JOB_MEM:-10G}" -n "pool$i" -- bash -c "$POOL_PRELUDE"'
        eval "$POOL_BLOCK"' > "$log" 2>&1 || st=$?
    else
      ( eval "${POOL_CODES[$i]}" ) > "$log" 2>&1 || st=$?
    fi
    e=$(_pool_now)
    echo "$(echo "$e - $s" | bc)" > "$POOL_DIR/$f.secs"
    echo "$st" > "$rc.tmp" && mv "$rc.tmp" "$rc"
  ) &
  POOL_PID[$i]=$!
}

pool_run() {
  local total=${#POOL_IDS[@]} i k n
  local -a order=() running=() POOL_T0=() POOL_PID=()
  local done_n=0 next=0 failed_n=0 skip_n=0 wall0 lastprog
  wall0=$(_pool_now); lastprog=$wall0
  # longest first; an item with no recorded wall first (99999), then the original order
  mapfile -t order < <(for ((i = 0; i < total; i++)); do
      printf '%s\t%s\n' "${POOL_SECS[${POOL_KEYS[$i]}]:-99999}" "$i"
    done | sort -t$'\t' -k1,1gr -k2,2n | cut -f2)
  echo "pool $POOL_NAME: $total items, -j $POOL_JOBS (longest first; $(for k in "${POOL_KEYS[@]}"; do [ -n "${POOL_SECS[$k]:-}" ] || echo x; done | wc -l) without a recorded time go first)"
  while [ "$done_n" -lt "$total" ]; do
    # launch while there is a free slot and memory for another job
    while [ "$next" -lt "$total" ] && [ "${#running[@]}" -lt "$POOL_JOBS" ]; do
      if [ "${#running[@]}" -gt 0 ] &&
         [ "$(par_mem_available_kb)" -lt $(( ${POOL_MEM_HEADROOM_KB:-$PAR_HEADROOM_KB} + ${POOL_JOB_MEM_KB:-$PAR_JOB_MEM_KB} )) ]; then
        break
      fi
      i=${order[$next]}; next=$((next + 1))
      _pool_spawn "$i"
      running+=("$i")
    done
    # reap
    local -a still=()
    for i in "${running[@]}"; do
      local id=${POOL_IDS[$i]} f rcf st label wall now
      f="$(_pool_file "$id")"; rcf="$POOL_DIR/$f.rc"
      if [ -f "$rcf" ]; then
        st=$(cat "$rcf"); wall=$(cat "$POOL_DIR/$f.secs" 2>/dev/null || echo 0)
        wait "${POOL_PID[$i]}" 2>/dev/null || true
      elif ! kill -0 "${POOL_PID[$i]}" 2>/dev/null; then
        st=""; wall=$(echo "$(_pool_now) - ${POOL_T0[$i]}" | bc)   # died without a result
      else
        still+=("$i"); continue
      fi
      done_n=$((done_n + 1))
      if [ -z "$st" ]; then label=MISSING
      elif [ "$st" = 0 ]; then
        if grep -q ' skipped (unchanged' "$POOL_DIR/$f.log" 2>/dev/null; then label=SKIP; skip_n=$((skip_n + 1)); else label=PASS; fi
      elif [ "$st" = 124 ] || grep -q '^TIMEOUT:' "$POOL_DIR/$f.log" 2>/dev/null; then label=TIMEOUT
      else label=FAIL; fi
      if [ "$label" = PASS ]; then printf '%s\t%.1f\n' "${POOL_KEYS[$i]}" "$wall" > "$POOL_DIR/$f.time"; fi
      if [ "$label" != PASS ] && [ "$label" != SKIP ]; then
        POOL_FAILED+=("$id"); failed_n=$((failed_n + 1))
      fi
      printf '[%*d/%d] %-7s %-34s %9s\n' "${#total}" "$done_n" "$total" "$label" "$id" "$(_pool_fmt "$wall")"
      if [ "$label" != PASS ] && [ "$label" != SKIP ]; then
        echo "  ---- last lines of $POOL_DIR/$f.log ----"; tail -n 30 "$POOL_DIR/$f.log" 2>/dev/null | sed 's/^/  | /'
      fi
      if [ -n "${POOL_TIMELINE:-}" ]; then
        now=$(_pool_now)
        printf '{"kind":"item","pool":"%s","id":"%s","status":"%s","rc":%s,"start":%.3f,"end":%.3f,"wall":%.3f}\n' \
          "$(_pool_json "$POOL_NAME")" "$(_pool_json "$id")" "$label" "${st:--1}" "${POOL_T0[$i]}" "$now" "$wall" >> "$POOL_TIMELINE"
      fi
    done
    running=(${still[@]+"${still[@]}"})
    [ "$done_n" -lt "$total" ] || break
    # progress
    now=$(_pool_now)
    if [ "$(echo "$now - $lastprog >= $POOL_PROGRESS_SECS" | bc)" = 1 ]; then
      lastprog=$now
      local desc="" cnt=0
      for i in "${running[@]}"; do
        cnt=$((cnt + 1)); [ "$cnt" -le 8 ] || { desc="$desc, ..."; break; }
        desc="${desc:+$desc, }${POOL_IDS[$i]} $(_pool_fmt "$(echo "$now - ${POOL_T0[$i]}" | bc)")"
      done
      printf -- '-- pool %s: %d/%d done, %d failed, %d running [%s], %s elapsed\n' "$POOL_NAME" "$done_n" "$total" \
        "$failed_n" "${#running[@]}" "$desc" "$(_pool_fmt "$(echo "$now - $wall0" | bc)")"
    fi
    sleep 1
  done
  now=$(_pool_now)
  printf 'pool %s: %d items, %d passed, %d skipped, %d failed, %s wall (-j %s)\n' "$POOL_NAME" "$total" \
    "$((total - failed_n - skip_n))" "$skip_n" "$failed_n" "$(_pool_fmt "$(echo "$now - $wall0" | bc)")" "$POOL_JOBS"
  if [ -n "${POOL_TIMELINE:-}" ]; then
    printf '{"kind":"pool","pool":"%s","items":%d,"failed":%d,"jobs":%s,"start":%.3f,"end":%.3f}\n' \
      "$(_pool_json "$POOL_NAME")" "$total" "$failed_n" "$POOL_JOBS" "$wall0" "$now" >> "$POOL_TIMELINE"
  fi
  [ "$failed_n" -eq 0 ]
}

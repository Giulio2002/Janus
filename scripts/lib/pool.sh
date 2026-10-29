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
#   pool_add ID CODE [COSTKEY [NEEDS]]
#                                  queue an item: CODE is shell code run in a subshell (it sees the
#                                  functions and variables defined so far); its exit status is the
#                                  item's verdict. COSTKEY (default ID) is the key into the times file.
#                                  NEEDS: space-separated ids of items that must have passed first; the
#                                  item waits for them and is reported BLOCKED (a failure) if one did not.
#   pool_run                       run the queue to the end. Each item's result line (PASS / FAIL /
#                                  TIMEOUT / MISSING + wall seconds) is printed the moment it finishes, a
#                                  progress line (done/total, the running items with elapsed time) every
#                                  $POOL_PROGRESS_SECS (default 60) seconds. Returns 1 if any item did
#                                  not pass (a missing result counts as a failure); POOL_FAILED holds the ids.
#
# Environment: POOL_TIMELINE=FILE appends one JSON line per finished item (and one per pool);
# POOL_PROGRESS_SECS; POOL_MEM_HEADROOM_KB / POOL_JOB_MEM_KB (admission, default as parallel.sh).
# Per-item memory admission (opt-in): pool_peaks FILE loads recorded peaks ("ID<TAB>seconds<TAB>peak GiB", the speed
# baseline) and POOL_BUDGET_KB is the pool's memory budget. A running item holds a reservation of its OWN recorded
# peak x1.3 (at least 0.25 GiB; POOL_UNKNOWN_GIB, default 9.15 = 6.1 x 1.5, for an item without a record); a new item
# is admitted only if the reservations of the running ones plus its own fit the budget (the first is always admitted),
# so small items run POOL_JOBS wide and heavy ones limit themselves. POOL_DEBUG=1 logs each deferral. The pool line
# of the timeline gets peakConcurrency and peakReservedGiB.
# A finished item whose log has a line starting "TIMEOUT:" (scripts/lib/itemtimeout.sh) or whose status
# is 124 is reported as TIMEOUT. An item whose log contains " skipped (unchanged" is reported SKIP
# (a pass that did not run: --changed) and does not update the times.

pool_init() {
  POOL_NAME="$1"; POOL_JOBS="$2"; POOL_DIR="$3"
  POOL_IDS=(); POOL_CODES=(); POOL_KEYS=(); POOL_NEEDS=(); POOL_FAILED=()
  declare -gA POOL_SECS=()
  declare -gA POOL_PEAK=()
  mkdir -p "$POOL_DIR"
  POOL_PROGRESS_SECS="${POOL_PROGRESS_SECS:-60}"
}

pool_times() { # FILE
  [ -f "$1" ] || return 0
  local k v
  while IFS=$'\t' read -r k v; do POOL_SECS[$k]=$v; done < "$1"
}

pool_peaks() { # FILE: recorded peaks in GiB, 3rd column
  [ -f "$1" ] || return 0
  local k w m
  declare -gA POOL_PEAK
  while IFS=$'\t' read -r k w m; do case "$k" in '#'*|lane:*|'') ;; *) POOL_PEAK[$k]=$m ;; esac; done < "$1"
}
_pool_res_kb() { # INDEX: this item's reservation in kB
  local pk=${POOL_PEAK[${POOL_KEYS[$1]}]:-}
  awk -v pk="$pk" -v unk="${POOL_UNKNOWN_GIB:-9.15}" 'BEGIN { g = (pk == "" ? unk : pk * 1.3); if (pk != "" && g < 0.25) g = 0.25; printf "%d", g * 1048576 }'
}

pool_add() { # ID CODE [COSTKEY [NEEDS]]
  POOL_IDS+=("$1"); POOL_CODES+=("$2"); POOL_KEYS+=("${3:-$1}"); POOL_NEEDS+=("${4:-}")
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
  local done_n=0 failed_n=0 skip_n=0 wall0 lastprog pick ready blocked
  local -A started=() known=()
  local -A STATUS=() deferred=() RES=()
  local peak_run=0 peak_res=0 res_sum=0 rr minjob
  for ((i = 0; i < total; i++)); do known[${POOL_IDS[$i]}]=1; done
  wall0=$(_pool_now); lastprog=$wall0
  # longest first; an item with no recorded wall first (99999), then the original order
  mapfile -t order < <(for ((i = 0; i < total; i++)); do
      printf '%s\t%s\n' "${POOL_SECS[${POOL_KEYS[$i]}]:-99999}" "$i"
    done | sort -t$'\t' -k1,1gr -k2,2n | cut -f2)
  echo "pool $POOL_NAME: $total items, -j $POOL_JOBS (longest first; $(for k in "${POOL_KEYS[@]}"; do [ -n "${POOL_SECS[$k]:-}" ] || echo x; done | wc -l) without a recorded time go first)"
  while [ "$done_n" -lt "$total" ]; do
    # launch while there is a free slot and memory for another job: the first queued item (in
    # longest-first order) whose needs have passed
    while [ "${#running[@]}" -lt "$POOL_JOBS" ]; do
      # live check: MemAvailable stays above the floor plus a job's budget (in per-item mode a 2 GiB margin: the
      # reservations already count the items)
      minjob=${POOL_JOB_MEM_KB:-$PAR_JOB_MEM_KB}; [ -z "${POOL_BUDGET_KB:-}" ] || minjob=2097152
      if [ "${#running[@]}" -gt 0 ] &&
         [ "$(par_mem_available_kb)" -lt $(( ${POOL_MEM_HEADROOM_KB:-$PAR_HEADROOM_KB} + minjob )) ]; then
        break
      fi
      res_sum=0; for rr in "${running[@]}"; do res_sum=$((res_sum + ${RES[$rr]:-0})); done
      pick=""
      for ((k = 0; k < total; k++)); do
        i=${order[$k]}
        [ -z "${started[$i]:-}" ] || continue
        ready=1; blocked=""
        for n in ${POOL_NEEDS[$i]}; do
          case "${STATUS[$n]:-}" in
            PASS|SKIP) ;;
            "") ready=""; [ -n "${known[$n]:-}" ] || blocked="$n (unknown item)" ;;
            *) blocked="$n"; break ;;
          esac
        done
        if [ -n "$blocked" ]; then pick=$i; break; fi
        [ -n "$ready" ] || continue
        if [ -n "${POOL_BUDGET_KB:-}" ] && [ "${#running[@]}" -gt 0 ]; then
          rr=$(_pool_res_kb "$i")
          if [ $((res_sum + rr)) -gt "$POOL_BUDGET_KB" ]; then
            if [ -n "${POOL_DEBUG:-}" ] && [ "${deferred[$i]:-}" != "$res_sum" ]; then
              deferred[$i]=$res_sum
              echo "pool $POOL_NAME: defer ${POOL_IDS[$i]} (reserved $((res_sum / 1024)) MiB + $((rr / 1024)) MiB > budget $((POOL_BUDGET_KB / 1024)) MiB)"
            fi
            continue
          fi
        fi
        pick=$i; break
      done
      [ -n "$pick" ] || break
      i=$pick; started[$i]=1
      if [ -n "$blocked" ]; then
        # a need failed (or does not exist): the item does not run
        done_n=$((done_n + 1)); failed_n=$((failed_n + 1)); POOL_FAILED+=("${POOL_IDS[$i]}"); STATUS[${POOL_IDS[$i]}]=BLOCKED
        printf '[%*d/%d] %-7s %-34s %9s  (needs %s)\n' "${#total}" "$done_n" "$total" BLOCKED "${POOL_IDS[$i]}" - "$blocked"
        if [ -n "${POOL_TIMELINE:-}" ]; then
          printf '{"kind":"item","pool":"%s","id":"%s","status":"BLOCKED","rc":-1,"start":%.3f,"end":%.3f,"wall":0}\n' \
            "$(_pool_json "$POOL_NAME")" "$(_pool_json "${POOL_IDS[$i]}")" "$(_pool_now)" "$(_pool_now)" >> "$POOL_TIMELINE"
        fi
        continue
      fi
      _pool_spawn "$i"
      running+=("$i")
      RES[$i]=$(_pool_res_kb "$i"); res_sum=$((res_sum + RES[$i]))
      [ "${#running[@]}" -le "$peak_run" ] || peak_run=${#running[@]}
      [ "$res_sum" -le "$peak_res" ] || peak_res=$res_sum
      [ -z "${POOL_RES_TRACE:-}" ] || echo "$res_sum ${#running[@]}" >> "$POOL_RES_TRACE"
    done
    if [ "${#running[@]}" -eq 0 ] && [ "$done_n" -lt "$total" ]; then
      # nothing runs and nothing can start: the remaining needs form a cycle
      for ((k = 0; k < total; k++)); do
        [ -z "${started[$k]:-}" ] || continue
        started[$k]=1; done_n=$((done_n + 1)); failed_n=$((failed_n + 1)); POOL_FAILED+=("${POOL_IDS[$k]}")
        printf '[%*d/%d] %-7s %-34s %9s  (needs can never be met)\n' "${#total}" "$done_n" "$total" BLOCKED "${POOL_IDS[$k]}" -
      done
      break
    fi
    # reap
    local -a still=()
    for i in "${running[@]}"; do
      local id=${POOL_IDS[$i]} f rcf st label wall now note
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
      STATUS[$id]=$label
      if [ "$label" = PASS ]; then printf '%s\t%.1f\n' "${POOL_KEYS[$i]}" "$wall" > "$POOL_DIR/$f.time"; fi
      note=""
      if [ "$label" = SKIP ]; then note="$(grep -m1 ' skipped (unchanged' "$POOL_DIR/$f.log" 2>/dev/null | sed 's/^.*skipped (unchanged: //; s/)$//' | cut -c1-300)"; fi
      if [ "$label" != PASS ] && [ "$label" != SKIP ]; then
        POOL_FAILED+=("$id"); failed_n=$((failed_n + 1))
      fi
      printf '[%*d/%d] %-7s %-34s %9s%s\n' "${#total}" "$done_n" "$total" "$label" "$id" "$(_pool_fmt "$wall")" "${note:+  $note}"
      if [ "$label" != PASS ] && [ "$label" != SKIP ]; then
        echo "  ---- last lines of $POOL_DIR/$f.log ----"; tail -n 30 "$POOL_DIR/$f.log" 2>/dev/null | sed 's/^/  | /'
      fi
      if [ -n "${POOL_TIMELINE:-}" ]; then
        now=$(_pool_now)
        printf '{"kind":"item","pool":"%s","id":"%s","status":"%s","rc":%s,"start":%.3f,"end":%.3f,"wall":%.3f,"note":"%s"}\n' \
          "$(_pool_json "$POOL_NAME")" "$(_pool_json "$id")" "$label" "${st:--1}" "${POOL_T0[$i]}" "$now" "$wall" "$(_pool_json "$note")" >> "$POOL_TIMELINE"
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
    printf '{"kind":"pool","pool":"%s","items":%d,"failed":%d,"jobs":%s,"start":%.3f,"end":%.3f,"peakConcurrency":%d,"peakReservedGiB":%.2f}\n' \
      "$(_pool_json "$POOL_NAME")" "$total" "$failed_n" "$POOL_JOBS" "$wall0" "$now" "$peak_run" "$(awk -v k="$peak_res" 'BEGIN { print k / 1048576 }')" >> "$POOL_TIMELINE"
  fi
  [ "$failed_n" -eq 0 ]
}

# Shared by the oracle drivers (scripts/oracle.sh, oracle-amd64.sh, oracle-sail.sh, asl.sh,
# x86formal.sh, audit/round5/model/run-model.sh): what a run leaves in its output directory.
#
# A full oracle run writes multi-GB JSON-lines dumps (gen.jsonl, harvest.jsonl, cases.jsonl,
# hw.jsonl, model.jsonl, verdicts.jsonl; the Sail run copies them again per comparison), and
# every worktree kept them: one finished worktree held 69 GB. After a run, art_prune applies
# $KEEP to them:
#
#   KEEP unset or 0  (default) keep the summaries (*.md, *.txt), the minimized reproductions
#                    (repro.*), soundness.jsonl and every other small file; write
#                    mismatches.jsonl (the MISMATCH verdicts, uncompressed, only if there are
#                    any) and keep verdicts.jsonl and the results other tools read (cases.jsonl,
#                    hw.jsonl, model.jsonl, qemu.jsonl, sail.jsonl, janus.jsonl)
#                    zstd-compressed (<name>.zst, ~5x smaller, verdicts ~15x); remove the dumps
#                    that are duplicates or cheap to derive again (gen.jsonl and harvest.jsonl,
#                    whose union is cases.jsonl; sail-model.jsonl, cases.sail-dczid.jsonl,
#                    sail-regen.jsonl, cases.in.jsonl) and, with --copies, the per-comparison
#                    copies of the corpus (cases.jsonl, hw.jsonl)
#   KEEP=zst         compress every dump, remove none
#   KEEP=1           keep everything raw, as before
#
# Any other *.jsonl over 64 MiB is compressed. Readers of a pruned directory use art_input (a
# file, decompressing <file>.zst next to it first; art_cleanup removes what it decompressed)
# or art_cat; `zstd -dc <file>.zst` restores a dump by hand.
#
#   art_prune [--copies] DIR...   apply $KEEP to the dumps directly in each DIR (not recursive)
#   art_exists FILE               FILE or FILE.zst exists
#   art_cat FILE                  FILE (or FILE.zst decompressed) on standard output
#   art_input FILE                print FILE, decompressing FILE.zst into FILE if needed (call it
#                                 directly, not in $(...), so that art_cleanup knows the file)
#   art_cleanup                   remove the files art_input decompressed

ART_DECOMPRESSED=()
ART_BIG=$((64 * 1024 * 1024))

art_mode() {
  case "${KEEP:-0}" in
    0|"") echo prune ;;
    zst|zstd) echo zst ;;
    1|raw|yes|true) echo raw ;;
    *) echo "KEEP=$KEEP: use 0 (default), zst or 1" >&2; echo prune ;;
  esac
}

art_zstd() { # compress $1 to $1.zst and remove $1 (keeps $1 if compression fails)
  local f="$1"
  if command -v zstd >/dev/null 2>&1; then
    zstd -q -f -T4 -3 --rm "$f" -o "$f.zst" || { rm -f "$f.zst"; return 1; }
  else
    echo "artifacts: zstd not installed; keeping $f uncompressed" >&2
    return 1
  fi
}

art_size() { stat -c %s "$1" 2>/dev/null || echo 0; }

art_prune() {
  local copies=0
  if [ "${1:-}" = --copies ]; then copies=1; shift; fi
  local mode; mode="$(art_mode)"
  [ "$mode" = raw ] && return 0
  local dir f base action before=0 after=0 n_c=0 n_r=0
  for dir in "$@"; do
    [ -d "$dir" ] || continue
    for f in "$dir"/*.jsonl; do
      [ -f "$f" ] || continue
      base="$(basename "$f")"
      case "$base" in
        verdicts.jsonl)
          action=compress
          if [ "$mode" = prune ] && grep -q '"verdict":"MISMATCH"' "$f"; then
            grep '"verdict":"MISMATCH"' "$f" > "$dir/mismatches.jsonl" || true
          fi ;;
        cases.jsonl|hw.jsonl)
          action=compress
          [ "$copies" = 1 ] && action=drop ;;
        model.jsonl|qemu.jsonl|sail.jsonl|janus.jsonl)
          action=compress ;;
        gen.jsonl|harvest.jsonl|sail-model.jsonl|cases.sail-dczid.jsonl|sail-regen.jsonl|cases.in.jsonl)
          action=drop ;;
        *)
          action=keep
          [ "$(art_size "$f")" -gt "$ART_BIG" ] && action=compress ;;
      esac
      [ "$mode" = zst ] && [ "$action" = drop ] && action=compress
      before=$((before + $(art_size "$f")))
      case "$action" in
        compress)
          rm -f "$f.zst"
          if art_zstd "$f"; then n_c=$((n_c + 1)); after=$((after + $(art_size "$f.zst"))); else after=$((after + $(art_size "$f"))); fi ;;
        drop) rm -f "$f" "$f.zst"; n_r=$((n_r + 1)) ;;
        keep) after=$((after + $(art_size "$f"))) ;;
      esac
    done
  done
  if [ $((n_c + n_r)) -gt 0 ]; then
    echo "artifacts: $n_c dumps compressed, $n_r removed ($((before / 1048576)) MiB -> $((after / 1048576)) MiB; KEEP=1 keeps them raw) in $*" >&2
  fi
}

art_exists() { [ -f "$1" ] || [ -f "$1.zst" ]; }

art_cat() {
  if [ -f "$1" ]; then cat "$1"
  elif [ -f "$1.zst" ]; then zstd -q -dc "$1.zst"
  else echo "artifacts: neither $1 nor $1.zst exists" >&2; return 1
  fi
}

art_input() {
  local f="$1"
  if [ ! -f "$f" ]; then
    [ -f "$f.zst" ] || { echo "artifacts: neither $f nor $f.zst exists" >&2; return 1; }
    zstd -q -d -T4 "$f.zst" -o "$f" || { rm -f "$f"; return 1; }
    ART_DECOMPRESSED+=("$f")
  fi
  printf '%s\n' "$f"
}

art_cleanup() {
  local f
  for f in "${ART_DECOMPRESSED[@]+"${ART_DECOMPRESSED[@]}"}"; do rm -f "$f"; done
  ART_DECOMPRESSED=()
}

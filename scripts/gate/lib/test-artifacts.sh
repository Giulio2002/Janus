#!/usr/bin/env bash
# Self-test of scripts/lib/artifacts.sh (run by `go test ./cmd/janus`, TestArtifactsLib): the
# pruning of an oracle output directory under KEEP unset / zst / 1, and art_input / art_cat /
# art_cleanup on a pruned directory. Writes only to a mktemp directory.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=artifacts.sh
. "$here/artifacts.sh"
W="$(mktemp -d "${TMPDIR:-/var/tmp}/test-artifacts.XXXXXX")"
trap 'rm -rf "$W"' EXIT
fail=0
check() { # check DESCRIPTION COMMAND...
  local what="$1"; shift
  if "$@"; then :; else echo "FAIL: $what" >&2; fail=1; fi
}

mkrun() { # a fake `oracle run` output directory, with a per-comparison subdirectory
  local d="$1"
  rm -rf "$d"; mkdir -p "$d/sub"
  for f in gen harvest cases hw model; do
    for i in 1 2 3; do echo "{\"id\":$i,\"f\":\"$f\"}"; done > "$d/$f.jsonl"
  done
  printf '%s\n' '{"id":1,"verdict":"agree"}' '{"id":2,"verdict":"MISMATCH","why":"x"}' '{"id":3,"verdict":"model-gap"}' > "$d/verdicts.jsonl"
  echo "# summary" > "$d/summary.md"
  echo '{"id":2}' > "$d/repro.jsonl"
  echo '{"small":1}' > "$d/smoke.jsonl"
  cp "$d/cases.jsonl" "$d/hw.jsonl" "$d/model.jsonl" "$d/verdicts.jsonl" "$d/sub/"
  # An unknown dump over the size threshold is compressed, a small one kept.
  head -c $((ART_BIG + 1)) /dev/zero | tr '\0' 'x' > "$d/big.jsonl"
}

# Default (KEEP unset): summaries, repro, small files kept; verdicts and corpus compressed;
# MISMATCH verdicts extracted; gen/harvest removed; --copies drops the corpus copies.
unset KEEP
D="$W/default"; mkrun "$D"
cp "$D/verdicts.jsonl" "$W/verdicts.orig"
art_prune --copies "$D/sub" 2>/dev/null
art_prune "$D" 2>/dev/null
for f in summary.md repro.jsonl smoke.jsonl cases.jsonl.zst hw.jsonl.zst model.jsonl.zst verdicts.jsonl.zst big.jsonl.zst sub/verdicts.jsonl.zst sub/model.jsonl.zst; do
  check "default keeps $f" test -f "$D/$f"
done
for f in gen.jsonl harvest.jsonl cases.jsonl hw.jsonl model.jsonl verdicts.jsonl big.jsonl gen.jsonl.zst sub/cases.jsonl sub/cases.jsonl.zst sub/hw.jsonl.zst; do
  check "default removes $f" test ! -e "$D/$f"
done
check "mismatches.jsonl holds the MISMATCH verdict" grep -qx '{"id":2,"verdict":"MISMATCH","why":"x"}' "$D/mismatches.jsonl"
check "mismatches.jsonl holds only it" test "$(wc -l < "$D/mismatches.jsonl")" = 1
art_cat "$D/verdicts.jsonl" > "$W/verdicts.back"
check "the compressed verdicts are the original" cmp -s "$W/verdicts.orig" "$W/verdicts.back"
check "art_cat decompresses" test "$(art_cat "$D/cases.jsonl" | wc -l)" = 3
check "art_exists sees a compressed file" art_exists "$D/hw.jsonl"
if art_exists "$D/gen.jsonl"; then echo "FAIL: art_exists accepts a removed file" >&2; fail=1; fi
art_input "$D/cases.jsonl" >/dev/null
check "art_input decompresses next to the .zst" test -f "$D/cases.jsonl"
check "art_input keeps the .zst" test -f "$D/cases.jsonl.zst"
art_cleanup
check "art_cleanup removes what art_input decompressed" test ! -e "$D/cases.jsonl"
echo raw > "$D/summary.txt"
art_input "$D/summary.txt" >/dev/null
art_cleanup
check "art_cleanup leaves files art_input did not create" test -f "$D/summary.txt"
check "art_input fails on a missing file" bash -c ". '$here/artifacts.sh'; ! art_input '$D/none.jsonl' 2>/dev/null"
# Pruning twice is harmless.
art_prune "$D" 2>/dev/null
check "a second prune keeps the compressed verdicts" test -f "$D/verdicts.jsonl.zst"

# No mismatch: no mismatches.jsonl.
D="$W/agree"; mkrun "$D"; grep -v MISMATCH "$D/verdicts.jsonl" > "$D/v" && mv "$D/v" "$D/verdicts.jsonl"
art_prune "$D" 2>/dev/null
check "no mismatches.jsonl without a mismatch" test ! -e "$D/mismatches.jsonl"

# KEEP=zst: everything compressed, nothing removed.
D="$W/zst"; mkrun "$D"
KEEP=zst art_prune --copies "$D/sub" 2>/dev/null
KEEP=zst art_prune "$D" 2>/dev/null
for f in gen harvest cases hw model verdicts big sub/cases sub/hw; do
  check "KEEP=zst keeps $f compressed" test -f "$D/$f.jsonl.zst"
  check "KEEP=zst leaves no raw $f" test ! -e "$D/$f.jsonl"
done
check "KEEP=zst decompresses to the original" test "$(art_cat "$D/gen.jsonl")" = "$(printf '%s\n' '{"id":1,"f":"gen"}' '{"id":2,"f":"gen"}' '{"id":3,"f":"gen"}')"

# KEEP=1: nothing touched.
D="$W/raw"; mkrun "$D"
before="$(cd "$D" && find . -type f | sort | xargs md5sum)"
KEEP=1 art_prune --copies "$D/sub"
KEEP=1 art_prune "$D"
check "KEEP=1 changes nothing" test "$before" = "$(cd "$D" && find . -type f | sort | xargs md5sum)"

[ "$fail" = 0 ] && echo "artifacts.sh: all checks passed" || { echo "artifacts.sh: FAILED" >&2; exit 1; }

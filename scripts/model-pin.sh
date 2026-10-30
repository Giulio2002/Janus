#!/usr/bin/env bash
# The pin of the ISA model artifacts (ArmASL build + lean-sail, Sail driver) for the cold gate.
# docs/TESTING.md "Cold gate and the model pin"; scripts/lib/modelpin.py.
#
#   scripts/model-pin.sh keys                 print the model keys of this checkout (armasl, sail)
#   scripts/model-pin.sh check [--stale rebuild|fail]
#                                             verify the pin for this checkout's keys: record HMAC, manifest HMAC and hash,
#                                             SHA-256 of every pinned file. Exit 0 pin holds (or stale with `rebuild`);
#                                             1 FAIL: no pin for the current keys (STALE), or a pin that is tampered,
#                                             corrupt or incomplete. Reads only.
#   scripts/model-pin.sh verify-tree [--stale rebuild|fail] [--only armasl,sail]
#                                             every pinned file in THIS checkout's JanusASL/.lake / oracle-sail still has its
#                                             pinned hash (the gate runs it after the lanes). Reads only.
#   scripts/model-pin.sh write --commit REV [--evidence FILE]
#                                             create/confirm the pin from THIS checkout's truly-cold build
#                                             (JanusASL/.lake, oracle-sail/target). Refused unless JANUS_PIN_WRITER is
#                                             set by scripts/nightly-cold-gate.sh, which calls it only after a cold gate
#                                             that built both from source passed and agreed with the cached run.
#
# JANUS_MODEL_PIN_DIR picks the pin store (default /srv/janus-model-pin, else ~/.cache/janus/model-pin).
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mp="$root/scripts/lib/modelpin.py"
cmd="${1:-}"; [ $# -eq 0 ] || shift
pin="$(python3 -I "$mp" dir)"
keys() { # sets ak, sk
  ak=$("$root/scripts/asl.sh" key) || { echo "model-pin: cannot compute the ArmASL key" >&2; return 1; }
  sk=$("$root/scripts/oracle-sail.sh" key) || { echo "model-pin: cannot compute the Sail driver key" >&2; return 1; }
}
case "$cmd" in
  keys) keys || exit 1; echo "armasl $ak"; echo "sail $sk"; echo "pin store $pin" ;;
  check)
    stale=rebuild
    while [ $# -gt 0 ]; do case "$1" in --stale) stale="${2:?}"; shift 2 ;; *) echo "model-pin: unknown argument $1" >&2; exit 2 ;; esac; done
    case "$stale" in fail|rebuild) ;; *) echo "model-pin: --stale fail|rebuild" >&2; exit 2 ;; esac
    keys || exit 1
    rc=0
    for kk in "armasl $ak" "sail $sk"; do
      set -- $kk; out=$(python3 -I "$mp" check "$1" "$pin" "$2"); r=$?
      case $r in
        0) echo "model pin: $out" ;;
        2) if [ "$stale" = rebuild ]; then echo "model pin: $out"; echo "model pin: $1 STALE: it will be built from source inside the gate"
           else echo "model pin: FAIL: $out"; rc=1; fi ;;
        *) echo "model pin: FAIL: $out"; rc=1 ;;
      esac
    done
    [ "$rc" = 0 ] || echo "model pin: the pin store is $pin; the nightly truly-cold run (scripts/nightly-cold-gate.sh) creates and updates it, nothing else does"
    exit $rc ;;
  verify-tree)
    stale=rebuild only="armasl,sail"
    while [ $# -gt 0 ]; do case "$1" in --stale) stale="${2:?}"; shift 2 ;; --only) only="${2:?}"; shift 2 ;; *) echo "model-pin: unknown argument $1" >&2; exit 2 ;; esac; done
    keys || exit 1
    rc=0
    for kk in "armasl $ak $root/JanusASL/.lake" "sail $sk $root/oracle-sail"; do
      set -- $kk
      case ",$only," in *",$1,"*) ;; *) continue ;; esac
      out=$(python3 -I "$mp" verify-tree "$1" "$pin" "$2" "$3"); r=$?
      case $r in
        0) echo "model pin: $out" ;;
        2) if [ "$stale" = rebuild ]; then echo "model pin: $1 STALE (built from source inside the gate): not checked"; else echo "model pin: FAIL: $out"; rc=1; fi ;;
        *) echo "model pin: FAIL: $out"; rc=1 ;;
      esac
    done
    exit $rc ;;
  write)
    commit="" ev=()
    while [ $# -gt 0 ]; do case "$1" in --commit) commit="${2:?}"; shift 2 ;; --evidence) ev=(--evidence "${2:?}"); shift 2 ;; *) echo "model-pin: unknown argument $1" >&2; exit 2 ;; esac; done
    [ -n "$commit" ] || { echo "model-pin: write needs --commit" >&2; exit 2; }
    keys || exit 1
    rc=0
    "$root/scripts/asl.sh" files | python3 -I "$mp" write armasl "$pin" "$ak" "$root/JanusASL/.lake" --commit "$commit" "${ev[@]}" || rc=$?
    [ "$rc" = 0 ] || exit $rc
    [ -f "$root/oracle-sail/target/release/janus-oracle-sail" ] || { echo "model-pin: no Sail driver built in $root/oracle-sail/target" >&2; exit 1; }
    printf 'target/release/janus-oracle-sail\0' | python3 -I "$mp" write sail "$pin" "$sk" "$root/oracle-sail" --commit "$commit" "${ev[@]}" || rc=$?
    exit $rc ;;
  *) sed -n '2,/^set -uo/p' "${BASH_SOURCE[0]}" | sed '$d'; exit 2 ;;
esac

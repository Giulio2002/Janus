#!/usr/bin/env bash
# The cold-side audit of the compiled-object cache, as the nightly cold gate runs it (scripts/nightly-cold-gate.sh):
#   scripts/lib/nightly-objaudit.sh COLD_TREE CACHE_DIR
# For both scopes (arm, jasl, janus) every cache entry of an id the cold tree also has is compared object by object with the
# cold tree's freshly compiled objects (asl_mod_cache.py objaudit). A differing entry is quarantined (.poisoned-<id>,
# never served again). Exit 0 only if both scopes compared something and found nothing; 1 on a poisoned entry, a
# failed audit, or an audit that compared NOTHING (it fails closed: an audit that did not run proves nothing).
set -uo pipefail
unset ASL_OBJAUDIT_TEST_PAUSE   # a test-only wait hook of obj_audit (M5): never active in a real nightly
tree="${1:?cold tree}" cache="${2:?cache dir}" bad=0
extra=("${@:3}")   # e.g. --dry-run (the smoke run against the production cache: no lock, no quarantine)
# The scope list is NOT a knob: a narrowed audit proves less than the nightly claims. The override exists for the script's own
# tests only and needs the explicit test marker; without it the script refuses (exit 2) rather than audit fewer scopes.
if [ -n "${NIGHTLY_OBJAUDIT_SCOPES:-}" ]; then
  if [ "${NIGHTLY_OBJAUDIT_TEST:-}" != 1 ]; then
    echo "nightly-objaudit: NIGHTLY_OBJAUDIT_SCOPES is set outside a test (NIGHTLY_OBJAUDIT_TEST=1): refusing to audit fewer scopes than arm jasl janus"
    exit 2
  fi
  echo "nightly-objaudit: TEST MODE: scopes narrowed to '$NIGHTLY_OBJAUDIT_SCOPES' (this is not the nightly audit)"
fi
[ -d "$cache/armobj" ] || { echo "nightly-objaudit: no armobj directory in $cache: nothing to audit, the audit did not run"; exit 1; }
for sc in ${NIGHTLY_OBJAUDIT_SCOPES:-arm jasl janus}; do
  python3 -I "$tree/models/asl/tools/asl_mod_cache.py" objaudit "$tree" "$sc" "$cache" ${extra[@]+"${extra[@]}"}
  oa=$?
  if [ "$oa" != 0 ]; then
    echo "nightly-objaudit: P0 compiled-object cache audit [$sc] FAILED (rc $oa: 3 = POISONED entry quarantined, 4 = nothing compared): every cached gate result since the last clean nightly is unproven"
    bad=1
  fi
done
exit $bad

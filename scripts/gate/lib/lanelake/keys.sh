# shellcheck shell=bash
# Lock keys of the shared-tree discipline. The lock is keyed by the RESOLVED path of the directory being written, with the
# lock file inside that real directory, so every tree (and the source checkout) that shares one .lake by symlink
# serialises on ONE lock:
#   lane_pkg_dir DIR          the package directory (nearest lakefile.toml / lakefile.lean at or above DIR)
#   lane_lake_lock PKGDIR     realpath(PKGDIR/.lake)/.gate-lake.lock         (created .lake if missing)
#   lane_fw_lock TREE         realpath(TREE/.lake)/janus-framework.lock      (the lock janus itself holds shared)
lane_pkg_dir() {
  local d; d="$(cd "$1" && pwd -P)"
  while [ "$d" != / ] && [ ! -f "$d/lakefile.toml" ] && [ ! -f "$d/lakefile.lean" ]; do d="$(dirname "$d")"; done
  echo "$d"
}
lane_lake_lock() { mkdir -p "$1/.lake" 2>/dev/null; echo "$(realpath -m "$1/.lake")/.gate-lake.lock"; }
lane_fw_lock() { echo "$(realpath -m "$1/.lake")/janus-framework.lock"; }

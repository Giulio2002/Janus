# NOTES-UP4 (hermetic sandbox) -- branch agent/up4-sandbox, base b8ac6cca
- Design: cmd/janus/sandbox.go bwrap = empty root + allowlist ro binds (/usr,/bin,/lib*,/sbin symlinks, minimal /etc,
  /usr/local masked), toolchain sysroot, LEAN_PATH dirs, argv[0] dir, protected, writable; private /tmp,/dev,/proc;
  --clearenv + allowlisted env (PATH, LEAN_*, LAKE_*, GIT_*, LC_*, LANG, TZ, TERM, HOME=/tmp); --cap-drop ALL.
- unshare fallback: tmpfs new root + same binds + pivot_root + setpriv (fail-closed 97).
- cache keys: "sandbox hermetic-v2" added to result-cache hashes.
- Tests: cmd/janus/hermetic_test.go.

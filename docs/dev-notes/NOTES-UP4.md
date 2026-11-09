# NOTES-UP4 (hermetic sandbox) -- branch agent/up4-sandbox, base b8ac6cca
- Design: cmd/janus/sandbox.go bwrap = empty root + allowlist ro binds (/usr,/bin,/lib*,/sbin symlinks, minimal /etc,
  /usr/local masked), toolchain sysroot, LEAN_PATH dirs, argv[0] dir, protected, writable; private /tmp,/dev,/proc;
  --clearenv + allowlisted env (PATH, LEAN_*, LAKE_*, GIT_*, LC_*, LANG, TZ, TERM, HOME=/tmp); --cap-drop ALL.
- unshare fallback: tmpfs new root + same binds + pivot_root + setpriv (fail-closed 97).
- cache keys: "sandbox hermetic-v2" added to result-cache hashes.
- Tests: cmd/janus/hermetic_test.go.

## Accepted nondeterminism (cannot be removed; does not affect soundness, the kernel check decides)
clock (monotonic/wall), random bytes, uid 0, and the host-wide contents of /proc/{cpuinfo,meminfo,loadavg}.
Everything else host-specific is hidden: empty root + allowlist ro binds, env allowlist (PATH scrubbed, HOME=/tmp),
private pid/ipc/uts/user/net ns, caps dropped, caller fds > 2 marked CLOEXEC (closeInheritedFDs).
Toolchain selection: findToolchain runs in the framework lease dir and consumers with a differing lean-toolchain are refused (consumer.go), not changed.

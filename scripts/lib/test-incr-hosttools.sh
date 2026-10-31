#!/usr/bin/env bash
# Mutation tests of incr_hosttools (scripts/lib/incr.sh): the host compiler/linker/loader/libc and LD_PRELOAD/LD_LIBRARY_PATH are part of every lane key.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$here"
mkdir -p artifacts; t="$(mktemp -d "$here/artifacts/test-incr-hosttools.XXXXXX")" || exit 2
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
. scripts/lib/incr.sh
base="$(incr_hosttools)"
[ "$base" = "$(incr_hosttools 2>/dev/null)" ] && ok "deterministic: two calls give the same digest" || bad "not deterministic"
# 1. a compiler shim at the SAME path (a dir put first on PATH holds gcc; its bytes change between two runs)
mkdir -p "$t/bin"; printf '#!/bin/sh\nexec /usr/bin/gcc "$@"\n# A\n' > "$t/bin/gcc"; chmod +x "$t/bin/gcc"
a="$(PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
printf '#!/bin/sh\nexec /usr/bin/gcc "$@"\n# B\n' > "$t/bin/gcc"
b="$(PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
[ "$a" != "$base" ] && [ "$a" != "$b" ] && ok "a compiler shim, and a changed shim at the same path, change the digest" || bad "compiler shim not noticed"
# the same shim bytes under a PATH-cache file (INCR_HOSTTOOLS_CACHE) must not serve a stale digest when PATH changes
c="$t/cache"; : > "$c"; c1="$(INCR_HOSTTOOLS_CACHE=$c incr_hosttools 2>/dev/null)"; c2="$(INCR_HOSTTOOLS_CACHE=$c incr_hosttools 2>/dev/null)"
c3="$(INCR_HOSTTOOLS_CACHE=$c PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
[ "$c1" = "$base" ] && [ "$c1" = "$c2" ] && [ "$c3" = "$b" ] && ok "the per-run cache serves the same digest, and is bypassed when PATH changes" || bad "cache: $c1 $c2 $c3"
# 2. the linker (CC points at another gcc-like binary: $CC is hashed)
printf '#!/bin/sh\nexec /usr/bin/ld "$@"\n' > "$t/bin/myld"; chmod +x "$t/bin/myld"
l1="$(PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"; printf '#!/bin/sh\nexec /usr/bin/ld "$@" \n#x\n' > "$t/bin/myld"
# (a shim named ld first on PATH)
cp "$t/bin/myld" "$t/bin/ld"; l2="$(PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"; echo "# y" >> "$t/bin/ld"; l3="$(PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
[ "$l2" != "$base" ] && [ "$l2" != "$l3" ] && ok "a linker shim, and a changed one, change the digest" || bad "linker shim not noticed"
# 3. the dynamic loader / libc: run a copy of incr.sh whose loader paths point at a scratch dir
ld="$(ls /lib64/ld-linux-*.so.* /lib/*-linux-gnu/ld-linux-*.so.* 2>/dev/null | head -n 1)"
mkdir -p "$t/sys"; cp "$(readlink -f "$ld")" "$t/sys/ld-linux-x.so.2"
sed -e "s#/lib64/ld-linux-\*\.so\.\*#$t/sys/ld-linux-x.so.2#" -e "s#/lib/ld-linux-\*\.so\.\*#/nonexistent#" -e "s#/lib/\*-linux-gnu/ld-linux-\*\.so\.\*#/nonexistent#" scripts/lib/incr.sh > "$t/incr2.sh"
grep -q "$t/sys/ld-linux-x.so.2" "$t/incr2.sh" || bad "test setup: loader path not substituted"
s1="$(. "$t/incr2.sh"; incr_hosttools 2>/dev/null)"; echo X >> "$t/sys/ld-linux-x.so.2"; s2="$(. "$t/incr2.sh"; incr_hosttools 2>/dev/null)"
[ "$s1" != "$s2" ] && ok "a changed ld.so changes the digest" || bad "ld.so change not noticed"
# 4. LD_PRELOAD / LD_LIBRARY_PATH
echo one > "$t/p.so"; p1="$(LD_PRELOAD="$t/p.so" incr_hosttools 2>/dev/null)"; echo two > "$t/p.so"; p2="$(LD_PRELOAD="$t/p.so" incr_hosttools 2>/dev/null)"
[ "$p1" != "$base" ] && [ "$p1" != "$p2" ] && ok "LD_PRELOAD (value, and the bytes of the file it names) changes the digest" || bad "LD_PRELOAD not noticed"
n1="$(LD_PRELOAD=/nonexistent/x.so incr_hosttools 2>/dev/null)"; n2="$(LD_PRELOAD=/nonexistent/x.so incr_hosttools 2>/dev/null)"
[ "$n1" != "$n2" ] && ok "LD_PRELOAD naming an unreadable file forces a miss" || bad "unreadable preload not a miss"
mkdir -p "$t/lib"; echo a > "$t/lib/libz.so"; q1="$(LD_LIBRARY_PATH="$t/lib" incr_hosttools 2>/dev/null)"; echo b > "$t/lib/libz.so"; q2="$(LD_LIBRARY_PATH="$t/lib" incr_hosttools 2>/dev/null)"
[ "$q1" != "$base" ] && [ "$q1" != "$q2" ] && ok "LD_LIBRARY_PATH (value and the files below it) changes the digest" || bad "LD_LIBRARY_PATH not noticed"
[ "$(LD_PRELOAD= LD_LIBRARY_PATH= incr_hosttools 2>/dev/null)" = "$base" ] && ok "empty LD_PRELOAD/LD_LIBRARY_PATH: same digest as unset" || bad "empty values change the digest"
# 5. the lane spec carries it, on one line
incr_lane_spec t | grep -q '^hosttools:tools=[0-9a-f]\{64\}' && ok "incr_lane_spec carries hosttools" || bad "lane spec lacks hosttools"
[ "$fail" = 0 ] && echo "all checks passed"; exit $fail

#!/usr/bin/env bash
# Mutation tests of incr_hosttools (scripts/lib/incr-host.sh) and the other lane-key inputs of scripts/lib/incr.sh: the host compiler, linker, loader,
# libc, Go toolchain, compiler-steering environment, dependency trees and LD_* variables are part of every lane key; lanes are skipped only on opt-in.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$here"
mkdir -p artifacts; t="$(mktemp -d "$here/artifacts/test-incr-hosttools.XXXXXX")" || exit 2
trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
# HERMETIC: nothing the gate (or an operator) exported may reach the digest, and nothing another lane writes concurrently may be read:
# the gate-exported cache file, compiler/LD/Python variables are unset; the artifacts/ manifest root and the dependency trees are private empty directories
for v in INCR_HOSTTOOLS_CACHE INCR_NORECORD_FILE LD_PRELOAD LD_LIBRARY_PATH CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH OBJC_INCLUDE_PATH LIBRARY_PATH COMPILER_PATH GCC_EXEC_PREFIX \
  CFLAGS CXXFLAGS CPPFLAGS LDFLAGS BASH_ENV ENV PYTHONPATH PYTHONSTARTUP PYTHONHOME DEPS X86DEPS OPAMROOT ASL_CACHE MAKEFLAGS MAKEFILES SOURCE_DATE_EPOCH CC CXX AS LD AR \
  GIT_CONFIG GIT_CONFIG_GLOBAL GIT_EXEC_PATH PKG_CONFIG_PATH PKG_CONFIG_LIBDIR JANUS_INCR_LANES JANUS_GATE_TREE0 JANUS_GATE_INCREMENTAL IH_MAX_FILES IH_MAX_BYTES; do unset "$v"; done
for v in $(compgen -e); do case "$v" in CCACHE_*|DISTCC_*|PYTHON*|OPAM*|GCC_*|ICECC*) unset "$v" ;; esac; done
mkdir -p "$t/iroot" "$t/nodeps" "$t/sysbin"
# a PATH without the heavy toolchains no test needs (qemu-*, clang, the cross gcc family): each full digest costs seconds under load
for f in /usr/bin/* /usr/local/go/bin/* "$(dirname "$(type -P go)")"/*; do
  b="${f##*/}"; case "$b" in qemu-*|*clang*|aarch64-*|x86_64-linux-gnu-*|*ccache*|*distcc*) continue ;; esac
  [ -e "$t/sysbin/$b" ] || ln -s "$f" "$t/sysbin/$b" 2>/dev/null
done
mkdir -p "$t/bin"
export PATH="$t/bin:$t/sysbin"
export IH_ROOT="$t/iroot" DEPS="$t/nodeps" X86DEPS="$t/nodeps"
. scripts/lib/incr.sh
H() { incr_hosttools --nocache 2>/dev/null; }
base="$(H)"
[ "$base" = "$(H)" ] && [[ "$base" =~ ^tools=[0-9a-f]{64}$ ]] && ok "deterministic and well-formed" || bad "not deterministic: $base"
differs() { local what=$1 x=$2 y=${3:-$base}; if [ "$x" != "$y" ]; then ok "$what"; else bad "$what: digest unchanged"; fi; }
fakegcc() { # TAG [PROG] [FILE]: a gcc front that forwards to the real gcc except for what it reports itself
  cat > "$t/bin/gcc" <<EOS
#!/bin/sh
case "\$1" in
  -print-prog-name=cc1) echo "$t/cc1x"; exit 0 ;;
  -print-file-name=crt1.o) echo "$t/crt1x"; exit 0 ;;
  --version) cat "$t/vtext"; exit 0 ;;
esac
exec /usr/bin/gcc "\$@"
# $1
EOS
  chmod +x "$t/bin/gcc"
}
echo A > "$t/cc1x"; echo A > "$t/crt1x"
fakegcc v1; g1="$(PATH="$t/bin:$PATH" H)"; differs "a compiler shim at the same path changes the digest" "$g1"
fakegcc v2; g2="$(PATH="$t/bin:$PATH" H)"; differs "a changed shim at the same path changes it again" "$g2" "$g1"
echo B > "$t/cc1x"; g3="$(PATH="$t/bin:$PATH" H)"; differs "-print-prog-name (the file the compiler names as cc1) is hashed" "$g3" "$g2"
echo B > "$t/crt1x"; g4="$(PATH="$t/bin:$PATH" H)"; differs "-print-file-name (crt1.o) is hashed" "$g4" "$g3"
# the --version text alone (the shim bytes stay the same)
echo "gcc 1.0" > "$t/vtext"; fakegcc v3; gv1="$(PATH="$t/bin:$PATH" H)"; echo "gcc 2.0" > "$t/vtext"; gv2="$(PATH="$t/bin:$PATH" H)"
differs "the --version text is part of the digest" "$gv2" "$gv1"
# $CC / $CXX words: the first word names a compiler found via PATH
printf '#!/bin/sh\nexec /usr/bin/gcc "$@"\n# 1\n' > "$t/bin/mycc"; chmod +x "$t/bin/mycc"
c1="$(CC='mycc -m64' PATH="$t/bin:$PATH" H)"; printf '# 2\n' >> "$t/bin/mycc"; c2="$(CC='mycc -m64' PATH="$t/bin:$PATH" H)"
differs "\$CC's first word is resolved and hashed" "$c1" "$c2"; differs "\$CC is part of the digest" "$c1" "$(PATH="$t/bin:$PATH" H)"
printf '#!/bin/sh\nexec /usr/bin/g++ "$@"\n# 1\n' > "$t/bin/mycxx"; chmod +x "$t/bin/mycxx"
x1="$(CXX=mycxx PATH="$t/bin:$PATH" H)"; printf '# 2\n' >> "$t/bin/mycxx"; x2="$(CXX=mycxx PATH="$t/bin:$PATH" H)"
differs "\$CXX is resolved and hashed" "$x1" "$x2"
rm -f "$t/bin/gcc" "$t/bin/mycc" "$t/bin/mycxx"
# the linker, objdump, python3, qemu, bwrap, git, make (any of the keyed tools) as a shim
for tool in ld objdump python3 qemu-aarch64 git make; do
  printf '#!/bin/sh\nexec /bin/true\n# a\n' > "$t/bin/$tool"; chmod +x "$t/bin/$tool"; a="$(H)"
  if [ "$tool" = ld ]; then printf '# b\n' >> "$t/bin/$tool"; b="$(H)"; differs "a changed $tool shim changes it again" "$a" "$b"; fi
  rm -f "$t/bin/$tool"; differs "a shim $tool at the same path changes the digest" "$a" "$base"
done
# the Go toolchain: a `go` shim (its bytes), and the tool directory / GOROOT through a copy of GOROOT's layout
printf '#!/bin/sh\nexec %s "$@"\n# 1\n' "$(type -P go)" > "$t/bin/go"; chmod +x "$t/bin/go"; o1="$(PATH="$t/bin:$PATH" H)"; printf '# 2\n' >> "$t/bin/go"; o2="$(PATH="$t/bin:$PATH" H)"
differs "a go shim changes the digest" "$o1" "$base"; differs "a changed go shim changes it" "$o1" "$o2"; rm -f "$t/bin/go"
fakeroot="$t/goroot"; mkdir -p "$fakeroot/pkg/tool/x" "$fakeroot/src" "$fakeroot/bin"; echo 1.0 > "$fakeroot/VERSION"; echo c1 > "$fakeroot/pkg/tool/x/compile"; echo m > "$fakeroot/src/a.go"
printf '#!/bin/sh\nif [ "$1 $2" = "env GOROOT" ]; then echo %s; elif [ "$1 $2" = "env GOTOOLDIR" ]; then echo %s/pkg/tool/x; else exec %s "$@"; fi\n' "$fakeroot" "$fakeroot" "$(type -P go)" > "$t/bin/go"; chmod +x "$t/bin/go"
r1="$(PATH="$t/bin:$PATH" H)"; echo c2 > "$fakeroot/pkg/tool/x/compile"; r2="$(PATH="$t/bin:$PATH" H)"; echo m2 > "$fakeroot/src/a.go"; r3="$(PATH="$t/bin:$PATH" H)"
differs "a changed Go tool (compile) changes the digest" "$r2" "$r1"; differs "a changed GOROOT source changes it" "$r3" "$r2"; rm -f "$t/bin/go"
# the dynamic loader / libc (a copy of the library files with the loader paths pointed at a scratch dir)
ld="$(ls /lib64/ld-linux-*.so.* /lib/*-linux-gnu/ld-linux-*.so.* 2>/dev/null | head -n 1)"
mkdir -p "$t/lib" "$t/sys"; cp scripts/lib/incr.sh scripts/lib/incr-host.sh "$t/lib/"; cp "$(readlink -f "$ld")" "$t/sys/ld-linux-x.so.2"
sed -i -e "s#/lib64/ld-linux-\*\.so\.\*#$t/sys/ld-linux-x.so.2#" -e "s#/lib/ld-linux-\*\.so\.\*#/nonexistent#" -e "s#/lib/\*-linux-gnu/ld-linux-\*\.so\.\*#/nonexistent#" "$t/lib/incr-host.sh"
grep -q "$t/sys/ld-linux-x.so.2" "$t/lib/incr-host.sh" || bad "test setup: loader path not substituted"
s1="$(. "$t/lib/incr.sh"; incr_hosttools --nocache 2>/dev/null)"; echo X >> "$t/sys/ld-linux-x.so.2"; s2="$(. "$t/lib/incr.sh"; incr_hosttools --nocache 2>/dev/null)"
differs "a changed ld.so changes the digest" "$s2" "$s1"
# the ldd / libc lines: an ldd shim naming a libc file
echo L1 > "$t/libcx"; printf '#!/bin/sh\necho "\tlibc.so.6 => %s/libcx (0x0)"\n' "$t" > "$t/bin/ldd"; chmod +x "$t/bin/ldd"
d1="$(PATH="$t/bin:$PATH" H)"; echo L2 > "$t/libcx"; d2="$(PATH="$t/bin:$PATH" H)"; differs "the libc found by ldd is hashed" "$d2" "$d1"; rm -f "$t/bin/ldd"
# /usr/include and compiler-steering environment, by value and by the content they name
mkdir -p "$t/inc"; echo '#define A 1' > "$t/inc/h.h"
e0="$(H)"; e1="$(CPATH="$t/inc" H)"; echo '#define A 2' > "$t/inc/h.h"; e2="$(CPATH="$t/inc" H)"
differs "CPATH changes the digest" "$e1" "$e0"; differs "the header CPATH names is hashed" "$e2" "$e1"
for v in C_INCLUDE_PATH CPLUS_INCLUDE_PATH LIBRARY_PATH COMPILER_PATH CFLAGS CXXFLAGS CPPFLAGS LDFLAGS PYTHONPATH PYTHONSTARTUP; do
  [ "$(env "$v=$t/inc" bash -c '. scripts/lib/incr.sh; _ih_env' 2>/dev/null)" != "$(bash -c '. scripts/lib/incr.sh; _ih_env' 2>/dev/null)" ] && ok "$v enters the environment part of the digest (_ih_env; the whole digest is the hash of it and the other parts)" || bad "$v not keyed"
done
echo 'echo hi' > "$t/benv"; b1="$(BASH_ENV="$t/benv" H)"; echo 'echo ho' > "$t/benv"; b2="$(BASH_ENV="$t/benv" H)"; differs "BASH_ENV and the file it names are keyed" "$b2" "$b1"
echo c > "$t/starts"; p1="$(PYTHONSTARTUP="$t/starts" H)"; echo d > "$t/starts"; p2="$(PYTHONSTARTUP="$t/starts" H)"; differs "PYTHONSTARTUP content is keyed" "$p2" "$p1"
# the dependency trees: X86DEPS (a scratch tree) and DEPS (Sail sources + opam switch binaries)
mkdir -p "$t/x86"; echo m1 > "$t/x86/model"; y1="$(X86DEPS="$t/x86" H)"; echo m2 > "$t/x86/model"; y2="$(X86DEPS="$t/x86" H)"; differs "X86DEPS content is keyed" "$y2" "$y1"
mkdir -p "$t/deps/sail-arm-abc1234/arm-v9.4-a/src" "$t/deps/opam/sw/bin"; echo s1 > "$t/deps/sail-arm-abc1234/arm-v9.4-a/src/a.sail"; echo b1 > "$t/deps/opam/sw/bin/sail"
z1="$(DEPS="$t/deps" H)"; echo s2 > "$t/deps/sail-arm-abc1234/arm-v9.4-a/src/a.sail"; z2="$(DEPS="$t/deps" H)"; echo b2 > "$t/deps/opam/sw/bin/sail"; z3="$(DEPS="$t/deps" H)"
differs "a Sail source under DEPS is keyed" "$z2" "$z1"; differs "the opam Sail binary under DEPS is keyed" "$z3" "$z2"
# a ccache/distcc launcher in front is a forced miss
l1="$(CC='ccache gcc' H)"; l2="$(CC='ccache gcc' H)"; [ "$l1" != "$l2" ] && ok "a compiler launcher (ccache) forces a miss" || bad "ccache launcher accepted"
# LD_PRELOAD / LD_LIBRARY_PATH
echo one > "$t/p.so"; p1="$(LD_PRELOAD="$t/p.so" H)"; echo two > "$t/p.so"; p2="$(LD_PRELOAD="$t/p.so" H)"
differs "LD_PRELOAD (value, and the bytes of the file it names) changes the digest" "$p1" "$base"; differs "a changed preload file" "$p2" "$p1"
n1="$(LD_PRELOAD=/nonexistent/x.so H)"; n2="$(LD_PRELOAD=/nonexistent/x.so H)"; differs "LD_PRELOAD naming an unreadable file forces a miss" "$n1" "$n2"
mkdir -p "$t/ll"; echo a > "$t/ll/libz.so"; q1="$(LD_LIBRARY_PATH="$t/ll" H)"; echo b > "$t/ll/libz.so"; q2="$(LD_LIBRARY_PATH="$t/ll" H)"
differs "LD_LIBRARY_PATH (value and the files below it) changes the digest" "$q2" "$q1"
# symlinked entries: a file symlink and a directory symlink inside the path, and the entry itself a symlink
mkdir -p "$t/real" "$t/lp"; echo s1 > "$t/real/libs.so"; ln -s "$t/real" "$t/lp/dirlink"; ln -s "$t/real/libs.so" "$t/lp/filelink"; ln -s "$t/lp" "$t/lpl"
k1="$(LD_LIBRARY_PATH="$t/lpl" H)"; echo s2 > "$t/real/libs.so"; k2="$(LD_LIBRARY_PATH="$t/lpl" H)"
differs "symlinked LD_LIBRARY_PATH entries (to files and directories) are followed" "$k2" "$k1"
[ "$(LD_PRELOAD= LD_LIBRARY_PATH= H)" = "$(H)" ] && ok "empty LD_PRELOAD/LD_LIBRARY_PATH: same digest as unset" || bad "empty values change the digest"
# the cap: a tree above the limit is a forced miss
mkdir -p "$t/big"; for i in 1 2 3; do echo $i > "$t/big/f$i"; done
m1="$(IH_MAX_FILES=2 CPATH="$t/big" H)"; m2="$(IH_MAX_FILES=2 CPATH="$t/big" H)"; differs "a tree above the file cap is a forced miss" "$m1" "$m2"
# the cache cannot freeze a changed tool: same size, mtime restored; the stamp holds inode, size, mtime AND ctime
printf '#!/bin/sh\nexec /bin/true\n# aaaa\n' > "$t/bin/make"; chmod +x "$t/bin/make"; touch -d '2020-01-01' "$t/bin/make"
cf="$t/cache"; : > "$cf"; f1="$(INCR_HOSTTOOLS_CACHE=$cf PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"; f1b="$(INCR_HOSTTOOLS_CACHE=$cf PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
printf '#!/bin/sh\nexec /bin/true\n# bbbb\n' > "$t/bin/make"; touch -d '2020-01-01' "$t/bin/make"
f2="$(INCR_HOSTTOOLS_CACHE=$cf PATH="$t/bin:$PATH" incr_hosttools 2>/dev/null)"
[ "$f1" = "$f1b" ] && ok "the per-run cache serves the same digest" || bad "cache not stable"
differs "a same-size, same-mtime replacement of a hashed binary is not served from the cache" "$f2" "$f1"
printf 'garbage\nnot-a-digest\n' > "$cf"; stamp0="$(_ih_stamp)"; printf '%s\nnot-a-digest\n' "$stamp0" > "$cf.m"
[[ "$(INCR_HOSTTOOLS_CACHE=$cf incr_hosttools 2>/dev/null)" == "$(H)" ]] && [[ "$(INCR_HOSTTOOLS_CACHE=$cf.m incr_hosttools 2>/dev/null)" == "$(H)" ]] && ok "a malformed cache line is ignored (recomputed)" || bad "malformed cache accepted"
rm -f "$t/bin/make"
# the lane spec: carries hosttools; one line per argument; _incr_oneline is injective; GOGCCFLAGS-only normalisation
spec_out="$(incr_lane_spec t)"; grep -q '^hosttools:tools=[0-9a-f]\{64\}' <<<"$spec_out" && ok "incr_lane_spec carries hosttools" || bad "lane spec lacks hosttools"
a="$(printf 'a\001b' | _incr_oneline | od -An -c | tr -d ' ')"; b="$(printf 'a\nb' | _incr_oneline | od -An -c | tr -d ' ')"; c="$(printf 'a\002b' | _incr_oneline | od -An -c | tr -d ' ')"
{ [ "$a" != "$b" ] && [ "$a" != "$c" ] && [ "$b" != "$c" ]; } && ok "_incr_oneline: a raw \\001, a newline and a raw \\002 stay distinct" || bad "oneline not injective: $a $b $c"
k_a="$(HOME="$t/go-build1" incr_lane_spec t | grep '^goenv:' | sha256sum)"; k_b="$(HOME="$t/go-build2" incr_lane_spec t | grep '^goenv:' | sha256sum)"; k_c="$(HOME="$t/go-build" incr_lane_spec t | grep '^goenv:' | sha256sum)"
{ [ "$k_a" != "$k_b" ] && [ "$k_a" != "$k_c" ] && [ "$k_b" != "$k_c" ]; } && ok "HOME=.../go-build1, go-build2 and go-build give different goenv arguments (only GOGCCFLAGS is normalised)" || bad "go-build rewrite is not confined to GOGCCFLAGS"
# lane skipping is OFF by default: with the default setting incr_lane always runs the code, reads and writes no record
export JANUS_GATE_TREE0=forged
d="$(mktemp -d "$t/lanes.XXXXXX")"; ( cd "$here" && JANUS_INCR_RECORD=1 JANUS_GATE_INCREMENTAL=1 JANUS_CACHE_DIR="$d/cache" bash -c '. scripts/lib/incr.sh; n=0; for i in 1 2 3; do incr_lane t1 "echo ran >> '"$d"'/log" >/dev/null; done; wc -l < '"$d"'/log' ) > "$d/out" 2>&1
[ "$(tail -n 1 "$d/out")" = 3 ] && ok "default (JANUS_INCR_LANES unset): the lane ran all 3 times, none skipped" || bad "lane skipped by default: $(cat "$d/out")"
grep -q 'JANUS_INCR_LANES' scripts/gate.sh && grep -q 'OFF (default' scripts/gate.sh && ok "the gate banner states the lane setting" || bad "banner lacks the setting"
unset JANUS_GATE_TREE0
# SKIP-as-pass: gotest-shards.sh reports skipped tests and leaves a no-record note
grep -q 'INCR_NORECORD_FILE' scripts/gotest-shards.sh && grep -q 'a skip is not a pass' scripts/gotest-shards.sh && ok "gotest-shards.sh never lets a run with a SKIP be recorded" || bad "SKIP-as-pass not guarded"
nr="$(mktemp "$t/nr.XXXXXX")"; echo "gotest: 2 skipped" > "$nr"
( cd "$here"; JANUS_INCR_LANES=1 JANUS_INCR_RECORD=1 JANUS_GATE_INCREMENTAL=1 bash -c '. scripts/lib/incr.sh; incr_tree_ok() { return 0; }; incr_active() { return 0; }; incr_begin() { return 1; }; incr_end() { echo RECORDED; }; incr_lane lanex '"'"'echo x >> "$INCR_NORECORD_FILE"'"'"'' ) > "$t/nr.out" 2>&1
grep -q 'not recorded: x' "$t/nr.out" && ! grep -q RECORDED "$t/nr.out" && ok "a lane that wrote to INCR_NORECORD_FILE is not recorded" || bad "norecord ignored: $(cat "$t/nr.out")"
[ "$fail" = 0 ] && echo "all checks passed"; exit $fail

#!/usr/bin/env bash
# Red team of the Sail driver cache key (oracle-sail/cache_key.py): toolchain swaps that keep the version
# text, compiler/linker environment, parent cargo config. Each must change the key. mktemp, seconds.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-rt-bcache.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
mkdir -p "$t/k/oracle-sail/src" "$t/bin"
for f in Cargo.toml Cargo.lock instrument_model.py; do echo "x" > "$t/k/oracle-sail/$f"; done
echo 'fn main(){}' > "$t/k/oracle-sail/src/main.rs"
mk() { printf '#!/bin/sh\necho "%s"\n' "$2" > "$t/bin/$1"; chmod +x "$t/bin/$1"; }
mk rustc "rustc 1.90.0 (abc)"; mk cargo "cargo 1.90.0"; mk c++ "g++ 13.2"; mk cc "gcc 13.2"; mk ld "GNU ld 2.42"
key() { PATH="$t/bin:/usr/bin:/bin" python3 -I "$root/oracle-sail/cache_key.py" "$t/k" --pins crate_rev=x; }
k0=$(key); [ "$k0" = "$(key)" ] && ok "deterministic" || bad "unstable"
chg() { local d=$1; shift; "$@"; local k1; k1=$(key); [ "$k1" != "$k0" ] && ok "key changes: $d" || bad "STALE: key unchanged: $d"; k0=$(key); }
chg "rustc version text" mk rustc "rustc 1.91.0 (abc)"
chg "rustc binary swapped, same version text" bash -c "printf '#!/bin/sh\n# patched\necho \"rustc 1.91.0 (abc)\"\n' > $t/bin/rustc"
chg "cargo binary swapped, same version text" bash -c "printf '#!/bin/sh\n# patched\necho \"cargo 1.90.0\"\n' > $t/bin/cargo"
chg "C++ compiler swapped, same --version" bash -c "printf '#!/bin/sh\n# patched\necho \"g++ 13.2\"\n' > $t/bin/c++"
chg "linker cc swapped, same --version" bash -c "printf '#!/bin/sh\n# patched\necho \"gcc 13.2\"\n' > $t/bin/cc"
chg "ld swapped" bash -c "printf '#!/bin/sh\n# patched\necho \"GNU ld 2.42\"\n' > $t/bin/ld"
chg "Cargo.lock" bash -c "echo '# x' >> $t/k/oracle-sail/Cargo.lock"
chg "a source file" bash -c "echo '// x' >> $t/k/oracle-sail/src/main.rs"
chg "a new source file" bash -c "echo '// y' > $t/k/oracle-sail/src/extra.rs"
chg "parent .cargo/config (rustflags)" bash -c "mkdir -p $t/.cargo; printf '[build]\nrustflags=[\"-Cdebuginfo=2\"]\n' > $t/.cargo/config.toml"
for e in RUSTFLAGS=-Cdebuginfo=2 CXXFLAGS=-O0 CFLAGS=-O0 CC=gcc CXX=g++ LDFLAGS=-s CARGO_BUILD_RUSTFLAGS=-Cx RUSTUP_TOOLCHAIN=nightly LD_LIBRARY_PATH=/x CARGO_ENCODED_RUSTFLAGS=x; do
  a=$(key); b=$(export "$e"; key); [ "$a" != "$b" ] && ok "env $e" || bad "STALE: env $e unkeyed"
done

# ---- the ASL side: JanusASL/tools/asl_cache_key.py with a fake lean toolchain (prefix we can mutate) ----
tc="$t/tc"; mkdir -p "$tc/bin" "$tc/lib/lean/Init" "$tc/include/lean"
for b in lake leanc leanchecker clang ld.lld llvm-ar extra-tool; do printf '#!/bin/sh\necho %s\n' "$b" > "$tc/bin/$b"; chmod +x "$tc/bin/$b"; done
printf '#!/bin/sh\nif [ "$1" = --print-prefix ]; then echo %s; else echo "Lean (version 9.9.9)"; fi\n' "$tc" > "$tc/bin/lean"; chmod +x "$tc/bin/lean"
echo core > "$tc/lib/lean/Init.olean"; echo so > "$tc/lib/lean/libleanshared.so"; echo a > "$tc/lib/lean/libInit.a"; echo h > "$tc/include/lean/lean.h"; echo crt > "$tc/lib/crt1.o"
mkdir -p "$t/a/JanusASL/vendor" "$t/a/JanusASL/sail"; cp "$root/JanusASL/lakefile.toml" "$root/JanusASL/lake-manifest.json" "$root/JanusASL/lean-toolchain" "$t/a/JanusASL/"
cp "$root/JanusASL/vendor/ArmASL.tar.gz.sha256" "$t/a/JanusASL/vendor/"; cp "$root/JanusASL/sail/split_lean.py" "$t/a/JanusASL/sail/"; cp "$root/lean-toolchain" "$root/lakefile.toml" "$t/a/"
akey() { PATH="$tc/bin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_cache_key.py" "$t/a"; }
ak=$(akey); [ "$ak" = "$(akey)" ] && ok "ASL key deterministic" || bad "ASL key unstable"
achg() { local d=$1; shift; "$@"; local k1; k1=$(akey); [ "$k1" != "$ak" ] && ok "ASL key changes: $d" || bad "STALE: ASL key unchanged: $d"; ak=$(akey); }
achg "lake binary swapped (same name)" bash -c "printf '#!/bin/sh\n#p\necho lake\n' > $tc/bin/lake"
achg "clang (lake's C compiler for the native parts) swapped" bash -c "printf '#!/bin/sh\n#p\necho clang\n' > $tc/bin/clang"
achg "ld.lld swapped" bash -c "printf '#!/bin/sh\n#p\necho x\n' > $tc/bin/ld.lld"
achg "a binary not on any list (bin/extra-tool)" bash -c "printf '#!/bin/sh\n#p\n' > $tc/bin/extra-tool"
achg "a core .olean" bash -c "echo changed > $tc/lib/lean/Init.olean"
achg "libleanshared.so" bash -c "echo changed > $tc/lib/lean/libleanshared.so"
achg "a static library lean links (libInit.a)" bash -c "echo changed > $tc/lib/lean/libInit.a"
achg "a C header the generated C compiles against" bash -c "echo changed > $tc/include/lean/lean.h"
achg "a CRT object" bash -c "echo changed > $tc/lib/crt1.o"
achg "lean --version text" bash -c "sed -i 's/9.9.9/9.9.8/' $tc/bin/lean"
for e in LEAN_CC=gcc LEAN_CXX=g++ LAKE_HOME=/x LD_LIBRARY_PATH=/x LD_PRELOAD=/x LEAN_FOO=1 LAKE_NO_CACHE=1 CC=gcc CFLAGS=-O0 LDFLAGS=-s; do
  a=$(akey); b=$(export "$e"; akey); [ "$a" != "$b" ] && ok "ASL env $e" || bad "STALE: ASL env $e unkeyed"
done
mkdir -p "$t/sysbin"; printf '#!/bin/sh\necho cc1\n' > "$t/sysbin/cc"; chmod +x "$t/sysbin/cc"
a=$(PATH="$tc/bin:$t/sysbin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_cache_key.py" "$t/a"); printf '#!/bin/sh\necho cc2\n' > "$t/sysbin/cc"
b=$(PATH="$tc/bin:$t/sysbin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_cache_key.py" "$t/a"); [ "$a" != "$b" ] && ok "ASL key changes: system cc swapped" || bad "STALE: system cc"
# the module cache shares the toolchain digest and env: its keys move with them
mk_=$(PATH="$tc/bin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_mod_cache.py" keys "$root" 2>/dev/null | sha256sum)
echo changed-again > "$tc/lib/lean/libInit.a"
mk2=$(PATH="$tc/bin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_mod_cache.py" keys "$root" 2>/dev/null | sha256sum)
[ "$mk_" != "$mk2" ] && ok "module cache keys change with the toolchain content" || bad "STALE: module keys ignore the toolchain content"
# ---- scheduling-only variables are not keyed; everything else is (the gate lanes run LEAN_NUM_THREADS=4) ----
a=$(akey); b=$(export LEAN_NUM_THREADS=4; akey); [ "$a" = "$b" ] && ok "ASL key: LEAN_NUM_THREADS (the gate sets 4) does not change it" || bad "ASL key depends on LEAN_NUM_THREADS"
a=$(akey); b=$(export LEAN_NUM_THREADS=1; akey); [ "$a" = "$b" ] && ok "ASL key: LEAN_NUM_THREADS=1 equals unset" || bad "ASL key depends on LEAN_NUM_THREADS=1"
# the exact environment scripts/gate.sh exports for its lanes, against a bare standalone run
gate_env=$(sed -n 's/^export \(LEAN_NUM_THREADS\)="\${LEAN_NUM_THREADS:-4}".*/\1/p' "$root/scripts/gate.sh" | head -1)
[ "$gate_env" = LEAN_NUM_THREADS ] && ok "gate.sh still exports LEAN_NUM_THREADS (the case under test)" || bad "gate.sh no longer exports LEAN_NUM_THREADS: update this test"
a=$(env -i PATH="$tc/bin:/usr/bin:/bin" HOME="$HOME" python3 -I "$root/JanusASL/tools/asl_cache_key.py" "$t/a")
b=$(env -i PATH="$tc/bin:/usr/bin:/bin" HOME="$HOME" JANUS_JOBS=2 LEAN_NUM_THREADS=4 JANUS_GATE_PREBUILT=1 JANUS_EXAMPLES_PREBUILT=1 python3 -I "$root/JanusASL/tools/asl_cache_key.py" "$t/a")
[ "$a" = "$b" ] && ok "ASL key: the gate lane environment equals a standalone run" || bad "ASL key differs between gate lane env and standalone"
a=$(key); b=$(export CARGO_TERM_COLOR=always; key); [ "$a" = "$b" ] && ok "Sail key: terminal-only CARGO_TERM_COLOR is not keyed" || bad "Sail key depends on CARGO_TERM_COLOR"
a=$(key); b=$(export CARGO_BUILD_JOBS=4; key); [ "$a" != "$b" ] && ok "Sail key: CARGO_BUILD_JOBS stays keyed (no identity evidence yet)" || bad "Sail key ignores CARGO_BUILD_JOBS without evidence"
a=$(akey); b=$(export LEAN_NUM_THREADS=4 LEAN_CC=gcc; akey); [ "$a" != "$b" ] && ok "ASL key: other LEAN_* variables are still keyed" || bad "ASL key ignores LEAN_CC"
mk_a=$(PATH="$tc/bin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_mod_cache.py" keys "$root" 2>/dev/null | sha256sum)
mk_b=$(export LEAN_NUM_THREADS=4; PATH="$tc/bin:/usr/bin:/bin" python3 -I "$root/JanusASL/tools/asl_mod_cache.py" keys "$root" 2>/dev/null | sha256sum)
[ "$mk_a" = "$mk_b" ] && ok "module cache keys: LEAN_NUM_THREADS does not change them" || bad "module keys depend on LEAN_NUM_THREADS"
exit $fail

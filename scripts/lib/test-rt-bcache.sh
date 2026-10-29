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
exit $fail

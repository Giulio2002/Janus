#!/usr/bin/env bash
# Lay out the DecLib git dependency and the R5Proofs consumer package under $1 (a fresh dir).
# Usage: audit/round5/dep/setup.sh DIR JANUS_ROOT
set -eu
out="$1"; jr="$2"; here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tc="$(cat "$jr/lean-toolchain")"
g() { git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main -c protocol.file.allow=always "$@"; }
mkdir -p "$out/declib" "$out/consumer/R5Proofs"
cd "$out/declib"
printf 'name = "declib"\ndefaultTargets = ["DecLib"]\n\n[[lean_lib]]\nname = "DecLib"\n' > lakefile.toml
echo "$tc" > lean-toolchain; echo ".lake/" > .gitignore
cp "$here/DecLib.lean" DecLib.lean
g init -q; g add -A; g commit -q -m declib
rev="$(g rev-parse HEAD)"
cd "$out/consumer"
echo "$tc" > lean-toolchain
cat > lakefile.toml <<TOML
name = "r5proofs"

[[require]]
name = "janus"
path = "$jr"

[[require]]
name = "declib"
git = "file://$out/declib"
rev = "$rev"

[[lean_lib]]
name = "R5Proofs"
TOML
cp "$here/Proofs.lean" R5Proofs/Proofs.lean
GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=protocol.file.allow GIT_CONFIG_VALUE_0=always lake update >/dev/null 2>&1
echo "$out/consumer"

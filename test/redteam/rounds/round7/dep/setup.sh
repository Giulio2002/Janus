#!/usr/bin/env bash
# Lay out the MisLib git dependency and the R7Proofs consumer package under $1 (a fresh dir).
# Usage: audit/round7/dep/setup.sh DIR JANUS_ROOT
set -eu
out="$1"; jr="$2"; here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tc="$(cat "$jr/lean-toolchain")"
g() { git -c user.name=t -c user.email=t@t -c commit.gpgsign=false -c init.defaultBranch=main -c protocol.file.allow=always "$@"; }
mkdir -p "$out/mislib" "$out/consumer/R7Proofs"
cd "$out/mislib"
printf 'name = "mislib"\ndefaultTargets = ["MisLib"]\n\n[[lean_lib]]\nname = "MisLib"\n' > lakefile.toml
echo "$tc" > lean-toolchain; echo ".lake/" > .gitignore
cp "$here/MisLib.lean" MisLib.lean
g init -q; g add -A; g commit -q -m mislib
rev="$(g rev-parse HEAD)"
cd "$out/consumer"
echo "$tc" > lean-toolchain
cat > lakefile.toml <<TOML
name = "r7proofs"

[[require]]
name = "janus"
path = "$jr"

[[require]]
name = "mislib"
git = "file://$out/mislib"
rev = "$rev"

[[lean_lib]]
name = "R7Proofs"
TOML
cp "$here/Proofs.lean" R7Proofs/Proofs.lean
GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=protocol.file.allow GIT_CONFIG_VALUE_0=always lake update >/dev/null 2>&1
echo "$out/consumer"

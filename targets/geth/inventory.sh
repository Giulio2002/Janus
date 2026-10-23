#!/usr/bin/env bash
# Regenerate the opcode table of targets/geth/INVENTORY.md.
#
#   targets/geth/build.sh && targets/geth/inventory.sh > /tmp/table.md
#
# Extracts every opcode function with `janus extract` into $OUT/<opcode> (default
# artifacts/geth), runs `janus blockers` over them (needs Lean/lake), and prints the
# markdown table. Scouting aid only: the trusted path is janus extract/check/verify.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
export PATH="$PATH:/usr/local/go/bin:$HOME/.elan/bin"
OUT="${OUT:-$root/artifacts/geth}"
BIN="$here/bin/geth-vm-arm64"
OPS="opAdd opSub opMul opLt opGt opEq opIszero opAnd opOr opXor opNot opByte opSHL opSHR opSAR
opSignExtend opSlt opSgt opDiv opSdiv opMod opSmod opAddmod opMulmod opExp"
(cd "$root" && go build -o bin/janus ./cmd/janus)
mkdir -p "$OUT"
syms=()
for op in $OPS; do
  sym="github.com/ethereum/go-ethereum/core/vm.$op"
  syms+=("$sym")
  "$root/bin/janus" extract "$BIN" "$sym" "$OUT/$op" > /dev/null 2> "$OUT/$op.warnings" ||
    echo "extract $op failed (see $OUT/$op.warnings)" >&2
done
"$root/bin/janus" blockers "$BIN" "${syms[@]}" --janus-root "$root" --json "$OUT/blockers.json" > "$OUT/blockers.txt"
python3 -I - "$OUT" $OPS <<'PY'
import json, os, sys
out, ops = sys.argv[1], sys.argv[2:]
bl = {s["symbol"].rsplit(".", 1)[1]: s for s in json.load(open(os.path.join(out, "blockers.json")))["symbols"]}
short = lambda n: n.replace("github.com/holiman/uint256.", "uint256.").replace("github.com/ethereum/go-ethereum/core/vm.", "vm.")
print("| Opcode fn | Instrs (entry) | Funcs | Instrs (total) | Callees | Stubs | Read-only data | Writable refs (not copied) | Lean decode | ≤ 64 funcs |")
print("|---|---|---|---|---|---|---|---|---|---|")
for op in ops:
    p = os.path.join(out, op, "identity.json")
    if not os.path.exists(p):
        print(f"| `{op}` | extraction failed | | | | | | | | no |"); continue
    d = json.load(open(p))
    fs = d["functions"]
    callees = ", ".join(f"`{short(f['name'])}`" for f in fs[1:]) or "-"
    stubs = ", ".join(sorted({s["name"].replace("runtime.", "rt.").replace("_noctxt.abi0", "_noctxt") for s in d["stubs"]})) or "-"
    data = ", ".join(f"{x['size']} B at {x['address']} ({x['section']})" for x in d["data"]) or "-"
    wr = sorted({f"`{s['symbol']}`" for s in d["skippedData"] if s["reason"] == "writable"})
    b = bl[op]
    dec = "all ok" if not b["rejected"] and not b.get("error") else f"{len(b['rejected'])} rejected"
    print(f"| `{op}` | {fs[0]['words']} | {len(fs)} | {sum(f['words'] for f in fs)} | {callees} | {stubs} | {data} | {', '.join(wr) or '-'} | {dec} | {'yes' if len(fs) <= 64 else 'no'} |")
PY

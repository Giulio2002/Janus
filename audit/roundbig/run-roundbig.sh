#!/usr/bin/env bash
# Regression rows for tree-shaped Extracted.lean files (a code segment, data object or global of more than 4096
# elements is written as a tree of generated `def seg<i>_<words|bytes>_<k>` chunk definitions joined by `++`).
# The chunks are new generated constants in the trusted `Extracted` / `JanusTrusted` modules, so:
#   control     a statement about the extracted code verifies (the chunks are read through Extracted.program only)
#   ChunkNew    a proof module declaring a new name under Extracted (a chunk the generator never emitted) is blocked
#   ChunkDup    a proof module re-declaring a generated chunk is rejected by Lean itself ("already declared")
#   ChunkEqn    an eq_1 theorem about a chunk the Extracted module does not declare is blocked (equation-lemma exemption is
#               exact: only c.eq_<k>/c.eq_def of a declared constant)
#   ChunkLookalike  a lookalike-letter namespace (Greek capital epsilon, which Lean accepts as an identifier letter) is rejected
#               by the AUDITOR's shadow rule, not by Lean (the row fails if Lean is the one rejecting it)
#   forgeByte   one byte of one chunk edited in Extracted.lean (identity.json hash updated): `janus check` and `janus
#               verify` reject it ("differs from the regenerated extraction"): the chunk contents are pinned
#   forgeSwap   two chunks of the same segment exchanged: rejected the same way
#   forgeName   a chunk renamed consistently (defs and uses): rejected the same way (the generated text is compared whole)
#   trust       the defeq check Extracted.program =?= JanusTrusted.program covers every chunk (it unfolds them): the forged
#               rows above fail BEFORE the kernel check as well as at the auditor when only the text check is bypassed
# Also prints the elaboration/verify time of the control for two sizes (linear scaling). Exits 1 if an attack verifies,
# a control stops verifying, or a forgery is accepted. Private temporary cache.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/roundbig
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundbig.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
# a Go program with one long straight-line function (more than 4096 words / bytes of code)
gen() { # LINES DIR
  mkdir -p "$2"
  { echo 'module example.com/big'; echo 'go 1.21'; } > "$2/go.mod"
  { echo 'package main'; echo '//go:noinline'; echo 'func Big(x *[4096]uint64) uint64 {'; echo '	var s uint64'
    for ((i = 0; i < $1; i++)); do echo "	s += x[$((i % 4096))] ^ (s >> $(((i % 7) + 1)))"; done
    echo '	return s'; echo '}'; echo 'func main() { var x [4096]uint64; println(Big(&x)) }'; } > "$2/main.go"
}
build() { # ARCH LINES NAME
  gen "$2" "$T/src$3"
  (cd "$T/src$3" && CGO_ENABLED=0 GOOS=linux GOARCH="$1" go build -trimpath -buildvcs=false -o "$root/$W/bin$3" .) || exit 1
}
broken=()
v() { "$J" verify --fresh --janus-root "$root" "$@" 2>&1; }
row() { # NAME expect(blocked|Verified) OUTPUT pattern...
  local name=$1 expect=$2 out=$3 verdict status="" pat; shift 3
  verdict="$(grep -m1 -E '^=== |^Error|^Rejected|^Invalid|^Verified' <<<"$out" | cut -c1-120)"
  [ -n "$verdict" ] || { verdict="(no verdict)"; status=BROKEN; }
  case $expect in
    blocked) case $verdict in *verified*|*Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in *verified*|*Verified*) ;; *) status=BROKEN ;; esac ;;
  esac
  for pat in "$@"; do grep -qF -- "$pat" <<<"$out" || status=BROKEN; done
  printf '  %-14s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
for isa in arm64 amd64; do
  echo "== tree-shaped extraction ($isa)"
  build "$isa" 1500 "$isa"
  D="$W/$isa"
  "$J" extract "$W/bin$isa" main.Big "$D" >/dev/null 2>&1 || { echo "extract failed"; exit 1; }
  kind=words; [ "$isa" = amd64 ] && kind=bytes
  grep -q "^def seg0_${kind}_0 : List Nat" "$D/Extracted.lean" || { echo "no chunk definitions generated ($isa)"; exit 1; }
  grep -q "^def seg0_${kind} : List Nat" "$D/Extracted.lean" || { echo "no chunk root generated ($isa)"; exit 1; }
  c0="seg0_${kind}_0"
  for a in ChunkNew ChunkDup ChunkEqn ChunkLookalike Control; do sed "s/seg0_CHUNK/seg0_${kind}/g" "$R/attacks/$a.lean" > "$W/$a.$isa.lean"; done
  s=$(date +%s.%N)
  row control Verified "$(v --proof "$W/Control.$isa.lean" "$D" --theorem Proof.correctness)"
  printf '  control verify time: %.1f s\n' "$(echo "$(date +%s.%N) - $s" | bc)"
  row ChunkNew blocked "$(v --proof "$W/ChunkNew.$isa.lean" "$D" --theorem Proof.correctness)" 'shadows the Extracted namespace'
  row ChunkDup blocked "$(v --proof "$W/ChunkDup.$isa.lean" "$D" --theorem Proof.correctness)" 'already been declared'
  row ChunkEqn blocked "$(v --proof "$W/ChunkEqn.$isa.lean" "$D" --theorem Proof.correctness)"
  # compiles in Lean (Greek capital epsilon is an identifier letter), so the AUDITOR's shadow rule must be what rejects it
  out="$(v --proof "$W/ChunkLookalike.$isa.lean" "$D" --theorem Proof.correctness)"
  row ChunkLookalike blocked "$out" 'The audit rejected the proof' 'shadows the Extracted namespace'
  grep -qF 'Lean rejected the proof' <<<"$out" && { echo "  ChunkLookalike was rejected by Lean, not the auditor   <-- BROKEN"; broken+=("ChunkLookalike.reason"); }
  forge() { # NAME python-expression-on-text
    local name=$1 dir="$W/forge-$isa-$1"
    rm -rf "$dir"; cp -r "$D" "$dir"
    python3 - "$dir" "$name" "$kind" <<'PY'
import sys,re,hashlib,json
d,name,kind=sys.argv[1:4]
p=d+'/Extracted.lean'; s=open(p).read(); orig=s
leaf=re.compile(r'(def seg0_%s_(\d+) : List Nat :=\n  \[)([^\]]*)\]'%kind)
ms=list(leaf.finditer(s))
if name=='forgeByte':
    m=ms[0]; body=m.group(3); i=body.index('0x')+3
    body=body[:i]+('1' if body[i]=='0' else '0')+body[i+1:]
    s=s[:m.start(3)]+body+s[m.end(3):]
elif name=='forgeSwap':
    a,b=ms[0],ms[1]
    s=s[:a.start(3)]+b.group(3)+s[a.end(3):b.start(3)]+a.group(3)+s[b.end(3):]
elif name=='forgeName':
    s=s.replace('seg0_%s_0'%kind,'seg0_%s_zero'%kind)
assert s!=orig
open(p,'w').write(s)
ip=d+'/identity.json'; idt=open(ip).read()
idt=idt.replace(hashlib.sha256(orig.encode()).hexdigest(),hashlib.sha256(s.encode()).hexdigest())
open(ip,'w').write(idt)
PY
    local out; out="$("$J" check "$dir" 2>&1)"; local rc=$?
    local st=""; [ $rc -eq 1 ] && grep -q "differs from the regenerated extraction" <<<"$out" || st=BROKEN
    printf '  %-14s %-8s check rc=%s%s\n' "$name" "blocked" "$rc" "${st:+   <-- BROKEN}"
    [ -n "$st" ] && broken+=("$name.$isa.check")
    row "$name.verify" blocked "$(v --proof "$W/Control.$isa.lean" "$dir" --theorem Proof.correctness)"
  }
  for f in forgeByte forgeSwap forgeName; do forge $f; done
done
echo "== linear scaling (arm64 control verify time, 1500 vs 3000 lines)"
build arm64 3000 big2
"$J" extract "$W/binbig2" main.Big "$W/big2" >/dev/null 2>&1 || { echo "extract failed (big2)"; exit 1; }
s=$(date +%s.%N); row control2 Verified "$(v --proof "$W/Control.arm64.lean" "$W/big2" --theorem Proof.correctness)"
printf '  3000-line control verify time: %.1f s (words: %s)\n' "$(echo "$(date +%s.%N) - $s" | bc)" "$(grep -c '^def seg0_words_[0-9]* ' "$W/big2/Extracted.lean") leaves"
echo
if [ ${#broken[@]} -gt 0 ]; then echo "round big: BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round big: all rows as expected"

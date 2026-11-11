#!/usr/bin/env bash
# Round ALLOC (v0.3.1): the allocation contracts keep the type descriptor (and growslice's old
# elements) out of the callee's stack window, arm64 and amd64.
#   model/EtInWindow.lean must compile: for EVERY state with et inside the window the new
#     preconditions are false (*_excluded), a concrete window state met the old one (newobject_old_holds),
#     and a rodata descriptor still meets the new one (newobject_ctl).
#   M1..M10 mutation rows: dropping the conjunct from ONE precondition (Alloc.lean / AllocAmd64.lean,
#     compiled privately in front of the tree's oleans) must make EtInWindow.lean fail, with the error in
#     the theorem that pins that precondition (a flipped row, not just any failure).
# Usage: test/redteam/rounds/roundalloc/run-roundalloc.sh   (needs `lake build Janus` done)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"; cd "$root" || exit 1
LEAN="$(lake env which lean)"; LP="$root/.lake/build/lib/lean"
M=test/redteam/rounds/roundalloc/model/EtInWindow.lean
broken=()
o="$(LEAN_PATH=$LP "$LEAN" $M 2>&1)"; rc=$?
if [ $rc = 0 ] && ! grep -q sorry <<<"$o"; then echo "  model                   ok   (all *_excluded, *_old_holds, *_ctl kernel-checked)"
else echo "  model                   BROKEN: $o"; broken+=(model); fi
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-roundalloc.XXXXXX")" || exit 1; trap 'rm -rf "$T"' EXIT
# mutant NAME FILE 'old' 'new' EXPECTED-THEOREM...
mutant() {
  local name=$1 file=$2 old=$3 new=$4; shift 4
  local d="$T/$name/lib" e; mkdir -p "$d/Janus/Contracts"
  # a symlink farm over the tree's oleans, except the two modules this row mutates (Lean resolves a
  # module root directory in the FIRST search-path entry that has it, so the mutant must hold all of it)
  for e in "$LP"/Janus/*; do [ "$(basename "$e")" = Contracts ] || ln -s "$e" "$d/Janus/"; done
  for e in "$LP"/Janus/Contracts/*; do case "$(basename "$e")" in AllocAmd64.*) ;; Alloc.*) [ "$file" = Alloc ] || ln -s "$e" "$d/Janus/Contracts/";; *) ln -s "$e" "$d/Janus/Contracts/";; esac; done
  for e in "$LP"/*; do [ "$(basename "$e")" = Janus ] || ln -s "$e" "$d/"; done
  python3 -I - "$root/Janus/Contracts/$file.lean" "$d/Janus/Contracts/$file.lean" "$old" "$new" <<'P' || { echo "  $name BROKEN (pattern not found)"; broken+=("$name"); return; }
import sys
src,dst,old,new=sys.argv[1:5]
t=open(src).read()
if t.count(old)!=1: sys.exit(1)
open(dst,'w').write(t.replace(old,new))
P
  local lp="$d" out
  (cd "$d" && LEAN_PATH="$lp" "$LEAN" "Janus/Contracts/$file.lean" -o "Janus/Contracts/$file.olean" 2>"$T/$name.err") || { echo "  $name BROKEN (mutant does not compile: $(grep -m1 error "$T/$name.err"))"; broken+=("$name"); return; }
  if [ "$file" = Alloc ]; then # AllocAmd64 (original text) against the mutated Alloc
    cp "$root/Janus/Contracts/AllocAmd64.lean" "$d/Janus/Contracts/AllocAmd64.lean"
    (cd "$d" && LEAN_PATH="$lp" "$LEAN" Janus/Contracts/AllocAmd64.lean -o Janus/Contracts/AllocAmd64.olean >/dev/null 2>&1)
  fi
  out="$(cd "$root" && LEAN_PATH="$lp" "$LEAN" $M 2>&1)"; [ -z "${DEBUG:-}" ] || echo "$out" | grep -v "warning\|deprecated" | head -8
  local ok=1 th
  [ -n "$out" ] && grep -q 'error' <<<"$out" || ok=0
  for th in "$@"; do grep -qE -- "$th" <<<"$out" || ok=0; done
  if [ $ok = 1 ]; then echo "  $name flipped (EtInWindow fails at: $*)"; else echo "  $name BROKEN (EtInWindow still passes or fails elsewhere)"; broken+=("$name"); fi
}
# the failing theorem is named by its line: look up the model's line numbers by theorem name
# the error of a flipped row lies in the pinned theorem's statement or first lines: a regex over its lines
thline() { local s hi=2; s=$(grep -n "theorem $1 " $M | head -1 | cut -d: -f1); case $1 in *_old_excluded) hi=4;; esac
  echo "($(seq -s'|' $((s+1)) $((s+hi))))"; }
mutant M1_newobject Alloc ' ∧
    Outside (s.regs 0).toNat 16 (calleeStack s stack 1)' '' "EtInWindow\\.lean:$(thline newobject_excluded):"
mutant M2_newobject64 AllocAmd64 ' ∧
    Outside (s.regs 0).toNat 16 (calleeStack64 s stack 1)' '' "EtInWindow\\.lean:$(thline newobject64_excluded):"
mutant M3_makeslice Alloc ' ∧
    Outside (s.regs 0).toNat 16 (calleeStack s stack 3)

/-- `makeslice`' '

/-- `makeslice`' "EtInWindow\\.lean:$(thline makeslice_excluded):"
mutant M4_makeslice64 AllocAmd64 ' ∧
    Outside (s.regs 0).toNat 16 (calleeStack64 s stack 3)

@[reducible] def makesliceObj64' '

@[reducible] def makesliceObj64' "EtInWindow\\.lean:$(thline makeslice64_excluded):"
mutant M5_mallocgc Alloc ' ∧
      Outside (s.regs 1).toNat 16 (calleeStack s stack 3)))' '))' "EtInWindow\\.lean:$(thline mallocgc_excluded):"
mutant M6_mallocgc64 AllocAmd64 ' ∧
      Outside (s.regs 3).toNat 16 (calleeStack64 s stack 3)))' '))' "EtInWindow\\.lean:$(thline mallocgc64_excluded):"
mutant M7_growslice_et Alloc ' ∧
    Outside (s.regs 4).toNat 16 (calleeStack s stack 5)' '' "EtInWindow\\.lean:$(thline growslice_excluded):"
mutant M8_growslice64_et AllocAmd64 ' ∧
    Outside (s.regs 6).toNat 16 (calleeStack64 s stack 5)' '' "EtInWindow\\.lean:$(thline growslice64_excluded):"
mutant M9_growslice_old Alloc ' ∧
    Outside (s.regs 0).toNat (8 * ((s.regs 1).toNat - (s.regs 3).toNat)) (calleeStack s stack 5)' '' "EtInWindow\\.lean:$(thline growslice_old_excluded):"
mutant M10_growslice64_old AllocAmd64 ' ∧
    Outside (s.regs 0).toNat (8 * ((s.regs 3).toNat - (s.regs 7).toNat)) (calleeStack64 s stack 5)' '' "EtInWindow\\.lean:$(thline growslice64_old_excluded):"
[ ${#broken[@]} -gt 0 ] && { echo "round alloc: BROKEN rows: ${broken[*]}"; exit 1; }
echo "round alloc: all rows as expected"

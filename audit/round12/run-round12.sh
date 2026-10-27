#!/usr/bin/env bash
# Round-12: the ELF loader's view (docs/AUDIT-ROUND12.md, docs/SOUNDNESS.md "ELF loader semantics").
# A crafted ELF must be rejected at extraction (never Verified); the unmodified binary must still
# verify; the synthetic-ELF defence tests (dynamic relocations, DT_TEXTREL, writable code,
# RELRO, symbol ranges, init_array) must pass. Exits 1 on any BROKEN row.
# Writes only under audit/round12/work/ and a mktemp directory (removed at the end).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
R=audit/round12
J="${JANUS_AUDIT_BIN:-$root/$R/bin/janus}"
if [ -z "${JANUS_AUDIT_BIN:-}" ]; then mkdir -p "$(dirname "$J")"; go build -o "$J" ./cmd/janus || exit 1; fi
if [ "${JANUS_AUDIT_PREBUILT:-}" != 1 ]; then
  lake build Janus Janus.Tools.Audit janus-audit >/dev/null || { echo "lake build failed"; exit 1; }
  [ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
  [ -f artifacts/examples-amd64 ] || bash scripts/build-examples-amd64.sh >/dev/null 2>&1
fi
W=$R/work; rm -rf "$W"; mkdir -p "$W"
T="$(mktemp -d "${TMPDIR:-/tmp}/janus-round12.XXXXXX")" || exit 1
trap 'rm -rf "$T"' EXIT
mkdir -m 700 "$T/cache"; export JANUS_CACHE_DIR="$T/cache"
broken=()
check() { # NAME OK-EXIT MESSAGE
  if [ "$2" = 0 ]; then printf '  %-34s ok       %s\n' "$1" "$3"
  else printf '  %-34s FAILED   %s   <-- BROKEN\n' "$1" "$3"; broken+=("$1"); fi
}

# attack ISA MODE NAME PATTERN [ALIGN]: craft, confirm the run-time effect where it has one, then
# require that extraction is rejected with PATTERN and that no verification can produce Verified.
attack() {
  local isa=$1 mode=$2 name=$3 pat=$4 align=${5:-0x1000}
  local bin=artifacts/examples-$isa sym=example.com/basic.Add proof qemu orig new thm=""
  case $isa in
    arm64) proof=examples/proofs/Add.lean; qemu=qemu-aarch64; orig=0000018b; new=000001cb ;;
    amd64) proof=examples/proofs-amd64/Add/Proof.lean; qemu=qemu-x86_64; orig=4801d8; new=4829d8; thm=Proof.correctness ;;
  esac
  local addr; addr=$("$J" list "$bin" 2>/dev/null | awk -v s="$sym" '$3==s{print $1}')
  local ev="$W/$isa-$name"
  python3 -I "$R/attacks/craft_elf.py" "$mode" "$bin" "$ev" "$addr" "$orig" "$new" "$align" >"$ev.craft" 2>&1
  check "${name}_${isa}_craft" $? "$(tail -1 "$ev.craft")"
  case $mode in overlap|overlap-sub) # the overlapping mapping really executes (real-runtime oracle)
    if command -v $qemu >/dev/null; then
      o1="$($qemu "$bin" a b 2>&1)"; o2="$($qemu "$ev" a b 2>&1)"
      [ "$o1" != "$o2" ]; check "${name}_${isa}_runtime_diverges" $? "same argv, different output under $qemu: the later PT_LOAD's bytes execute"
    fi ;; esac
  local out v
  out="$("$J" extract "$ev" "$sym" "$W/$isa-$name.x" 2>&1)"; local rc=$?
  if [ $rc = 0 ]; then
    out="$out$("$J" verify --fresh --janus-root "$root" --proof "$proof" "$W/$isa-$name.x" ${thm:+--theorem "$thm"} 2>&1)"
    case $out in *Verified*) check "${name}_${isa}_blocked" 1 "FALSE VERIFY: extraction accepted the crafted binary and verify printed Verified"; return ;; esac
    check "${name}_${isa}_blocked" 1 "extraction accepted the crafted binary"; return
  fi
  grep -qF -- "$pat" <<<"$out"; check "${name}_${isa}_blocked" $? "rejected at extraction: $(grep -m1 -F -- "$pat" <<<"$out" | cut -c1-110)"
}

for isa in arm64 amd64; do
  echo "== O1 ($isa): overlapping PT_LOADs (port of round-11b O1 and variants)"
  attack $isa overlap O1_overlap_4k "overlaps an earlier PT_LOAD"
  attack $isa overlap O1b_overlap_align64k "overlaps an earlier PT_LOAD" 0x10000
  attack $isa overlap-sub O1c_overlap_16b "overlaps an earlier PT_LOAD"
  echo "== H ($isa): header consistency"
  attack $isa secoff H1_section_offset "differs from the bytes the loader maps"
  attack $isa filesz H2_filesz_gt_memsz "p_filesz > p_memsz"
  attack $isa wx H3_writable_exec "writable and executable"
  attack $isa misalign H4_misaligned "not congruent"
  echo "== C ($isa): control"
  bin=artifacts/examples-$isa
  if [ $isa = arm64 ]; then
    out="$("$J" extract "$bin" example.com/basic.Add "$W/$isa-ctl" 2>&1 && "$J" verify --fresh --janus-root "$root" --proof examples/proofs/Add.lean "$W/$isa-ctl" 2>&1)"
  else
    out="$("$J" extract "$bin" example.com/basic.Add "$W/$isa-ctl" 2>&1 && "$J" verify --fresh --janus-root "$root" --proof examples/proofs-amd64/Add/Proof.lean "$W/$isa-ctl" --theorem Proof.correctness 2>&1)"
  fi
  grep -q '^Verified' <<<"$out"; check "C1_${isa}_unmodified_verifies" $? "$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-90)"
done

echo "== D: synthetic-ELF defences (cmd/janus/elfview_test.go)"
o="$(go test -count=1 -run 'TestElf' ./cmd/janus/ 2>&1)"; check D1_elf_defence_unit_tests $? "$(tail -n 1 <<<"$o" | cut -c1-90)"

echo
if [ ${#broken[@]} -gt 0 ]; then echo "BROKEN rows: ${broken[*]}"; exit 1; fi
echo "round12: all rows as expected"

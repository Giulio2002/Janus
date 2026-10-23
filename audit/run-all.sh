#!/usr/bin/env bash
# Reproduce every attack in docs/AUDIT.md. Writes only under audit/work/.
# Usage: audit/run-all.sh            (builds audit/bin/janus from the current tree)
# Expected after the F1-F6 fixes: every "blocked" row prints "Invalid" (or "rejected"); every
# "Verified"/"Verified-honest"/"ok"/"mitigated" row prints "Verified" (or the axioms of a
# refutation). No row should print "Verified" for a false or misleading claim.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="$root/audit/bin/janus"
go build -o "$J" ./cmd/janus || exit 1
lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build Janus failed (fix the Lean library first)"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null

W=audit/work
mkdir -p $W
cp artifacts/examples-arm64 $W/examples-arm64
# Fresh extractions of the attacked functions (independent of scripts/verify-examples.sh).
for n in Add Add256 Get; do
  rm -rf "${W:?}/$n" "$W/extract-$n"
  "$J" extract $W/examples-arm64 "example.com/basic.$n" $W/extract-$n >/dev/null || { echo "extract $n failed"; exit 1; }
  mkdir -p $W/$n; cp $W/extract-$n/Extracted.lean $W/extract-$n/identity.json $W/$n/
  rm -rf $W/extract-$n
done

# row NAME EXPECT RESULT prints a row and records a regression ("BROKEN"): a "blocked" row
# must not print Verified; a Verified/Verified-honest/mitigated row must print Verified; an
# "ok" row (a refutation compiled with lake env lean) must print its axioms.
broken=()
row() {
  local status=""
  case "$2" in
    blocked) case "$3" in Verified*|accepted*) status=BROKEN ;; esac ;;
    Verified|Verified-honest|mitigated) case "$3" in Verified*) ;; *) status=BROKEN ;; esac ;;
    ok) case "$3" in *"depends on axioms"*) ;; *) status=BROKEN ;; esac ;;
  esac
  printf '%-28s %-8s %s%s\n' "$1" "$2" "$3" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$1")
  return 0
}
v() { "$J" verify --janus-root "$root" "$@" 2>&1 | head -1; }

echo "attack                       expect   result"
# F1/F2 fixes: these attacks are now rejected (Invalid) by the sandbox, the trusted janus-audit
# (no proof initializers run), the axiom audit, the Extracted-identity check or the
# trusted-only / mentions-Extracted statement rules.
for a in A1_instance A3_initialize A6_eval_io A9_namespace_shadow A5_skipkernel A7_private_shadow A10_exit; do
  row "$a" blocked "$(v --proof audit/attacks/$a.lean $W/Add)"
done
# A2/A4 still verify, but the printed statement is now honest (the proof's unexpanders are
# inactive in the clean print environment), so the attack no longer misleads. Verify prints
# "Verified"; inspect the statement with `janus explain`.
for a in A2_unexpander A4_unexpand_janus; do
  row "$a" Verified-honest "$(v --proof audit/attacks/$a.lean $W/Add)"
done
for t in t1 t3 t4; do
  row "A8_classic.$t" blocked "$(v --theorem Proof.$t --proof audit/attacks/A8_classic.lean $W/Add)"
done
# B1/B2 are blocked by fixes F3/F4: the attacks no longer verify, and their negations do.
row B1_neverpanics_fault blocked "$(v --proof audit/specs/B1_neverpanics_fault.lean $W/Add256)"
row B1_refuted Verified "$(v --proof audit/specs/B1_refuted.lean $W/Add256)"
if lake env lean audit/specs/B2_exit_sentinel.lean >/dev/null 2>&1; then b2=accepted; else b2="rejected (does not compile)"; fi
row B2_exit_sentinel blocked "$b2"
row B2_refuted ok "$(lake env lean audit/specs/B2_refuted.lean 2>&1 | head -1)"
for n in Add Add256 Get; do
  row "control:${n}_witness" Verified "$(v --proof audit/controls/${n}_witness.lean $W/$n)"
done

# C1: a planted Extracted.olean in a janus-root copy's library dir. The verifier now compiles
# Extracted into a private trusted dir placed first on LEAN_PATH, and rejects any stray
# Extracted.olean elsewhere on the path (module identity), so the shadow is caught (blocked).
C=$W/janus-root-copy
rm -rf $C; mkdir -p $C
cp -a lakefile.toml lake-manifest.json lean-toolchain Janus.lean JanusTests.lean Janus JanusTests Oracle .lake $C/
cp audit/attacks/C1_fake_Extracted.lean $C/Extracted.lean
(cd $C && lake env lean -o .lake/build/lib/lean/Extracted.olean Extracted.lean && rm Extracted.lean)
row C1_shadow_library blocked "$("$J" verify --janus-root $C --proof audit/attacks/C1_proof.lean $W/Add 2>&1 | head -1)"
rm -rf $C

# C2: the TOCTOU on a shared .janus-build no longer exists. Each verify uses a fresh private
# work dir, the sandbox runs under --die-with-parent in a new PID namespace (no lingering
# watcher survives), and every olean is hash-bound and re-checked after the audit and replay.
# The honest proof verifies; there is no window to swap a fake pair into.
row C2_toctou_swap mitigated "$(v --proof examples/proofs/Add.lean $W/Add)"
rm -f $W/A6-written-during-verify.txt

# R1: the compiled framework is pinned and read-only to untrusted builds, and the kernel replay
# covers the theorem's whole non-core import closure. Before the fix a consumer lakefile could
# rewrite the workspace's framework build: `ensures` (GoABI.olean recompiled with
# Ensures := True, "Add returns 42") and `auditor` (a forged Janus.Tools.Audit) both printed
# Verified. Each variant runs in its own package copy (Lake caches an elaborated lakefile).
# Sandboxed, the write fails (read-only framework; the false claim no longer compiles or the
# genuine auditor rejects it); unsandboxed, the framework pins reject the changed build.
R1=$W/R1
rm -rf "$R1"; mkdir -p "$R1"
nonce=$(date +%s%N)
r1pkg() { # r1pkg DIR [dep]: a copy of audit/attacks/R1_pkg requiring janus from this checkout
  local d=$1 req="" pk="" dep=${2:-}
  cp -r audit/attacks/R1_pkg "$d"
  if [ "${2:-}" = dep ]; then
    cp -r audit/attacks/R1_dep "$d-dep"
    req="require r1dep from \"$root/$d-dep\""
    pk=',{"type":"path","scope":"","name":"r1dep","manifestFile":"lake-manifest.json","inherited":false,"dir":"'"$root/$d-dep"'","configFile":"lakefile.lean"}'
  fi
  sed -i "s|@JANUS@|$root|; s|-- @EXTRA_REQUIRE@|$req|" "$d/lakefile.lean"
  # A new lakefile hash per run, so Lake elaborates (and runs) it again in a reused workspace.
  echo "-- run $nonce" >> "$d/lakefile.lean"; [ -z "$dep" ] || echo "-- run $nonce" >> "$d-dep/lakefile.lean"
  printf '{"version":"1.2.0","packagesDir":".lake/packages","name":"r1","lakeDir":".lake","fixedToolchain":false,"packages":[{"type":"path","scope":"","name":"janus","manifestFile":"lake-manifest.json","inherited":false,"dir":"%s","configFile":"lakefile.toml"}%s]}\n' "$root" "$pk" > "$d/lake-manifest.json"
}
# r1 NAME MODE PROOF THEOREM [dep] [flags…]: prints the verdict line and its stage
r1() {
  local name=$1 mode=$2 proof=$3 thm=$4; shift 4
  local dep=""; [ "${1:-}" = dep ] && { dep=dep; shift; }
  r1pkg "$R1/$name" $dep
  local out; out=$(JANUS_R1_MODE=$mode "$J" verify --janus-root "$root" $W/Add --proof "$R1/$name/R1/$proof.lean" \
    --proof-root "$R1/$name" --theorem "$thm" "$@" 2>&1)
  local what; what=$(grep -m1 -E '^  (modified|unexpected|missing) ' <<<"$out" | sed 's/^  //; s/ (pinned.*//')
  printf '%s%s [%s]' "$(grep -m1 -E '^(Verified|Invalid)' <<<"$out" | cut -c1-90)" "${what:+ … $what}" "$(grep -m1 'Stage:' <<<"$out" | sed 's/.*Stage: //')"
}
row R1a_ensures blocked "$(r1 ensures ensures Ensures R1.Ensures.claim)"
row R1a_ensures_nosandbox blocked "$(r1 ensures-ns ensures Ensures R1.Ensures.claim --unsafe-no-sandbox)"
row R1a_auditor blocked "$(r1 auditor auditor False R1.False.claim)"
row R1a_auditor_nosandbox blocked "$(r1 auditor-ns auditor False R1.False.claim --unsafe-no-sandbox)"
row R1b_corrupt blocked "$(r1 corrupt corrupt Ensures R1.Ensures.claim)"
row R1b_corrupt_nosandbox blocked "$(r1 corrupt-ns corrupt Ensures R1.Ensures.claim --unsafe-no-sandbox)"
row R1c_inject blocked "$(r1 inject inject Inject R1.Inject.claim)"
row R1c_inject_nosandbox blocked "$(r1 inject-ns inject Inject R1.Inject.claim --unsafe-no-sandbox)"
row R1c_inject_dep blocked "$(r1 inject-dep none Plain R1.Plain.claim dep --allow-path-deps)"
row R1c_inject_dep_nosandbox blocked "$(r1 inject-dep-ns none Plain R1.Plain.claim dep --allow-path-deps --unsafe-no-sandbox)"
# R1b forged lemma: a --janus-root copy whose Janus/GoABI.olean (sources untouched) carries a
# `False` lemma added with debug.skipKernelTC. The olean is well-formed and it is the build the
# pins are taken from, so only the kernel replay of the framework module catches it.
F=$W/janus-root-forged
rm -rf $F; mkdir -p $F/.lake $F/forge/Janus
cp -a lakefile.toml lake-manifest.json lean-toolchain Janus.lean JanusTests.lean Janus JanusTests Oracle $F/
cp -a .lake/build $F/.lake/
{ echo "import Lean"; cat Janus/GoABI.lean audit/attacks/R1_forged_lemma.lean; } > $F/forge/Janus/GoABI.lean
(cd $F && lake env lean --root=forge -o .lake/build/lib/lean/Janus/GoABI.olean forge/Janus/GoABI.lean >/dev/null && rm -rf forge)
row R1b_forged_lemma blocked "$("$J" verify --janus-root $F --proof audit/attacks/R1_forged_proof.lean $W/Add 2>&1 | head -1)"
rm -rf $F
# R1 proof-overwrite: a proof whose #eval corrupts the framework build on LEAN_PATH (a throwaway
# --janus-root copy). Sandboxed the write fails and the honest theorem verifies; unsandboxed
# the framework pins reject the run.
O=$W/janus-root-overwrite
for ns in "" --unsafe-no-sandbox; do
  rm -rf $O; mkdir -p $O/.lake
  cp -a lakefile.toml lake-manifest.json lean-toolchain Janus.lean JanusTests.lean Janus JanusTests Oracle $O/
  cp -a .lake/build $O/.lake/
  res="$("$J" verify --janus-root $O --proof audit/attacks/R1_proof_overwrite.lean $W/Add $ns 2>&1 | head -1)"
  if [ -z "$ns" ]; then row R1_proof_overwrite mitigated "$res"; else row R1_proof_overwrite_nosandbox blocked "$res"; fi
done
rm -rf $O

echo "model controls (audit/model/Model.lean):"
if lake env lean audit/model/Model.lean >/dev/null 2>&1; then
  echo "  Model.lean: all decide controls pass, including M1-M3 now faulting (blocked by F5)"
else
  echo "  Model.lean: FAILED   <-- BROKEN"
  broken+=(model)
fi

if [ ${#broken[@]} -gt 0 ]; then
  echo "BROKEN: ${#broken[@]} row(s) regressed: ${broken[*]}"
  exit 1
fi
echo "All rows as expected (no BROKEN row)."

#!/usr/bin/env bash
# Self-test of the layout-independent module digest (tools/oleandigest, scripts/gate/gate-cachecmp.py `hashes`/`compare`) with REAL
# Lean builds of a small module and a fake-run comparison:
#   * the same source in two directories (absolute paths) has different file bytes (the stored linter message embeds the path)
#     but the same digest (SHA-256 of the message-log-stripped re-serialization); the layout check holds;
#   * MUTATIONS each change the digest: a changed declaration (same file size), a proof term, a removed simp attribute, a changed
#     instance priority, a compiled-code-only change;
#   * compare: a path-only difference of a JanusASL/Proofs module agrees ("path-only", counted); a mutated module, the same
#     difference in an ArmASL module, in a module whose message log is empty, a trailing-garbage olean, a module in only one run,
#     a missing digest, other digest-tool binaries and non-object JSON all fail (rc 1 or 2);
#   * the digest runner fails closed on a failing tool, a truncated olean and unexpected output.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-olean-digest.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
(cd "$root/tools/oleandigest" && lake build >/dev/null 2>&1) || { echo "FAIL cannot build tools/oleandigest"; exit 1; }
LEAN="$(cd "$root" && lean --print-prefix)/bin/lean"
base() { # base MUTATION
  local m=$1
  local fbody="n + 1" proof="rfl" simp="@[simp] " prio="" irpre=""
  [ "$m" != decl ] || fbody="n + 2"
  [ "$m" != proof ] || proof="by decide"
  [ "$m" != simp ] || simp=""
  [ "$m" != inst ] || prio="(priority := 10) "
  [ "$m" != ir ] || irpre="set_option compiler.extract_closed false in"
  cat <<LEAN
def f (n : Nat) : Nat := $fbody
theorem t : f 1 = $([ "$m" = decl ] && echo 3 || echo 2) := $([ "$m" = decl ] && echo "by decide" || echo "$proof")
${simp}theorem s : f 0 = $([ "$m" = decl ] && echo 2 || echo 1) := by decide
structure Foo where x : Nat
instance ${prio}: Inhabited Foo := ⟨⟨0⟩⟩
def unusedWarn (a : Nat) (h : a = a) : Nat := 3
$irpre
def clo : List Nat := [1, 2, 3].map (· * 2)
LEAN
}
build() { # build MUTATION DIRNAME -> the olean path (built from an ABSOLUTE source path)
  local d="$t/$2"; mkdir -p "$d"; base "$1" > "$d/M.lean"
  (cd "$d" && "$LEAN" --root="$d" -o "$d/M.olean" "$d/M.lean") > "$d/build.log" 2>&1 || { echo "FAIL build $1 in $2: $(tail -3 "$d/build.log")" >&2; exit 1; }
  echo "$d/M.olean"
}
# the digest records of one olean as "<sha> <lint> <layout>" through gate-cachecmp.py's own runner
rec() { python3 -I - "$root" "$1" <<'PY'
import importlib.util, sys
root, ol = sys.argv[1:3]
spec = importlib.util.spec_from_file_location("cc", root + "/scripts/gate/gate-cachecmp.py"); cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
exe, src, binsha = cc.digest_tool()
dg, lint, lay = cc.semantic(exe, [ol])[ol]
print(dg, lint, lay)
PY
}
a=$(build none aaa); b=$(build none bbbbbbbbbbbbbbbbbbbb)
ra=$(rec "$a"); rb=$(rec "$b")
[ "$(sha256sum < "$a")" != "$(sha256sum < "$b")" ] && ok "premise: the same source at two absolute paths gives different file bytes" || bad "premise: file bytes equal (no path embedded?)"
[ "${ra%% *}" = "${rb%% *}" ] && ok "the same module at two paths has the same digest (${ra%% *})" || bad "digest depends on the path: $ra vs $rb"
case "$ra $rb" in *" ok "*" ok") ok "layout check ok for both (original size = unstripped re-serialization, header equal); message logs non-empty (${ra#* })" ;; *) bad "layout/lint: $ra | $rb" ;; esac
set -- $ra; [ "$2" -gt 0 ] && ok "the message log of the sample has entries ($2)" || bad "no message-log entries in the sample"
for m in decl proof simp inst ir; do
  x=$(build $m mut-$m); rx=$(rec "$x")
  extra=""; [ "$m" != decl ] || extra=" (file sizes $(stat -c %s "$a") vs $(stat -c %s "$x"))"
  [ "${ra%% *}" != "${rx%% *}" ] && ok "mutation '$m' changes the digest$extra" || bad "mutation '$m' NOT detected"
done
# a ONE-CHARACTER, SAME-SIZE mutation that touches one declaration only (a size or presence check could not see it)
same() { local d="$t/$1"; mkdir -p "$d"; printf 'def g : Nat := %s\ndef unusedW (a : Nat) (h : a = a) : Nat := 3\n' "$2" > "$d/M.lean"
  (cd "$d" && "$LEAN" --root="$d" -o "$d/M.olean" "$d/M.lean") > "$d/build.log" 2>&1 && echo "$d/M.olean"; }
z1=$(same z1 11); z2=$(same z2 12); r1=$(rec "$z1"); r2=$(rec "$z2")
[ "$(stat -c %s "$z1")" = "$(stat -c %s "$z2")" ] && [ "${r1%% *}" != "${r2%% *}" ] && ok "a same-size one-character change of one constant changes the digest (file size $(stat -c %s "$z1") both)" || bad "same-size mutation: sizes $(stat -c %s "$z1") $(stat -c %s "$z2"), digests ${r1%% *} ${r2%% *}"
# fake runs
mkrun() { # mkrun DIR MODULE_REL OLEAN [ALT_SEM_FROM_OLEAN] [LINT_OVERRIDE] [LAY_OVERRIDE] [nosem]
  mkdir -p "$1"; printf '{"kind":"gate","commit":"c1"}\n' > "$1/timeline.jsonl"
  python3 -I - "$root" "$1" "$2" "$3" "${4:-}" "${5:-}" "${6:-}" "${7:-}" <<'PY'
import importlib.util, json, sys
root, out, rel, ol, alt, lint, lay, nosem = sys.argv[1:9]
spec = importlib.util.spec_from_file_location("cc", root + "/scripts/gate/gate-cachecmp.py"); cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
exe, src, binsha = cc.digest_tool()
h = {"olean:" + rel: cc.sha_file(ol), "config:SAIL_SPLIT": "1", "config:SAIL_SPLIT_PARTS": "48", "sail-driver": "d",
     "config:oleandigest-src": src, "config:oleandigest-bin": binsha, "ir:janus/Fake.c": "c0ffee"}  # compare needs some emitted-C record in both runs
if not nosem:
    dg, nl, la = cc.semantic(exe, [alt or ol])[alt or ol]
    h["sem:" + rel], h["lint:" + rel], h["lay:" + rel] = dg, lint or str(nl), lay or la
json.dump(h, open(out + "/artifact-hashes.json", "w"))
PY
}
cmpc() { python3 -I "$root/scripts/gate/gate-cachecmp.py" compare "$1" "$2" 2>&1; }
want() { # want DESC RC GREP DIR1 DIR2
  local out rc; out=$(cmpc "$4" "$5"); rc=$?
  if [ "$rc" = "$2" ] && { [ -z "$3" ] || grep -q -- "$3" <<<"$out"; }; then ok "$1 (rc $rc)"; else bad "$1: rc $rc (wanted $2): $out"; fi
}
P=JanusASL/Proofs/M.olean
mkrun "$t/c1" $P "$a"; mkrun "$t/c2" $P "$b"
want "compare: a path-only difference of a JanusASL/Proofs module agrees and is counted" 0 "1 module file hashes differ ONLY" "$t/c1" "$t/c2"
mkrun "$t/c3" $P "$(build decl mut-decl2)"
want "compare: a changed declaration is P0" 1 "SEMANTIC digests differ" "$t/c1" "$t/c3"
mkrun "$t/c4" $P "$(build ir mut-ir2)"
want "compare: an IR / compiled-code change is P0" 1 "SEMANTIC digests differ" "$t/c1" "$t/c4"
# the same byte difference in a module that is NOT under models/asl/JanusASL/Proofs/ must be byte-identical
mkrun "$t/d1" ArmASL/M.olean "$a"; mkrun "$t/d2" ArmASL/M.olean "$b"
want "compare: differing bytes in an ArmASL module are P0 even with equal digests" 1 "ArmASL/M.olean" "$t/d1" "$t/d2"
mkrun "$t/d3" Janus/M.olean "$a"; mkrun "$t/d4" Janus/M.olean "$b"
want "compare: differing bytes in a Janus module are P0" 1 "Janus/M.olean" "$t/d3" "$t/d4"
# a Proofs module whose cold message log is empty cannot differ because of it
mkrun "$t/e2" $P "$b" "" 0
want "compare: differing bytes with an EMPTY message log (cold) are P0" 1 "message log is empty" "$t/c1" "$t/e2"
# trailing garbage after the compacted region
cp "$b" "$t/garbage.olean"; head -c 4096 /dev/urandom >> "$t/garbage.olean"
mkrun "$t/g2" $P "$t/garbage.olean"
want "compare: an olean with trailing garbage is not path-only (layout check)" 1 "bytes the module data does not account for" "$t/c1" "$t/g2"
# header tamper (the Lean version / git hash area)
cp "$b" "$t/hdr.olean"; printf 'X' | dd of="$t/hdr.olean" bs=1 seek=50 conv=notrunc 2>/dev/null
(cd "$t" && python3 -I - "$root" "$t/hdr.olean" <<'PY'
import importlib.util, sys
root, ol = sys.argv[1:3]
spec = importlib.util.spec_from_file_location("cc", root + "/scripts/gate/gate-cachecmp.py"); cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
exe, _, _ = cc.digest_tool()
try:
    r = cc.semantic(exe, [ol])[ol]
    print("HDR", r[2])
except RuntimeError as e:
    print("HDR error", str(e)[:80])
PY
) > "$t/hdr.out" 2>&1
grep -q "HDR bad\|HDR error" "$t/hdr.out" && ok "a tampered olean header is not layout-ok (or not loadable): $(cat "$t/hdr.out" | cut -c1-70)" || bad "header tamper accepted: $(cat "$t/hdr.out")"
# one-sided module, missing digest, tool provenance, non-object JSON
cp -r "$t/c2" "$t/f2"; python3 -I - "$t/f2/artifact-hashes.json" <<'PY'
import json, sys
h = json.load(open(sys.argv[1])); h["olean:JanusASL/Proofs/Extra.olean"] = "x"; json.dump(h, open(sys.argv[1], "w"))
PY
want "compare: a module present in only one run is P0" 1 "Extra.olean" "$t/c1" "$t/f2"
mkrun "$t/h2" $P "$b" "" "" "" nosem
want "compare: differing file hashes without a semantic digest fail closed" 1 "fail closed" "$t/c1" "$t/h2"
cp -r "$t/c2" "$t/i2"; python3 -I - "$t/i2/artifact-hashes.json" <<'PY'
import json, sys
h = json.load(open(sys.argv[1])); h["config:oleandigest-bin"] = "0" * 64; json.dump(h, open(sys.argv[1], "w"))
PY
want "compare: a different digest executable is a configuration mismatch (never a pass)" 2 "oleandigest-bin" "$t/c1" "$t/i2"
cp -r "$t/c2" "$t/j2"; echo '[]' > "$t/j2/artifact-hashes.json"
want "compare: artifact-hashes.json that is not an object cannot be compared" 2 "" "$t/c1" "$t/j2"
echo 'null' > "$t/j2/artifact-hashes.json"
want "compare: artifact-hashes.json null cannot be compared" 2 "" "$t/c1" "$t/j2"
# the runner fails closed
python3 -I - "$root" "$a" "$t" <<'PY' && ok "semantic() fails closed on a failing tool, a truncated olean, unexpected and duplicate output" || bad "semantic() accepted bad output"
import importlib.util, os, stat, sys
root, ol, t = sys.argv[1:4]
spec = importlib.util.spec_from_file_location("cc", root + "/scripts/gate/gate-cachecmp.py"); cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
exe, _, _ = cc.digest_tool()
def raises(f):
    try:
        f(); return False
    except RuntimeError:
        return True
trunc = os.path.join(t, "trunc.olean"); open(trunc, "wb").write(open(ol, "rb").read()[:3000])
assert raises(lambda: cc.semantic(exe, [trunc])), "truncated olean accepted"
assert raises(lambda: cc.semantic(exe, [ol, os.path.join(t, "missing.olean")])), "missing file accepted"
def fake(name, body):
    p = os.path.join(t, "fake-" + name); open(p, "w").write("#!/bin/sh\n" + body + "\n"); os.chmod(p, 0o755); return p
assert raises(lambda: cc.semantic(fake("f1", "exit 1"), [ol])), "failing tool accepted"
assert raises(lambda: cc.semantic(fake("f2", "echo garbage"), [ol])), "garbage line accepted"
assert raises(lambda: cc.semantic(fake("f3", "exit 0"), [ol])), "no output accepted"
assert raises(lambda: cc.semantic(fake("f4", 'printf "0\\t%s\\t1\\t1\\t1\\t1\\n0\\t%s\\t1\\t1\\t1\\t1\\n" "$2" "$2"'), [ol])), "duplicate line accepted"
assert raises(lambda: cc.semantic(fake("f5", 'printf "0\\t/other\\t1\\t1\\t1\\t1\\n"'), [ol])), "wrong module accepted"
PY
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail

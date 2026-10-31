#!/usr/bin/env bash
# Self-test of the layout-independent module digest (tools/oleandigest, scripts/gate-cachecmp.py `hashes`/`compare`) with REAL
# Lean builds of a small module:
#   * the same source built in two directories of different path length has different file bytes (the stored linter message
#     embeds the source path) but the same semantic digest; only the message-log piece differs;
#   * MUTATIONS each change the semantic digest: a changed declaration, a changed proof term, a removed simp attribute, a
#     changed instance priority, a compiled-code (IR) only change;
#   * compare treats the path-only difference as agreement ("path-only", counted) and a mutated module as P0.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
t=$(mktemp -d "${TMPDIR:-/tmp}/test-olean-digest.XXXXXX"); trap 'rm -rf "$t"' EXIT
fail=0; ok() { echo "ok   $*"; }; bad() { echo "FAIL $*"; fail=1; }
(cd "$root/tools/oleandigest" && lake build >/dev/null 2>&1) || { echo "FAIL cannot build tools/oleandigest"; exit 1; }
D="$root/tools/oleandigest/.lake/build/bin/janus-olean-digest"
LEAN="$(cd "$root" && lean --print-prefix)/bin/lean"
base() { # base MUTATION: the module source
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
build() { # build MUTATION DIRNAME -> the olean path
  local d="$t/$2"; mkdir -p "$d"; base "$1" > "$d/M.lean"
  (cd "$d" && "$LEAN" --root="$d" -o "$d/M.olean" "$d/M.lean") > "$d/build.log" 2>&1 || { echo "FAIL build $1 in $2: $(tail -3 "$d/build.log")"; exit 1; }
  echo "$d/M.olean"
}
pieces() { "$D" "$1" | awk '{print $2" "$3}'; }
agg() { pieces "$1" | grep -v '^ext:Lean.Linter.lintLogExt ' | sha256sum | cut -c1-16; }
a=$(build none aaa); b=$(build none bbbbbbbbbbbbbbbbbbbb)
[ "$(sha256sum < "$a")" != "$(sha256sum < "$b")" ] && ok "premise: the same source in two directories gives different file bytes" || bad "premise: file bytes equal (no path embedded?)"
[ "$(agg "$a")" = "$(agg "$b")" ] && ok "the same module at two paths has the same semantic digest" || bad "semantic digest depends on the path"
dl=$(diff <(pieces "$a") <(pieces "$b") | grep '^<' | awk '{print $2}' | tr '\n' ' ')
[ "$dl" = "ext:Lean.Linter.lintLogExt " ] && ok "only the message log piece differs between the two paths" || bad "pieces differing across paths: $dl"
for m in decl proof simp inst ir; do
  x=$(build $m mut-$m)
  [ "$(agg "$a")" != "$(agg "$x")" ] && ok "mutation '$m' changes the semantic digest ($(diff <(pieces "$a") <(pieces "$x") | grep '^<' | awk '{print $2}' | grep -v lintLog | tr '\n' ' '))" || bad "mutation '$m' NOT detected"
done
# compare: path-only agrees, a mutation is P0, a module in one run only is P0, a missing digest fails closed
mkrun() { # mkrun DIR OLEAN [SEM|nosem]
  mkdir -p "$1"; printf '{"kind":"gate","commit":"c1"}\n' > "$1/timeline.jsonl"
  python3 -I - "$1" "$2" "${3:-sem}" "$root" <<'PY'
import hashlib, importlib.util, json, sys
out, ol, mode, root = sys.argv[1:5]
spec = importlib.util.spec_from_file_location("cc", root + "/scripts/gate-cachecmp.py"); cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
h = {"olean:M.olean": cc.sha_file(ol), "config:SAIL_SPLIT": "1", "config:SAIL_SPLIT_PARTS": "48", "sail-driver": "d"}
if mode == "sem":
    h["sem:M.olean"] = cc.semantic(root + "/tools/oleandigest/.lake/build/bin/janus-olean-digest", [ol])[ol]
json.dump(h, open(out + "/artifact-hashes.json", "w"))
PY
}
cmpc() { python3 -I "$root/scripts/gate-cachecmp.py" compare "$1" "$2" 2>&1; }
mkrun "$t/r1" "$a"; mkrun "$t/r2" "$b"
out=$(cmpc "$t/r1" "$t/r2"); rc=$?
[ "$rc" = 0 ] && grep -q "1 module file hashes differ ONLY" <<<"$out" && ok "compare: a path-only difference agrees and is reported (rc 0)" || bad "path-only: rc $rc: $out"
mkrun "$t/r3" "$(build decl mut-decl2)"
out=$(cmpc "$t/r1" "$t/r3"); rc=$?
[ "$rc" = 1 ] && grep -q "P0 CACHE BUG" <<<"$out" && ok "compare: a changed declaration is P0 (rc 1)" || bad "mutation: rc $rc: $out"
mkrun "$t/r4" "$(build ir mut-ir2)"
out=$(cmpc "$t/r1" "$t/r4"); rc=$?
[ "$rc" = 1 ] && ok "compare: an IR-only change is P0 (rc 1)" || bad "IR mutation: rc $rc: $out"
cp "$t/r2/artifact-hashes.json" "$t/r5.json"; mkdir -p "$t/r5"; cp "$t/r2/timeline.jsonl" "$t/r5/"
python3 -I - "$t/r5.json" "$t/r5/artifact-hashes.json" <<'PY'
import json, sys
h = json.load(open(sys.argv[1])); h["olean:Extra.olean"] = "x"; h["sem:Extra.olean"] = "y"; json.dump(h, open(sys.argv[2], "w"))
PY
out=$(cmpc "$t/r1" "$t/r5"); rc=$?
[ "$rc" = 1 ] && ok "compare: a module present in only one run is P0 (rc 1)" || bad "one-sided module: rc $rc: $out"
mkrun "$t/r6" "$b" nosem
out=$(cmpc "$t/r1" "$t/r6"); rc=$?
[ "$rc" = 1 ] && grep -q "fail closed" <<<"$out" && ok "compare: differing file hashes without a semantic digest fail closed" || bad "missing sem: rc $rc: $out"
[ "$fail" = 0 ] && echo "all checks passed"
exit $fail

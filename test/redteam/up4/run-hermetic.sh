#!/usr/bin/env bash
# UP4 regression rows (docs: NOTES-UP4.md): proof elaboration is hermetic.
#   S1  the n11 sandbox probe cannot read the cache dir / HMAC key            -> Verified
#   U1  cannot see $HOME, ~/.cache siblings, /srv, /etc secrets, env secrets   -> Verified
#   U2  behaves identically with and without a host file present               -> Verified, same output
#   legit Add proof still verifies.
# Usage: test/redteam/up4/run-hermetic.sh [JANUS_BIN]    (modes: bwrap and, with UP4_UNSHARE=1, the unshare fallback)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"; cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="${1:-$root/janus-up4}"
CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1   # always built from the current tree
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=test/redteam/up4/work; rm -rf "$W"; mkdir -p "$W"
# U1/U2 are templates: they name this checkout (__ROOT__, __ROOT_NAME__), generated here so the probes follow the repo they run from
rootname="$(basename "$root")"
for p in U1_hermetic_probe U2_hostfile_probe; do sed -e "s#__ROOT__#$root#g" -e "s#__ROOT_NAME__#$rootname#g" test/redteam/up4/$p.lean > "$W/$p.lean"; done
# the U1 probe expects the cache under /srv/janus-ops/work.up4* (the only visible /srv/janus-ops entry)
if [ -z "${JANUS_CACHE_DIR:-}" ]; then ucache="$(mktemp -d /srv/janus-ops/work.up4.XXXXXX)"; trap 'rm -rf "$ucache"' EXIT; export JANUS_CACHE_DIR="$ucache/cache"; mkdir -m 700 "$JANUS_CACHE_DIR"; fi
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
broken=0
v() { "$J" verify --no-result-cache --janus-root "$root" "$W/Add" --proof "$1" --theorem Proof.correctness --theorem Proof.Witness.nonvacuous 2>&1; }
row() { local n=$1 out=$2; if grep -q '^Verified' <<<"$out" && ! grep -q 'ESCAPE' <<<"$out"; then echo "  ok: $n"; else echo "  BROKEN: $n"; echo "$out" | head -20; broken=1; fi; }
row legit_Add "$(v examples/proofs/Add.lean)"
row S1 "$(v test/redteam/up4/S1_sandbox_probe.lean)"
row U1 "$(v $W/U1_hermetic_probe.lean)"
# S4 (n11 host-state probe): reports what elaboration sees as an error. Required: scrubbed env, no /root /srv /etc secrets,
# private /proc. ACCEPTED nondeterminism (cannot be removed, does not affect soundness: the kernel check decides): the clock,
# random bytes, uid, and the host-wide /proc/{cpuinfo,meminfo,loadavg} contents.
s4="$(v test/redteam/up4/S4_hoststate_probe.lean)"; echo "$s4" > "$W/s4.out"
s4ok=1
grep -q 'env HOME=/tmp' <<<"$s4" || s4ok=0
grep -q 'env JANUS_CACHE_DIR=<unset>' <<<"$s4" || s4ok=0
grep -q 'env SSH_AUTH_SOCK=<unset>' <<<"$s4" || s4ok=0
grep -q 'env PATH=[^ ]*\.cargo' <<<"$s4" && s4ok=0
grep -q 'env PATH=[^ ]*\.bun' <<<"$s4" && s4ok=0
grep -q 'file /root/.ssh: no' <<<"$s4" || s4ok=0
grep -q 'file /root/.claude: no' <<<"$s4" || s4ok=0
# /srv/janus-ops is only the empty mount-point ancestor of the cache work dir (dir:1), never its contents
grep -qE 'file /srv/janus-ops: no( dir:1)?(,|$)' <<<"$s4" || s4ok=0
# private pid ns: pid 1 is the sandbox's own init (bwrap/unshare), not the host's init; /proc/self/environ is the scrubbed env
grep -q 'file /proc/1/cmdline: ' <<<"$s4" || s4ok=0
host1=$(wc -c < /proc/1/cmdline); grep -q "file /proc/1/cmdline: ${host1}B" <<<"$s4" && s4ok=0
grep -q 'file /etc/hostname: no' <<<"$s4" || s4ok=0
[ $s4ok = 1 ] && echo "  ok: S4 host-state probe (output in $W/s4.out)" || { echo "  BROKEN: S4"; echo "$s4" | head -12 | cut -c1-1500; broken=1; }
rm -f test/redteam/up4/HOSTFILE-PRESENT
a="$(v $W/U2_hostfile_probe.lean)"; row U2_absent "$a"
touch test/redteam/up4/HOSTFILE-PRESENT
# the file must really exist on the host during the present run, and the probe (which throws if it sees it) must report it invisible
[ -e "$root/test/redteam/up4/HOSTFILE-PRESENT" ] || { echo "  BROKEN: U2 host file was not created"; broken=1; }
b="$(v $W/U2_hostfile_probe.lean)"; row U2_present "$b"
[ -e "$root/test/redteam/up4/HOSTFILE-PRESENT" ] && echo "  ok: U2 host file existed on the host during the run" || { echo "  BROKEN: U2 host file vanished during the run"; broken=1; }
# the probe throws HERMETIC ESCAPE if it can see the file, so Verified with the file present on the host = invisible inside
grep -q '^Verified' <<<"$b" && ! grep -q 'HERMETIC ESCAPE' <<<"$b" && echo "  ok: U2 file invisible inside the sandbox" || { echo "  BROKEN: U2 present run does not report the file invisible"; broken=1; }
rm -f test/redteam/up4/HOSTFILE-PRESENT
norm() { grep -v -e 'Report:' -e '^real' <<<"$1"; }
[ "$(norm "$a")" = "$(norm "$b")" ] && echo "  ok: U2 output identical" || { echo "  BROKEN: U2 outputs differ"; diff <(norm "$a") <(norm "$b") | head; broken=1; }
exit $broken

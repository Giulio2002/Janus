#!/usr/bin/env bash
# UP4 regression rows (docs: NOTES-UP4.md): proof elaboration is hermetic.
#   S1  the n11 sandbox probe cannot read the cache dir / HMAC key            -> Verified
#   U1  cannot see $HOME, ~/.cache siblings, /srv, /etc secrets, env secrets   -> Verified
#   U2  behaves identically with and without a host file present               -> Verified, same output
#   legit Add proof still verifies.
# Usage: audit/up4/run-hermetic.sh [JANUS_BIN]    (modes: bwrap and, with UP4_UNSHARE=1, the unshare fallback)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"; cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
J="${1:-$root/janus-up4}"; [ -x "$J" ] || CGO_ENABLED=0 go build -o "$J" ./cmd/janus || exit 1
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/up4/work; rm -rf "$W"; mkdir -p "$W"
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
broken=0
v() { "$J" verify --no-result-cache --janus-root "$root" "$W/Add" --proof "$1" 2>&1; }
row() { local n=$1 out=$2; if grep -q '^Verified' <<<"$out" && ! grep -q 'ESCAPE' <<<"$out"; then echo "  ok: $n"; else echo "  BROKEN: $n"; echo "$out" | head -20; broken=1; fi; }
row legit_Add "$(v examples/proofs/Add.lean)"
row S1 "$(v audit/up4/S1_sandbox_probe.lean)"
row U1 "$(v audit/up4/U1_hermetic_probe.lean)"
# S4 (n11 host-state probe): reports what elaboration sees as an error. Required: scrubbed env, no /root /srv /etc secrets,
# private /proc. ACCEPTED nondeterminism (cannot be removed, does not affect soundness: the kernel check decides): the clock,
# random bytes, uid, and the host-wide /proc/{cpuinfo,meminfo,loadavg} contents.
s4="$(v audit/up4/S4_hoststate_probe.lean)"; echo "$s4" > "$W/s4.out"
s4ok=1
grep -q 'env HOME=/tmp' <<<"$s4" || s4ok=0
grep -q 'env JANUS_CACHE_DIR=<unset>' <<<"$s4" || s4ok=0
grep -q 'env SSH_AUTH_SOCK=<unset>' <<<"$s4" || s4ok=0
grep -q 'env PATH=[^ ]*\.cargo' <<<"$s4" && s4ok=0
grep -q 'env PATH=[^ ]*\.bun' <<<"$s4" && s4ok=0
for f in /etc/hostname /root/.ssh /root/.claude /srv/janus-ops /proc/1/cmdline /proc/self/environ; do
  grep -q "file $f: no" <<<"$s4" || { grep -q "file $f: [0-9]*B" <<<"$s4" && s4ok=0; }
done
grep -q 'file /root/.ssh: no' <<<"$s4" || s4ok=0
grep -q 'file /root/.claude: no' <<<"$s4" || s4ok=0
grep -q 'file /srv/janus-ops: no' <<<"$s4" || s4ok=0
grep -q 'file /etc/hostname: no' <<<"$s4" || s4ok=0
[ $s4ok = 1 ] && echo "  ok: S4 host-state probe (output in $W/s4.out)" || { echo "  BROKEN: S4"; echo "$s4" | head -12 | cut -c1-1500; broken=1; }
rm -f audit/up4/HOSTFILE-PRESENT
a="$(v audit/up4/U2_hostfile_probe.lean)"; row U2_absent "$a"
touch audit/up4/HOSTFILE-PRESENT
b="$(v audit/up4/U2_hostfile_probe.lean)"; row U2_present "$b"
rm -f audit/up4/HOSTFILE-PRESENT
norm() { grep -v -e 'Report:' -e '^real' <<<"$1"; }
[ "$(norm "$a")" = "$(norm "$b")" ] && echo "  ok: U2 output identical" || { echo "  BROKEN: U2 outputs differ"; diff <(norm "$a") <(norm "$b") | head; broken=1; }
exit $broken

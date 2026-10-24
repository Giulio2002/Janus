package main

import (
	"bufio"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Regression tests for the round-2 audit (docs/AUDIT-ROUND2.md): CRITICAL-1 (an inline
// instance in the statement made the printed theorem lie) and U1 (the unshare fallback left
// non-root mounts writable).

// TestInlineInstanceRejected: every S1 variant (HSub, HMul, OfNat, Decidable in an `if`, LT,
// an inline NatCast coercion, an inline Coe, a literal behind a beta-redex) compiles against
// the real Add proof but is rejected at the statement-identity stage; the honest Add proof
// verifies, and its report carries the pp.explicit statement.
func TestInlineInstanceRejected(t *testing.T) {
	t.Parallel()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	for _, a := range []string{"S1_inline_instance", "S1c_mul", "S1d_ofnat", "S1e_decidable_if", "S1f_lt",
		"S1g_coe", "S1h_coe_inline", "S1i_beta"} {
		p := filepath.Join(repoRoot, "audit", "round2", "attacks", a+".lean")
		code, _, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot)
		if code != 1 || !strings.Contains(stderr, "inline instance") || !strings.Contains(stderr, "Stage: statement identity") {
			t.Errorf("%s not rejected as an inline instance: %d %s", a, code, stderr)
		}
	}
	code, _, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(repoRoot, "examples", "proofs", "Add.lean"),
		"--janus-root", repoRoot)
	if code != 0 {
		t.Fatalf("honest Add: %s", stderr)
	}
	r := readReport(t, add)
	if !strings.Contains(r.StatementExplicit, "@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)") {
		t.Errorf("statementExplicit does not show the instances: %q", r.StatementExplicit)
	}
}

// TestRoundTripRejectsAmbiguousPrint: a statement whose printed form does not determine it
// (`[] = []` at an element type the printer hides, an implicit argument rather than an
// instance) passes the instance-argument check but is rejected by the round-trip.
func TestRoundTripRejectsAmbiguousPrint(t *testing.T) {
	t.Parallel()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	proof := writeProof(t, `import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ @Eq (List Bool) [] []) := by
  intro ret hret s hs hp
  obtain ⟨f, s', h1, h2, h3⟩ := honest x y ret hret s hs hp
  exact ⟨f, s', h1, h2, h3, rfl⟩
end Proof
`)
	code, _, stderr := runJanus(t, "verify", add, "--proof", proof, "--janus-root", repoRoot)
	if code != 1 || !strings.Contains(stderr, "does not round-trip") || !strings.Contains(stderr, "Stage: statement identity") {
		t.Fatalf("ambiguous print not rejected by the round-trip: %d %s", code, stderr)
	}
}

// writableMounts lists the host's read-write mounts of ordinary filesystems whose mount point
// is a directory we can write on the host (candidates for a sandbox escape), excluding /tmp
// and /dev/shm (checked separately), pseudo filesystems and container root filesystems.
func writableMounts(t *testing.T) []string {
	t.Helper()
	f, err := os.Open("/proc/self/mountinfo")
	if err != nil {
		t.Skip("no /proc/self/mountinfo")
	}
	defer f.Close()
	real := map[string]bool{"ext2": true, "ext3": true, "ext4": true, "xfs": true, "btrfs": true, "vfat": true,
		"tmpfs": true, "f2fs": true, "zfs": true, "overlay": true}
	var out []string
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		fields := strings.Fields(sc.Text())
		sep := -1
		for i, x := range fields {
			if x == "-" {
				sep = i
				break
			}
		}
		if sep < 0 || sep+1 >= len(fields) || len(fields) < 6 {
			continue
		}
		mp, opts, fstype := fields[4], fields[5], fields[sep+1]
		if !real[fstype] || !strings.HasPrefix(opts, "rw") || strings.Contains(mp, `\`) {
			continue
		}
		if mp == "/tmp" || mp == "/dev/shm" || strings.HasPrefix(mp, "/proc") || strings.HasPrefix(mp, "/sys") ||
			strings.HasPrefix(mp, "/var/lib/docker") || strings.HasPrefix(mp, "/snap") {
			continue
		}
		if st, err := os.Stat(mp); err != nil || !st.IsDir() {
			continue
		}
		probe := filepath.Join(mp, ".janus-u1-probe-"+newNonce())
		if err := os.WriteFile(probe, nil, 0o600); err != nil {
			continue
		}
		_ = os.Remove(probe)
		out = append(out, mp)
	}
	return out
}

// TestUnshareFallbackConfinement (U1): under the unshare fallback, /tmp and /dev/shm are
// private tmpfs mounts and every other mount is read-only; only the work dir is writable.
func TestUnshareFallbackConfinement(t *testing.T) {
	useTestCache(t)
	if _, err := exec.LookPath("unshare"); err != nil {
		t.Skip("unshare not installed")
	}
	sb := &sandbox{mode: "unshare"}
	if err := sb.selfTest(); err != nil {
		t.Skipf("unshare fallback unavailable here: %v", err)
	}
	base, _ := janusRunBase()
	ws, err := os.MkdirTemp(base, "u1-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(ws)
	name := ".janus-u1-" + newNonce()
	targets := append([]string{"/tmp", "/dev/shm"}, writableMounts(t)...)
	t.Logf("probing %v", targets)
	script := "echo ok > own.txt && echo OWN; "
	for _, d := range targets {
		script += "(echo x > " + shQuote(filepath.Join(d, name)) + ") 2>/dev/null && echo WROTE:" + shQuote(d) + "; "
	}
	script += "true"
	out, err := sb.command(ws, nil, []string{"/bin/sh", "-c", script}, os.Environ()).CombinedOutput()
	if err != nil {
		t.Fatalf("sandbox: %v %s", err, out)
	}
	if !strings.Contains(string(out), "OWN") {
		t.Errorf("the work dir is not writable: %s", out)
	}
	for _, d := range targets {
		p := filepath.Join(d, name)
		if _, err := os.Lstat(p); err == nil {
			_ = os.Remove(p)
			t.Errorf("a write to %s inside the unshare sandbox reached the host", d)
		}
		inside := strings.Contains(string(out), "WROTE:"+d+"\n") || strings.HasSuffix(string(out), "WROTE:"+d)
		// /tmp, /dev/shm and (round 3, S2) /run are private tmpfs mounts: writable inside but
		// isolated from the host, which the host-leak check above already confirmed.
		isPrivate := d == "/tmp" || d == "/dev/shm" || d == "/run" || strings.HasPrefix(d, "/run/")
		if inside && !isPrivate {
			t.Errorf("%s is writable inside the unshare sandbox", d)
		}
	}
	// /tmp and /dev/shm are private but usable.
	if !strings.Contains(string(out), "WROTE:/tmp") {
		t.Errorf("the private /tmp is not writable: %s", out)
	}
}

// TestUnshareFallbackVerifies: forcing the fallback (JANUS_SANDBOX=unshare) with the cache
// under /tmp — the setup that used to leave the cache writable — the honest Add proof
// verifies and the report records the unshare sandbox.
func TestUnshareFallbackVerifies(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	t.Setenv("JANUS_SANDBOX", "unshare")
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("unshare fallback unavailable: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	code, _, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(repoRoot, "examples", "proofs", "Add.lean"),
		"--janus-root", repoRoot)
	if code != 0 {
		t.Fatalf("verify under the unshare fallback: %s", stderr)
	}
	if r := readReport(t, add); r.Sandbox.Mode != "unshare" {
		t.Errorf("sandbox mode %q, want unshare", r.Sandbox.Mode)
	}
	t.Setenv("JANUS_SANDBOX", "nonsense")
	if _, err := detectSandbox(false); err == nil {
		t.Error("an unknown JANUS_SANDBOX was accepted")
	}
}

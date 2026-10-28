package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

func TestParseMemSize(t *testing.T) {
	for in, want := range map[string]int64{
		"16G": 16 << 30, "16g": 16 << 30, "1500M": 1500 << 20, "1.5GiB": 3 << 29, "2T": 2 << 40,
		"1073741824": 1 << 30, "512MB": 512 << 20, "65536K": 64 << 20,
	} {
		if got, err := parseMemSize(in); err != nil || got != want {
			t.Errorf("parseMemSize(%q) = %d, %v; want %d", in, got, err, want)
		}
	}
	for _, in := range []string{"", "G", "abc", "-1G", "1M", "0"} {
		if _, err := parseMemSize(in); err == nil {
			t.Errorf("parseMemSize(%q) accepted", in)
		}
	}
}

func TestDefaultMemLimit(t *testing.T) {
	lim := defaultMemLimit()
	if lim <= 0 || lim > 24<<30 {
		t.Fatalf("default limit %d", lim)
	}
	if tot := memInfo("MemTotal"); tot > 0 && lim > tot*2/5+1 {
		t.Fatalf("default limit %d above 40%% of MemTotal %d", lim, tot)
	}
}

func TestJobLabel(t *testing.T) {
	c := exec.Command("/usr/bin/bwrap", "--unshare-all", "--ro-bind", "/", "/", "--chdir", "/w", "--", "/opt/lean/bin/lean", "--root=/w", "/w/Proof.lean", "-o", "/w/Proof.olean")
	if got := jobLabel(c); got != "lean Proof.lean Proof.olean" {
		t.Errorf("bwrap label %q", got)
	}
	if got := jobLabel(exec.Command("/x/lake", "build", "Janus")); got != "lake build Janus" {
		t.Errorf("lake label %q", got)
	}
}

func TestMemLimitDiag(t *testing.T) {
	g := &memGuard{mech: "systemd-user", limit: 1 << 30}
	d := memLimitDiag(g, memEvent{Label: "lean Proof.lean", Peak: 1 << 30}, &diag{Stage: "proof checking", Msg: "Lean rejected the proof"})
	var b bytes.Buffer
	printDiag(&b, d)
	s := b.String()
	for _, want := range []string{"Invalid: lean Proof.lean exceeded the memory limit", "limit 1.0 GiB", "peak 1.0 GiB",
		"Stage: resource limit", "JANUS_MEM_MAX", "interrupted the stage: proof checking"} {
		if !strings.Contains(s, want) {
			t.Errorf("diagnostic lacks %q:\n%s", want, s)
		}
	}
}

// guardedMech reports the guard detected for the janus processes of the tests (the default
// configuration), skipping when there is no cgroup mechanism: then a memory-hungry job would
// not be stopped by a cgroup, and the test must not put the host at risk.
func guardedMech(t *testing.T, bin string, env []string) string {
	t.Helper()
	cmd := exec.Command(bin, "memguard")
	cmd.Env = env
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("janus memguard: %v\n%s", err, out)
	}
	s := string(out)
	t.Logf("%s", strings.TrimSpace(s))
	for _, m := range []string{"cgroup", "systemd-user", "systemd-system"} {
		if strings.HasPrefix(s, "memory guard: "+m+",") {
			return m
		}
	}
	t.Skipf("no cgroup memory guard on this host (%s); not running a memory-hungry job", strings.TrimSpace(s))
	return ""
}

func envWith(kv ...string) []string {
	env := []string{}
	drop := map[string]bool{}
	for _, e := range kv {
		k, _, _ := strings.Cut(e, "=")
		drop[k] = true
	}
	for _, e := range os.Environ() {
		k, _, _ := strings.Cut(e, "=")
		if !drop[k] {
			env = append(env, e)
		}
	}
	return append(env, kv...)
}

// hungryProof elaborates a list of 10^8 naturals (several GB of cons cells) before stating the
// theorem: under JANUS_MEM_MAX=1G its Lean process must be killed by the guard, and janus must
// say so, not report a proof error.
const hungryProof = "import Extracted\nnamespace Proof\n" +
	"#eval (List.replicate 100000000 (7 : Nat)).foldl (· + ·) 0\n" +
	"theorem correctness : Extracted.entry = Extracted.entry := rfl\nend Proof\n"

func checkResourceLimit(t *testing.T, out string, report string) {
	t.Helper()
	for _, want := range []string{"Invalid: ", "Stage: resource limit", "exceeded the memory limit", "limit 1.0 GiB", "measured peak "} {
		if !strings.Contains(out, want) {
			t.Errorf("output lacks %q:\n%s", want, out)
		}
	}
	for _, bad := range []string{"Stage: proof checking", "Lean rejected", "Stage: theorem audit"} {
		if strings.Contains(out, bad) {
			t.Errorf("a memory kill was reported as a proof error (%q):\n%s", bad, out)
		}
	}
	if _, err := os.Stat(report); err == nil {
		t.Error("verified.json written for a killed verification")
	}
}

// TestMemGuardKillsHungryProof runs a deliberately memory-hungry proof in a separate janus
// process under a 1 GiB limit: directly (the detected mechanism), and nested in a job-level guard
// of scripts/lib/memguard.sh (janus then limits its jobs with child cgroups of that guard).
func TestMemGuardKillsHungryProof(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	bin := buildJanusBinary(t)
	base := envWith("JANUS_MEM_MAX=1G", "JANUS_MEMGUARD=", "JANUS_MEMGUARD_CGROUP=", "JANUS_MEMGUARD_VERBOSE=1")
	mech := guardedMech(t, bin, base)
	dir := mustExtract(t, "example.com/basic.Get")
	proof := filepath.Join(t.TempDir(), "Hungry.lean")
	writeFile(t, proof, hungryProof)
	report := filepath.Join(dir, "verified.json")
	verify := func(env []string, argv ...string) (int, string) {
		cmd := exec.Command(argv[0], append(argv[1:], "verify", dir, "--proof", proof, "--janus-root", repoRoot)...)
		cmd.Env = env
		var b bytes.Buffer
		cmd.Stdout, cmd.Stderr = &b, &b
		err := cmd.Run()
		code := 0
		if ee, ok := err.(*exec.ExitError); ok {
			code = ee.ExitCode()
		} else if err != nil {
			t.Fatal(err)
		}
		return code, b.String()
	}
	t.Run("direct", func(t *testing.T) {
		code, out := verify(base, bin)
		if code != 1 {
			t.Fatalf("exit %d:\n%s", code, out)
		}
		if !strings.Contains(out, "memory guard: "+mech) || !strings.Contains(out, "mechanism "+mech) {
			t.Errorf("mechanism %s not reported:\n%s", mech, out)
		}
		checkResourceLimit(t, out, report)
	})
	t.Run("nested", func(t *testing.T) {
		if mech == "cgroup" {
			t.Skip("already nested")
		}
		// A 4 GiB job-level guard (as scripts/lib/parallel.sh gives each slot) around janus,
		// whose per-job limit is 1 GiB: the job is killed by janus's own child cgroup.
		code, out := verify(base, "bash", filepath.Join(repoRoot, "scripts", "lib", "memguard.sh"), "run", "-l", "4G", "-n", "slot", "--", bin)
		if code != 1 {
			t.Fatalf("exit %d:\n%s", code, out)
		}
		if !strings.Contains(out, "memory guard: cgroup") || !strings.Contains(out, "mechanism cgroup") {
			t.Errorf("janus did not nest its job cgroups in the job-level guard:\n%s", out)
		}
		checkResourceLimit(t, out, report)
		if !strings.Contains(out, "memguard[slot]: peak ") || !strings.Contains(out, "limit 4.0 GiB") {
			t.Errorf("job-level guard summary missing:\n%s", out)
		}
		if strings.Contains(out, "OOM-KILLED") {
			t.Errorf("the job-level guard claimed a kill made by janus's own limit:\n%s", out)
		}
	})
}

// TestMemGuardNormalVerify: honest proofs verify under the default limit, and verified.json
// records the guard and the measured peak.
func TestMemGuardNormalVerify(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	bin := buildJanusBinary(t)
	// The configured limit (JANUS_MEM_MAX, as CI sets it on small runners) or the default.
	env := envWith("JANUS_MEMGUARD=", "JANUS_MEMGUARD_CGROUP=")
	mech := guardedMech(t, bin, env)
	want := defaultMemLimit()
	if v := os.Getenv("JANUS_MEM_MAX"); v != "" {
		n, err := parseMemSize(v)
		if err != nil {
			t.Skipf("JANUS_MEM_MAX=%q", v)
		}
		want = n
	}
	for _, ex := range []string{"Add", "Max"} {
		dir := mustExtract(t, "example.com/basic."+ex)
		proof := filepath.Join(repoRoot, "examples", "proofs", ex+".lean")
		if _, err := os.Stat(proof); err != nil {
			t.Fatalf("missing example proof %s", proof)
		}
		cmd := exec.Command(bin, "verify", dir, "--proof", proof, "--janus-root", repoRoot)
		cmd.Env = env
		out, err := cmd.CombinedOutput()
		if err != nil || !strings.Contains(string(out), "Verified: ") {
			t.Fatalf("%s: %v\n%s", ex, err, out)
		}
		var r verifiedReport
		b, err := os.ReadFile(filepath.Join(dir, "verified.json"))
		if err != nil || json.Unmarshal(b, &r) != nil {
			t.Fatalf("%s: verified.json: %v", ex, err)
		}
		mg := r.MemoryGuard
		if mg == nil || mg.Mechanism != mech || mg.LimitBytes != want || mg.Jobs == 0 ||
			mg.PeakBytes <= 0 || mg.PeakBytes >= mg.LimitBytes {
			t.Fatalf("%s: memoryGuard %+v", ex, mg)
		}
		t.Logf("%s: %d guarded jobs, peak %s of %s (%s)", ex, mg.Jobs, mg.Peak, mg.Limit, mg.Mechanism)
	}
}

// TestMemGuardBadLimit: an unparsable JANUS_MEM_MAX is refused before anything runs.
func TestMemGuardBadLimit(t *testing.T) {
	t.Setenv("JANUS_MEM_MAX", "lots")
	resetMemGuardForTest()
	defer resetMemGuardForTest()
	code, _, stderr := runJanus(t, "memguard")
	if code != 1 || !strings.Contains(stderr, "Stage: resource limit") || !strings.Contains(stderr, `JANUS_MEM_MAX="lots"`) {
		t.Fatalf("%d %s", code, stderr)
	}
}

// TestMemGuardFailureDiag: a job the guard itself could not run (no scope, no supervisor
// report) is a resource-limit failure, never the job's own (meaningless) error.
func TestMemGuardFailureDiag(t *testing.T) {
	mark := memMark()
	recordMem(memEvent{Label: "lean Proof.lean", Limit: 1 << 30, GuardErr: "systemd-run: exit status 1: Failed to start transient scope unit"})
	_, err := memOutcome(mark, &verifiedReport{}, &diag{Stage: "proof checking", Msg: "Lean rejected the proof"})
	d, ok := err.(*diag)
	if !ok || d.Stage != "resource limit" || !strings.Contains(d.Msg, "could not run lean Proof.lean") || !strings.Contains(d.Msg, "transient scope") {
		t.Fatalf("%#v", err)
	}
	// A clean run records the guard and the peak in the report.
	mark = memMark()
	recordMem(memEvent{Label: "lean Proof.lean", Limit: 1 << 30, Peak: 300 << 20})
	r, err := memOutcome(mark, &verifiedReport{}, nil)
	if err != nil || r.MemoryGuard == nil || r.MemoryGuard.PeakBytes != 300<<20 || r.MemoryGuard.Jobs != 1 {
		t.Fatalf("%v %+v", err, r.MemoryGuard)
	}
}

// TestMemOutcomeSkip: a kill inside a request's own build range is not held against the other
// requests of its group (verify-batch builds each request's import closure separately).
func TestMemOutcomeSkip(t *testing.T) {
	mark := memMark()
	recordMem(memEvent{Label: "lake build A", Limit: 1 << 30, Peak: 1 << 30, Killed: true})
	skip := [][2]int{{mark, memMark()}}
	recordMem(memEvent{Label: "lake build B", Limit: 1 << 30, Peak: 200 << 20})
	r, err := memOutcomeSkip(mark, skip, &verifiedReport{}, nil)
	if err != nil || r.MemoryGuard == nil || r.MemoryGuard.Jobs != 2 {
		t.Fatalf("%v %+v", err, r)
	}
	if _, err := memOutcome(mark, &verifiedReport{}, nil); err == nil {
		t.Fatal("an unskipped kill must fail the result")
	}
}

// TestMemguardShell exercises scripts/lib/memguard.sh as the runner scripts use it (sourced
// under set -euo pipefail): a command's status passes through, a command over its limit is
// OOM-killed (137) with the summary line, nested guards report only their own kills, and no
// cgroup is left behind. The memory hog is bash holding a 600 MiB string under a 300M limit.
func TestMemguardShell(t *testing.T) {
	defer parallel(t)()
	lib := filepath.Join(repoRoot, "scripts", "lib", "memguard.sh")
	mech, err := exec.Command("bash", lib, "mechanism").Output()
	m := strings.TrimSpace(string(mech))
	if err != nil || (m != "cgroup" && m != "systemd-user" && m != "systemd-system") {
		t.Skipf("no cgroup mechanism for scripts (%q, %v)", m, err)
	}
	hog := `x=$(head -c 629145600 /dev/zero | tr '\0' a); echo ${#x}`
	script := `set -euo pipefail
. "$1"
st=0; memguard_run -l 300M -n ok -- true || st=$?; echo "ok=$st"
st=0; memguard_run -l 300M -n three -- bash -c 'exit 3' || st=$?; echo "three=$st"
st=0; memguard_run -l 300M -n hog -- bash -c "$2" || st=$?; echo "hog=$st"
st=0; memguard_run -l 2G -n outer -- bash "$1" run -l 300M -n inner -- bash -c "$2" || st=$?; echo "nested=$st"
memguard_run -l 300M -n verbatim -- bash -c 'echo "arg=${#HOME}:$HOME"'
st=0; memguard_lake --version >/dev/null || st=$?; echo "lake=$st"
echo "jobs=$(memguard_jobs 3G 8)"
echo done`
	cmd := exec.Command("bash", "-c", script, "memguard-test", lib, hog)
	cmd.Env = envWith("JANUS_MEMGUARD=", "JANUS_MEMGUARD_CGROUP=", "JANUS_MEM_MAX=")
	out, err := cmd.CombinedOutput()
	s := string(out)
	if err != nil {
		t.Fatalf("%v\n%s", err, s)
	}
	for _, want := range []string{"ok=0", "three=3", "hog=137", "memguard[hog]: peak ", "/ limit 300 MiB", "OOM-KILLED",
		"memguard[inner]: ", "memguard[outer]: ", "(a nested guard killed one of its jobs)", "done"} {
		if !strings.Contains(s, want) {
			t.Errorf("output lacks %q:\n%s", want, s)
		}
	}
	if !regexp.MustCompile(`memguard\[hog\]: peak .* OOM-KILLED`).MatchString(s) {
		t.Errorf("the hog's own guard did not report the kill:\n%s", s)
	}
	if h := os.Getenv("HOME"); !strings.Contains(s, fmt.Sprintf("arg=%d:%s", len(h), h)) {
		t.Errorf("arguments were not passed verbatim (systemd-run expansion?):\n%s", s)
	}
	if !strings.Contains(s, "nested=137") {
		t.Errorf("the nested hog's status was not passed through:\n%s", s)
	}
	if _, err := findLake(); err == nil && !strings.Contains(s, "lake=0") {
		t.Errorf("memguard_lake failed:\n%s", s)
	}
	if !regexpJobs.MatchString(s) {
		t.Errorf("memguard_jobs:\n%s", s)
	}
	t.Logf("%s", s)
}

var regexpJobs = regexp.MustCompile(`(?m)^jobs=[1-8]$`)

func TestLeanThreadsMax(t *testing.T) {
	t.Setenv("JANUS_LEAN_THREADS_MAX", "3")
	if got := leanThreadsMax(); got != 3 {
		t.Fatalf("JANUS_LEAN_THREADS_MAX=3: got %d", got)
	}
	if got := lakeJobs(); got > 3 {
		t.Fatalf("lakeJobs exceeds the CPU cap: %d", got)
	}
	t.Setenv("JANUS_LEAN_THREADS_MAX", "bogus")
	if got := leanThreadsMax(); got < 2 {
		t.Fatalf("default cap below 2: %d", got)
	}
}

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

// Concurrent janus processes on one machine share the framework build (the cached base of the
// embedded framework, or a --janus-root checkout). Before the shared/exclusive locking of
// framework.go, a writer (`janus blockers` building janus-decode, which adds
// Janus.Tools.Decode) failed every verification that was using the build with "framework
// integrity … unexpected Janus/Tools/Decode.olean" (docs/AUDIT-ASL.md, C1).

// buildJanusBinary builds this command into a temporary directory: the tests below run real,
// separate janus processes, as concurrent users do.
func buildJanusBinary(t *testing.T) string {
	t.Helper()
	bin := filepath.Join(t.TempDir(), "janus")
	cmd := exec.Command("go", "build", "-o", bin, ".")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go build: %v\n%s", err, out)
	}
	return bin
}

type janusProc struct {
	name string
	args []string
	wait time.Duration // start delay
	code int
	out  string
}

// runConcurrently starts every process (after its delay) and waits for all of them.
func runConcurrently(bin string, env []string, procs []*janusProc) {
	var wg sync.WaitGroup
	for _, p := range procs {
		wg.Add(1)
		go func(p *janusProc) {
			defer wg.Done()
			time.Sleep(p.wait)
			cmd := exec.Command(bin, p.args...)
			cmd.Env = env
			var b bytes.Buffer
			cmd.Stdout, cmd.Stderr = &b, &b
			err := cmd.Run()
			p.code, p.out = 0, b.String()
			if err != nil {
				p.code = 1
				if ee, ok := err.(*exec.ExitError); ok {
					p.code = ee.ExitCode()
				}
			}
		}(p)
	}
	wg.Wait()
}

func sandboxArgs() []string {
	if _, err := detectSandbox(false); err != nil {
		return []string{"--unsafe-no-sandbox"}
	}
	return nil
}

// testEnv is the environment of the janus subprocesses: the test cache, no JANUS_ROOT.
func testEnv() []string {
	var env []string
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "JANUS_ROOT=") && !strings.HasPrefix(e, "JANUS_CACHE_DIR=") {
			env = append(env, e)
		}
	}
	return append(env, "JANUS_CACHE_DIR="+cacheRoot())
}

func embeddedBase(t *testing.T) string {
	t.Helper()
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	return filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])
}

// TestConcurrentVerify runs verifications in parallel, of the same artifact and of different
// ones, while `janus blockers` builds the decoder in the same framework build, first on the
// cached embedded framework and then on a --janus-root checkout. Every one must succeed.
func TestConcurrentVerify(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	bin := buildJanusBinary(t)
	sb := sandboxArgs()
	add := mustExtract(t, "example.com/basic.Add")
	arts := map[string]string{"Add": add}
	for _, n := range []string{"Max", "Mul64", "Add128"} {
		arts[n] = mustExtract(t, "example.com/basic."+n)
	}
	verifyArgs := func(n string, extra ...string) []string {
		a := []string{"verify", arts[n], "--proof", filepath.Join(repoRoot, "examples", "proofs", n+".lean")}
		return append(append(a, sb...), extra...)
	}
	env := testEnv()
	check := func(procs []*janusProc) {
		t.Helper()
		for _, p := range procs {
			ok := p.code == 0
			if strings.HasPrefix(p.args[0], "verify") {
				ok = ok && strings.Contains(p.out, "Verified: ")
			}
			if !ok {
				t.Errorf("%s failed (exit %d):\n%s", p.name, p.code, p.out)
			}
		}
	}

	// Make sure the base exists (built once per framework version; may take long the first time).
	if code, _, stderr := runJanus(t, verifyArgs("Add")...); code != 0 {
		t.Fatalf("priming verify: %s", stderr)
	}
	// Then make the decoder build a real writer: drop the stamp and the decoder module, so the
	// first process rebuilds and stamps, and blockers compiles Janus.Tools.Decode again while
	// verifications are using the build.
	base := embeddedBase(t)
	_ = os.Remove(base + ".ready")
	removeModuleOutputs(filepath.Join(base, ".lake", "build", "lib", "lean"), "Janus.Tools.Decode")

	var procs []*janusProc
	for i, n := range []string{"Add", "Add", "Add", "Max", "Mul64", "Add128"} {
		procs = append(procs, &janusProc{name: fmt.Sprintf("verify#%d %s", i, n), args: verifyArgs(n), wait: time.Duration(i) * 500 * time.Millisecond})
	}
	procs = append(procs, &janusProc{name: "blockers", wait: 2 * time.Second,
		args: []string{"blockers", exampleBin, "example.com/basic.Add", "example.com/basic.Max"}})
	for i, n := range []string{"Add", "Max"} {
		procs = append(procs, &janusProc{name: fmt.Sprintf("late verify#%d %s", i, n), args: verifyArgs(n), wait: 4 * time.Second})
	}
	runConcurrently(bin, env, procs)
	check(procs)
	b, err := os.ReadFile(base + ".ready")
	if err != nil {
		t.Fatalf("no ready stamp after the runs: %v", err)
	}
	var st frameworkStamp
	if err := json.Unmarshal(b, &st); err != nil || !strings.Contains(strings.Join(st.Targets, " "), "janus-decode") {
		t.Errorf("ready stamp lacks janus-decode: %s", b)
	}

	// A --janus-root checkout: the lock and stamp live in its .lake/.
	procs = nil
	for i, n := range []string{"Add", "Add", "Max", "Mul64"} {
		procs = append(procs, &janusProc{name: fmt.Sprintf("checkout verify#%d %s", i, n), args: verifyArgs(n, "--janus-root", repoRoot),
			wait: time.Duration(i) * 300 * time.Millisecond})
	}
	procs = append(procs, &janusProc{name: "checkout blockers", wait: time.Second,
		args: []string{"blockers", exampleBin, "example.com/basic.Add", "--janus-root", repoRoot}})
	runConcurrently(bin, env, procs)
	check(procs)
}

// TestForeignFrameworkWriteDetected: a write to the framework build that does not go through
// the lock (here the proof itself, compiled without a sandbox, appends to a framework olean) is
// still rejected as "framework integrity", and the next verification repairs the build.
func TestForeignFrameworkWriteDetected(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	bin := buildJanusBinary(t)
	add := mustExtract(t, "example.com/basic.Add")
	env := testEnv()
	good := []string{"verify", add, "--proof", filepath.Join(repoRoot, "examples", "proofs", "Add.lean"), "--unsafe-no-sandbox"}
	p := []*janusProc{{name: "priming verify", args: good}}
	runConcurrently(bin, env, p)
	if p[0].code != 0 {
		t.Fatalf("priming verify failed:\n%s", p[0].out)
	}
	target := filepath.Join(embeddedBase(t), ".lake", "build", "lib", "lean", "Janus", "Tools", "Audit.olean")
	before, err := os.ReadFile(target)
	if err != nil {
		t.Fatal(err)
	}
	proof := writeProof(t, fmt.Sprintf(`import Extracted

#eval show IO Unit from do
  let h ← IO.FS.Handle.mk %q .append
  h.putStr "forged"

theorem correctness : True := trivial
`, target))
	evil := []*janusProc{{name: "foreign write", args: []string{"verify", add, "--proof", proof, "--unsafe-no-sandbox"}}}
	runConcurrently(bin, env, evil)
	if evil[0].code == 0 || !strings.Contains(evil[0].out, "Stage: framework integrity") ||
		!strings.Contains(evil[0].out, "modified Janus/Tools/Audit.olean") {
		t.Fatalf("foreign write to the framework build not detected (exit %d):\n%s", evil[0].code, evil[0].out)
	}
	// The damaged build no longer matches its stamp: the next use rebuilds the module.
	after := []*janusProc{{name: "verify after repair", args: good}}
	runConcurrently(bin, env, after)
	if after[0].code != 0 {
		t.Fatalf("verify after the foreign write failed:\n%s", after[0].out)
	}
	now, _ := os.ReadFile(target)
	if !bytes.Equal(now, before) {
		t.Errorf("Janus/Tools/Audit.olean was not rebuilt to its original bytes")
	}
}

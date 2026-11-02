package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Leases of consumer workspaces (the flock on <ws>.lock held for the whole use of a workspace),
// the busy marker that makes a half-written workspace a miss, and the collector's honest report.

// TestHelperLease is not a test: the child process of TestCacheGCLeasedWorkspaceSurvives. It takes
// the lease of a workspace as a verification does (lockEntry + beginUse), prints "leased", and
// holds it until its standard input closes (or it is killed).
func TestHelperLease(t *testing.T) {
	dir := os.Getenv("JANUS_TEST_LEASE_DIR")
	if dir == "" {
		t.Skip("helper process")
	}
	lk, err := lockEntry(dir, dir+".lock")
	if err != nil {
		fmt.Println("error", err)
		os.Exit(2)
	}
	ws := &consumerWS{Dir: dir, lock: lk}
	if err := ws.beginUse(); err != nil {
		fmt.Println("error", err)
		os.Exit(2)
	}
	fmt.Println("leased")
	_, _ = bufio.NewReader(os.Stdin).ReadByte()
	ws.endUse()
	lk.unlock()
}

func startLeaseHolder(t *testing.T, root, dir string) (kill func(), release func()) {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^TestHelperLease$")
	cmd.Env = append(cacheEnv(root), "JANUS_TEST_LEASE_DIR="+dir)
	in, _ := cmd.StdinPipe()
	out, _ := cmd.StdoutPipe()
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	line, _ := bufio.NewReader(out).ReadString('\n')
	if strings.TrimSpace(line) != "leased" {
		t.Fatalf("lease holder said %q", line)
	}
	var once sync.Once
	reap := func() { once.Do(func() { _ = cmd.Wait() }) }
	t.Cleanup(func() { _ = cmd.Process.Kill(); reap() })
	return func() { _ = cmd.Process.Kill(); reap() }, func() { in.Close(); reap() }
}

// runGCJSON runs `janus cache gc --max 0 --grace 0s --json` in a separate process.
func runGCJSON(t *testing.T, bin, root string) gcReport {
	t.Helper()
	cmd := exec.Command(bin, "cache", "gc", "--max", "0", "--grace", "0s", "--json")
	cmd.Env = cacheEnv(root)
	out, err := cmd.Output()
	if err != nil {
		t.Fatalf("cache gc: %v\n%s", err, out)
	}
	var rep gcReport
	if err := json.Unmarshal(out, &rep); err != nil {
		t.Fatalf("cache gc output: %v\n%s", err, out)
	}
	return rep
}

// TestCacheGCLeasedWorkspaceSurvives: a workspace leased by another process (taken exactly as
// openWorkspace takes it) survives `cache gc --max 0 --grace 0s` run in a third process and is
// reported as in use; an idle workspace is collected. When the holder dies the lease vanishes
// with it: the abandoned workspace (its busy marker still there) is collected whole, marker too.
func TestCacheGCLeasedWorkspaceSurvives(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("go not installed")
	}
	f := newGCFixture(t)
	bin := buildJanusBinary(t)
	old := 48 * time.Hour
	idle := f.locked("consumer/fam/idle", 4096, old)
	leased := f.locked("consumer/fam/leased", 4096, old)
	kill, _ := startLeaseHolder(t, f.root, leased)
	if !exists(busyMarker(leased)) {
		t.Fatal("the lease holder did not mark the workspace busy")
	}
	// The holder's beginUse and touch made the workspace recent; age everything as an idle build.
	f.age("consumer/fam/leased", old)
	f.age("consumer/fam/leased.lock", old)

	rep := runGCJSON(t, bin, f.root)
	if !exists(leased) || !exists(filepath.Join(leased, "data", "blob")) {
		t.Fatalf("the leased workspace was collected (evicted %v)", evictedPaths(&rep))
	}
	if exists(idle) {
		t.Errorf("the idle workspace survived --max 0")
	}
	if rep.Skipped != 1 || len(rep.InUsePaths) != 1 || rep.InUsePaths[0] != leased {
		t.Errorf("report: skipped %d, in use %v; want exactly %s", rep.Skipped, rep.InUsePaths, leased)
	}
	// Dry runs and `cache du` agree.
	s := scanCache(f.root)
	found := false
	for _, e := range s.entries {
		if e.Path == leased {
			found = e.probeInUse()
		}
	}
	if !found {
		t.Errorf("cache du does not see the lease")
	}

	kill() // the holder dies without cleaning up: the kernel drops the lease
	rep = runGCJSON(t, bin, f.root)
	if exists(leased) || exists(busyMarker(leased)) || exists(leased+".lock") {
		t.Errorf("the abandoned workspace (or its marker) survived: %v", evictedPaths(&rep))
	}
	if rep.Skipped != 0 {
		t.Errorf("skipped %d after the holder died", rep.Skipped)
	}
}

// TestWorkspaceHalfWrittenIsRebuilt: a workspace whose holder died (busy marker present) is
// discarded whole by the next opener and starts empty; a cleanly closed one is kept; neither a
// dead nor a busy workspace seeds a sibling.
func TestWorkspaceHalfWrittenIsRebuilt(t *testing.T) {
	f := newGCFixture(t)
	fam := f.p("consumer/fam")
	mk := func(name string) string {
		d := filepath.Join(fam, name)
		for _, p := range []string{"root/.lake/build/lib/lean/A.olean", "janus/.lake/build/lib/lean/Janus.olean"} {
			if err := os.MkdirAll(filepath.Dir(filepath.Join(d, p)), 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(filepath.Join(d, p), []byte("x"), 0o644); err != nil {
				t.Fatal(err)
			}
		}
		return d
	}
	open := func(d string) *consumerWS {
		lk, err := lockEntry(d, d+".lock")
		if err != nil {
			t.Fatal(err)
		}
		ws := &consumerWS{Dir: d, lock: lk}
		if err := ws.beginUse(); err != nil {
			t.Fatal(err)
		}
		return ws
	}
	half := mk("half")
	if err := os.WriteFile(busyMarker(half), []byte("1\n"), 0o644); err != nil { // a dead holder's marker
		t.Fatal(err)
	}
	good := mk("good")
	older := time.Now().Add(-time.Hour)
	_ = os.Chtimes(half, older, older)

	if sib, lk := newestSibling(fam, filepath.Join(fam, "other")); sib != good {
		t.Fatalf("seed = %q, want the consistent workspace %q", sib, good)
	} else {
		lk.unlock()
	}
	ws := open(half)
	if entries, _ := os.ReadDir(half); len(entries) != 0 {
		t.Errorf("the half-written workspace was reused: %v", entries)
	}
	if !exists(busyMarker(half)) {
		t.Errorf("no busy marker while in use")
	}
	// While in use it is no seed either.
	if sib, lk := newestSibling(fam, filepath.Join(fam, "other")); sib == half {
		lk.unlock()
		t.Errorf("a busy workspace was chosen as a seed")
	}
	ws.opened = true
	ws.close()
	if exists(busyMarker(half)) {
		t.Errorf("busy marker left after a clean close")
	}
	ws = open(good) // consistent: kept as is (incremental builds)
	if !exists(filepath.Join(good, "root/.lake/build/lib/lean/A.olean")) {
		t.Errorf("a consistent workspace was discarded")
	}
	ws.opened = true
	ws.close()
	// No trash is left behind by the discard.
	if ents, _ := os.ReadDir(f.p("tmp")); len(ents) != 0 {
		t.Errorf("trash left in v1/tmp: %v", ents)
	}
}

// TestCacheGCStressLeases: many concurrent real janus processes lease, mark and release a few
// workspaces while a collector loops with --max 0 --grace 0s. A workspace is never taken from
// under a holder (its files stay readable while leased) and no holder ever sees a partial one.
func TestCacheGCStressLeases(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("go not installed")
	}
	f := newGCFixture(t)
	fam := f.p("consumer/fam")
	var stop atomic.Bool
	var gcRuns, uses atomic.Int64
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for !stop.Load() {
			if _, err := collectCache(gcOptions{Max: 0, Grace: 0, Now: time.Now().Add(time.Second)}, true); err != nil {
				t.Errorf("collect: %v", err)
				return
			}
			gcRuns.Add(1)
		}
	}()
	var users sync.WaitGroup
	for u := 0; u < 6; u++ {
		users.Add(1)
		go func(u int) {
			defer users.Done()
			d := filepath.Join(fam, fmt.Sprintf("ws%d", u%3)) // two users per workspace
			for i := 0; i < 150; i++ {
				lk, err := lockEntry(d, d+".lock")
				if err != nil {
					t.Errorf("lockEntry: %v", err)
					return
				}
				ws := &consumerWS{Dir: d, lock: lk}
				if err := ws.beginUse(); err != nil {
					t.Errorf("beginUse: %v", err)
					lk.unlock()
					return
				}
				// What a verification does: write, then read back while holding the lease. A
				// collector that took the workspace from under it would break one of these.
				a := filepath.Join(d, "root", ".lake", "build", "m.olean")
				if err := os.MkdirAll(filepath.Dir(a), 0o755); err != nil {
					t.Errorf("mkdir under lease: %v", err)
				}
				if err := os.WriteFile(a, []byte(fmt.Sprint(u, i)), 0o644); err != nil {
					t.Errorf("write under lease: %v", err)
				}
				time.Sleep(time.Millisecond)
				if b, err := os.ReadFile(a); err != nil || string(b) != fmt.Sprint(u, i) {
					t.Errorf("workspace changed under its lease: %q %v", b, err)
				}
				ws.opened = true
				ws.close()
				uses.Add(1)
			}
		}(u)
	}
	users.Wait()
	stop.Store(true)
	wg.Wait()
	if gcRuns.Load() < 5 || uses.Load() != 900 {
		t.Errorf("%d collections, %d uses", gcRuns.Load(), uses.Load())
	}
	t.Logf("%d collections, %d uses", gcRuns.Load(), uses.Load())
}

// TestCacheGCStressConsumerVerifies: real consumer-package verifications of two extractions (two
// sibling workspaces of one family: each seeds from the other) in separate processes, repeatedly
// and concurrently, while `cache gc --max 0 --grace 0s` loops. Every verification must pass
// (none may see a missing or partial workspace) and the report must be a genuine kernel replay.
func TestCacheGCStressConsumerVerifies(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	cache := seededCache(t)
	bin := buildJanusBinary(t)
	sb := sandboxArgs()
	env := cacheEnv(cache)
	pkg := consumerCopy(t, "toml")
	args := func(n string) []string {
		return append([]string{"verify", mustExtract(t, "example.com/basic."+n), "--proof", filepath.Join(pkg, "ConsumerExample", n+".lean"),
			"--proof-root", pkg, "--theorem", "ConsumerExample." + n + ".correctness", "--json"}, sb...)
	}
	add, max := args("Add"), args("Max")
	var stop atomic.Bool
	var gcRuns, gcSkipped atomic.Int64
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for !stop.Load() {
			cmd := exec.Command(bin, "cache", "gc", "--max", "0", "--grace", "0s", "--json")
			cmd.Env = env
			out, err := cmd.Output()
			if err != nil {
				t.Errorf("cache gc: %v", err)
				return
			}
			var rep gcReport
			if json.Unmarshal(out, &rep) == nil {
				gcSkipped.Add(int64(rep.Skipped))
			}
			gcRuns.Add(1)
			time.Sleep(50 * time.Millisecond)
		}
	}()
	start := time.Now()
	for round := 0; round < 2; round++ {
		var procs []*janusProc
		for i, a := range [][]string{add, max, add, max} {
			procs = append(procs, &janusProc{name: fmt.Sprintf("round %d verify#%d", round, i), args: a, wait: time.Duration(i) * 400 * time.Millisecond})
		}
		runConcurrently(bin, env, procs)
		for _, p := range procs {
			if p.code != 0 || !strings.Contains(p.out, `"theorem"`) || strings.Contains(p.out, "is not a module") {
				t.Errorf("%s failed under the collector (exit %d):\n%s", p.name, p.code, p.out)
			}
		}
	}
	stop.Store(true)
	wg.Wait()
	t.Logf("%d collections (%d leased entries skipped) during 8 verifications: %.1fs", gcRuns.Load(), gcSkipped.Load(), time.Since(start).Seconds())
	if gcRuns.Load() < 3 {
		t.Errorf("only %d collections ran", gcRuns.Load())
	}
}

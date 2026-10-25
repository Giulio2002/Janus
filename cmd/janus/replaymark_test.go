package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// pendingDone lists the modules replayed in this run (sorted).
func (p *replayPlan) pendingDone() []string {
	var out []string
	for _, m := range p.modules {
		if p.done[m] {
			out = append(out, m)
		}
	}
	return out
}

// fakeFramework is a pinned framework build of three modules (no files: the verdict depends only
// on the pins).
func fakeFramework(sums ...string) *pinnedLib {
	p := pins{"Janus.olean": "00", "Janus/A.olean": "aa", "Janus/A.ir": "a1", "Janus/B.olean": "bb"}
	for i, s := range sums {
		p[fmt.Sprintf("Janus/C%d.olean", i)] = s
	}
	return &pinnedLib{who: "the Janus framework build", dir: "/nonexistent", want: p}
}

// TestFrameworkVerdictKey: the verdict's key changes with every framework module-data file, the
// set of modules and the toolchain, so no verdict outlives a framework edit or a toolchain change.
func TestFrameworkVerdictKey(t *testing.T) {
	base := frameworkVerdictKey("tc1", fakeFramework())
	if base != frameworkVerdictKey("tc1", fakeFramework()) {
		t.Fatal("key not deterministic")
	}
	for name, fw := range map[string]*pinnedLib{
		"edited module":  {want: pins{"Janus.olean": "00", "Janus/A.olean": "ab", "Janus/A.ir": "a1", "Janus/B.olean": "bb"}},
		"edited IR":      {want: pins{"Janus.olean": "00", "Janus/A.olean": "aa", "Janus/A.ir": "a2", "Janus/B.olean": "bb"}},
		"removed module": {want: pins{"Janus.olean": "00", "Janus/A.olean": "aa", "Janus/A.ir": "a1"}},
		"added module":   fakeFramework("cc"),
		"renamed module": {want: pins{"Janus.olean": "00", "Janus/A.olean": "aa", "Janus/A.ir": "a1", "Janus/D.olean": "bb"}},
	} {
		if frameworkVerdictKey("tc1", fw) == base {
			t.Errorf("%s: same verdict key", name)
		}
	}
	if frameworkVerdictKey("tc2", fakeFramework()) == base {
		t.Error("another toolchain: same verdict key")
	}
}

// TestFrameworkVerdictAuthentic: only a verdict janus recorded under this cache's hidden key is a
// hit: a planted file, a marker from another cache (another key), a marker of another kind or key,
// a symbolic link and a truncated marker are all misses. The same holds for module markers.
func TestFrameworkVerdictAuthentic(t *testing.T) {
	privateCache(t)
	fw := fakeFramework()
	k := frameworkVerdictKey("tc", fw)
	if hasFrameworkVerdict(k) {
		t.Fatal("verdict in an empty cache")
	}
	p := frameworkVerdictPath(k)
	writeBytes(t, p, []byte("leanchecker Janus passed\n")) // planted (or written before this change)
	if hasFrameworkVerdict(k) {
		t.Fatal("a planted verdict without a MAC was accepted")
	}
	recordFrameworkVerdict(k, fw)
	if !hasFrameworkVerdict(k) {
		t.Fatal("a recorded verdict missed")
	}
	good, _ := os.ReadFile(p)
	other := frameworkVerdictKey("tc", fakeFramework("cc"))
	// The authentic marker of k copied to the name of another framework build.
	writeBytes(t, frameworkVerdictPath(other), good)
	if hasFrameworkVerdict(other) {
		t.Error("a verdict copied to another framework key was accepted")
	}
	// The verdict as a module marker of the same key (another kind).
	writeBytes(t, moduleMarkerPath(k), good)
	if markerOK(moduleMarkerPath(k), "module", k) {
		t.Error("a framework verdict was accepted as a module marker")
	}
	for name, edit := range map[string]func(){
		"truncated MAC": func() { writeBytes(t, p, good[:len(markerHeader)+20]) },
		"flipped MAC": func() {
			b := append([]byte{}, good...)
			i := len(markerHeader) + 3
			b[i] ^= 1
			writeBytes(t, p, b)
		},
		"symbolic link": func() {
			real := filepath.Join(t.TempDir(), "real")
			writeBytes(t, real, good)
			os.Remove(p)
			if err := os.Symlink(real, p); err != nil {
				t.Fatal(err)
			}
		},
	} {
		edit()
		if hasFrameworkVerdict(k) {
			t.Errorf("%s: accepted", name)
		}
		os.Remove(p)
		writeBytes(t, p, good)
		if !hasFrameworkVerdict(k) {
			t.Fatalf("%s: restoring the authentic verdict missed", name)
		}
	}
	// Another cache key (another cache, or the key replaced): the old verdict fails.
	if err := os.WriteFile(filepath.Join(resultCacheDir(), ".key"), []byte(strings.Repeat("k", 32)), 0o600); err != nil {
		t.Fatal(err)
	}
	if hasFrameworkVerdict(k) {
		t.Error("a verdict verified under another cache key")
	}
}

// TestModuleMarkerPlanted: a module replay marker that janus did not write (named by the right
// key, but without the MAC) does not make the module count as replayed.
func TestModuleMarkerPlanted(t *testing.T) {
	privateCache(t)
	lib := t.TempDir()
	writeBytes(t, filepath.Join(lib, "A.olean"), []byte("a"))
	resolved := map[string]string{"A": filepath.Join(lib, "A.olean")}
	graph := map[string][]string{"A": {"Init"}}
	p, err := planReplay(resolved, graph, "v1", true)
	if err != nil || len(p.todo) != 1 {
		t.Fatalf("plan: %v %v", err, p)
	}
	writeBytes(t, moduleMarkerPath(p.keys["A"]), []byte("A\n")) // the pre-HMAC marker format
	if p2, _ := planReplay(resolved, graph, "v1", true); len(p2.todo) != 1 || len(p2.cached) != 0 {
		t.Fatalf("a planted marker was used: todo %v cached %v", p2.todo, p2.cached)
	}
	p.record([]string{"A"})
	if p3, _ := planReplay(resolved, graph, "v1", true); len(p3.cached) != 1 {
		t.Fatalf("a recorded marker missed: todo %v", p3.todo)
	}
}

// TestFrameworkReplayOnce: concurrent verifications of a framework build without a verdict run
// `leanchecker Janus` once; the others wait and use its verdict. A failing replay records nothing
// and is reported (the plan replays the framework itself). Without the cache (--fresh) every
// verification replays.
func TestFrameworkReplayOnce(t *testing.T) {
	privateCache(t)
	fw := fakeFramework()
	k := frameworkVerdictKey("tc", fw)
	var calls atomic.Int64
	slow := func(argv ...string) (string, error) {
		if len(argv) != 2 || argv[1] != "Janus" {
			t.Errorf("replay argv %v", argv)
		}
		calls.Add(1)
		time.Sleep(300 * time.Millisecond)
		return "", nil
	}
	start := func(run func(...string) (string, error), read, write bool) *fwReplay {
		have, lease := false, (*fileLock)(nil)
		if read {
			have, lease = lookupFrameworkVerdict(k)
		}
		return startFrameworkReplay("leanchecker", run, k, fw, have, lease, read, write)
	}
	// A failing replay first: no verdict, the error is kept.
	f := start(func(...string) (string, error) { return "bad module", fmt.Errorf("exit 1") }, true, true)
	f.wait()
	if f.err == nil || f.out != "bad module" || hasFrameworkVerdict(k) {
		t.Fatalf("failing replay: err %v out %q verdict %v", f.err, f.out, hasFrameworkVerdict(k))
	}
	f.release()
	var wg sync.WaitGroup
	reps := make([]*fwReplay, 6)
	for i := range reps {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			reps[i] = start(slow, true, true)
			reps[i].wait()
		}(i)
	}
	wg.Wait()
	if n := calls.Load(); n != 1 {
		t.Fatalf("%d concurrent verifications ran leanchecker Janus %d times (want once)", len(reps), n)
	}
	ran := 0
	for _, r := range reps {
		if r.ran {
			ran++
		}
		if r.err != nil || !(r.ran || r.waited || r.have) {
			t.Errorf("replay state %+v", r)
		}
	}
	if ran != 1 || !hasFrameworkVerdict(k) {
		t.Fatalf("ran %d, verdict %v", ran, hasFrameworkVerdict(k))
	}
	// Plan application: only the pinned framework modules count, reported as reused.
	for _, r := range reps {
		plan := &replayPlan{modules: []string{"Extracted", "Janus", "Janus.A", "Janus.B", "Janus.Stray", "Proof"}}
		r.apply(plan, fw)
		got := strings.Join(plan.cached, ",")
		if r.ran {
			got = strings.Join(plan.pendingDone(), ",")
		}
		if got != "Janus,Janus.A,Janus.B" {
			t.Errorf("ran %v: the framework replay covered %q", r.ran, got)
		}
		for _, m := range []string{"Extracted", "Janus.Stray", "Proof"} {
			if plan.passed(m) {
				t.Errorf("the framework replay covered %s", m)
			}
		}
	}
	// The verdict in use is not collected; released, it is.
	if rep, err := collectCache(gcOptions{Max: 0, Grace: 0}, true); err != nil || !hasFrameworkVerdict(k) {
		t.Fatalf("a verdict in use was collected: %v %+v", err, rep)
	}
	for _, r := range reps {
		r.release()
	}
	if _, err := collectCache(gcOptions{Max: 0, Grace: 0}, true); err != nil {
		t.Fatal(err)
	}
	if hasFrameworkVerdict(k) || fileExists(frameworkVerdictUsePath(k)) {
		t.Error("an unused verdict (or its lock) survived the collection")
	}
	// The cache off: every run replays and records nothing.
	calls.Store(0)
	for i := 0; i < 2; i++ {
		r := start(slow, false, false)
		r.release()
	}
	if calls.Load() != 2 || hasFrameworkVerdict(k) {
		t.Errorf("without the cache: %d replays, verdict %v", calls.Load(), hasFrameworkVerdict(k))
	}
	// A reader that may not write (no sandbox) uses a verdict, but never records one.
	r := start(slow, true, false)
	r.release()
	if !r.ran || hasFrameworkVerdict(k) {
		t.Errorf("an unsandboxed replay recorded a verdict (ran %v)", r.ran)
	}
}

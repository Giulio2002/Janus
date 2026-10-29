package main

import (
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Tests of the cache collector (cachegc.go) on fixture caches in private temporary
// directories; TestCacheGCConcurrentVerify runs it against real verifications.

// gcFixture is a cache root under a private temporary directory, selected as JANUS_CACHE_DIR.
type gcFixture struct {
	t    *testing.T
	root string
	now  time.Time
}

func newGCFixture(t *testing.T) *gcFixture {
	t.Helper()
	root := filepath.Join(t.TempDir(), "cache")
	if err := os.MkdirAll(filepath.Join(root, "v1"), 0o700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_CACHE_DIR", root)
	for _, v := range []string{"JANUS_CACHE_MAX", "JANUS_CACHE_RETENTION_DAYS", "JANUS_ASL_RETENTION_DAYS", "JANUS_CACHE_TMP_HOURS", "JANUS_CACHE_GC"} {
		t.Setenv(v, "")
	}
	return &gcFixture{t: t, root: root, now: time.Now()}
}

func (f *gcFixture) p(rel string) string { return filepath.Join(f.root, "v1", filepath.FromSlash(rel)) }

// file writes rel with n bytes and sets its modification time to age ago.
func (f *gcFixture) file(rel string, n int, age time.Duration) string {
	f.t.Helper()
	p := f.p(rel)
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		f.t.Fatal(err)
	}
	if err := os.WriteFile(p, make([]byte, n), 0o644); err != nil {
		f.t.Fatal(err)
	}
	f.age(rel, age)
	return p
}

func (f *gcFixture) age(rel string, age time.Duration) {
	f.t.Helper()
	at := f.now.Add(-age)
	if err := os.Chtimes(f.p(rel), at, at); err != nil {
		f.t.Fatal(err)
	}
}

// locked writes a locked entry rel (a directory with one n-byte file, its .lock and the given
// extra sibling files), all last used age ago.
func (f *gcFixture) locked(rel string, n int, age time.Duration, siblings ...string) string {
	f.t.Helper()
	f.file(rel+"/data/blob", n, age)
	f.age(rel+"/data", age)
	f.age(rel, age)
	f.file(rel+".lock", 0, age)
	for _, s := range siblings {
		f.file(rel+s, 10, age)
	}
	return f.p(rel)
}

func (f *gcFixture) gc(o gcOptions) *gcReport {
	f.t.Helper()
	if o.Grace == 0 {
		o.Grace = gcGrace
	}
	// The collector's clock is the fixture's (one second after its reference time, so that "just now"
	// entries are strictly older than a zero grace): priorities (age / weight) depend only on the ages
	// the fixture set, never on how long the test has been running (no drift, no ordering flake).
	if o.Now.IsZero() {
		o.Now = f.now.Add(time.Second)
	}
	rep, err := collectCache(o, true)
	if err != nil {
		f.t.Fatalf("collectCache: %v", err)
	}
	return rep
}

func exists(p string) bool { _, err := os.Lstat(p); return err == nil }

func evictedPaths(rep *gcReport) []string {
	var ps []string
	for _, e := range rep.Evicted {
		ps = append(ps, e.Path)
	}
	return ps
}

func sizeOf(t *testing.T, root, path string) int64 {
	t.Helper()
	for _, e := range scanCache(root).entries {
		if e.Path == path {
			return e.Size
		}
	}
	t.Fatalf("no entry %s", path)
	return 0
}

func TestParseCacheSize(t *testing.T) {
	for in, want := range map[string]int64{"40G": 40 << 30, "500M": 500 << 20, "1.5GiB": 3 << 29, "123": 123, "0": 0,
		"10%": 100, "off": -1, "OFF": -1, "2kb": 2048} {
		got, err := parseCacheSize(in, 1000)
		if err != nil || got != want {
			t.Errorf("parseCacheSize(%q) = %d, %v; want %d", in, got, err, want)
		}
	}
	for _, bad := range []string{"", "x", "-1G", "101%", "G"} {
		if _, err := parseCacheSize(bad, 1000); err == nil {
			t.Errorf("parseCacheSize(%q) accepted", bad)
		}
	}
	if _, err := parseCacheSize("10%", 0); err == nil {
		t.Errorf("a percentage of an unknown filesystem size was accepted")
	}
}

func TestDefaultCacheBudget(t *testing.T) {
	cases := []struct {
		fs   fsInfo
		want int64
	}{
		{fsInfo{size: 874 << 30}, 40 << 30},                    // 10% = 87 GiB: capped at 40 GiB
		{fsInfo{size: 100 << 30}, 10 << 30},                    // 10%
		{fsInfo{size: 126 << 30, ram: true}, (126 << 30) / 20}, // tmpfs: 5%
		{fsInfo{size: 500 << 30, ram: true}, 8 << 30},
		{fsInfo{}, 40 << 30}, // unknown size
	}
	for _, c := range cases {
		if got := defaultCacheBudget(c.fs); got != c.want {
			t.Errorf("defaultCacheBudget(%+v) = %d, want %d", c.fs, got, c.want)
		}
	}
	t.Setenv("JANUS_CACHE_MAX", "1G")
	if b, err := cacheBudget(fsInfo{size: 1 << 40}); err != nil || b != 1<<30 {
		t.Errorf("JANUS_CACHE_MAX=1G: %d %v", b, err)
	}
	t.Setenv("JANUS_CACHE_MAX", "bogus")
	if _, err := cacheBudget(fsInfo{size: 1 << 40}); err == nil {
		t.Errorf("JANUS_CACHE_MAX=bogus accepted")
	}
}

// TestCacheGCLRUOrder: over budget, entries go in order of age / weight (asl 4, framework 2),
// and collection stops as soon as the cache fits.
func TestCacheGCLRUOrder(t *testing.T) {
	f := newGCFixture(t)
	const mb = 1 << 20
	c1 := f.locked("consumer/fam/c1", mb, 4*time.Hour)
	c2 := f.locked("consumer/fam/c2", mb, 3*time.Hour)
	c3 := f.locked("consumer/fam/c3", mb, 2*time.Hour)
	c4 := f.locked("consumer/fam/c4", mb, time.Hour)
	f.age("consumer/fam", time.Hour)
	a1 := f.locked("asl/a1", mb, 14*time.Hour)                // priority 3.5 h
	f1 := f.locked("framework/f1", mb, 5*time.Hour, ".ready") // priority 2.5 h
	a2 := f.locked("asl/a2", mb, 6*time.Hour)                 // priority 1.5 h
	want := []string{c1, a1, c2, f1}
	total := scanCache(f.root).total()
	var drop int64
	for _, p := range want {
		drop += sizeOf(t, f.root, p)
	}
	dry := f.gc(gcOptions{Max: total - drop, DryRun: true})
	if got := evictedPaths(dry); fmt.Sprint(got) != fmt.Sprint(want) {
		t.Fatalf("dry run would evict %v, want %v", got, want)
	}
	for _, p := range want {
		if !exists(p) {
			t.Fatalf("dry run removed %s", p)
		}
	}
	rep := f.gc(gcOptions{Max: total - drop})
	if got := evictedPaths(rep); fmt.Sprint(got) != fmt.Sprint(want) {
		t.Fatalf("evicted %v, want %v", got, want)
	}
	for _, p := range want {
		if exists(p) || exists(p+".lock") {
			t.Errorf("%s (or its lock) still exists", p)
		}
	}
	if exists(f1 + ".ready") {
		t.Errorf("the framework's ready stamp survived its build")
	}
	for _, p := range []string{c3, c4, a2} {
		if !exists(p) || !exists(p+".lock") {
			t.Errorf("%s was removed, though the cache fit without it", p)
		}
	}
	if rep.After > total-drop {
		t.Errorf("after %d > budget %d", rep.After, total-drop)
	}
	// Nothing left in the trash.
	if ents, _ := os.ReadDir(f.p("tmp")); len(ents) != 0 {
		t.Errorf("v1/tmp holds %v after the collection", ents)
	}
}

// TestCacheGCRespectsLocks: an entry whose lock another holder has (consumer workspace:
// exclusive; framework build: shared; JanusASL build: .use shared) is never collected; once it
// is released it is.
func TestCacheGCRespectsLocks(t *testing.T) {
	f := newGCFixture(t)
	ws := f.locked("consumer/fam/ws", 4096, 48*time.Hour)
	fw := f.locked("framework/fw", 4096, 48*time.Hour, ".ready")
	asl := f.locked("asl/a", 4096, 48*time.Hour)
	f.file("asl/a.use", 0, 48*time.Hour)
	aslBuilding := f.locked("asl/b", 4096, 48*time.Hour)

	l1, err := lockFile(ws+".lock", false)
	if err != nil {
		t.Fatal(err)
	}
	l2, err := lockFileMode(fw+".lock", true, false)
	if err != nil {
		t.Fatal(err)
	}
	l3, err := lockFileMode(asl+".use", true, false)
	if err != nil {
		t.Fatal(err)
	}
	l4, err := lockFile(aslBuilding+".lock", false)
	if err != nil {
		t.Fatal(err)
	}
	rep := f.gc(gcOptions{Max: 0})
	if len(rep.Evicted) != 0 || rep.Skipped != 4 {
		t.Fatalf("evicted %v (skipped %d) while all four were in use", evictedPaths(rep), rep.Skipped)
	}
	for _, p := range []string{ws, fw, fw + ".ready", asl, aslBuilding} {
		if !exists(p) {
			t.Fatalf("%s removed while in use", p)
		}
	}
	// `cache du` reports them in use without disturbing them.
	s := scanCache(f.root)
	inUse := 0
	for _, e := range s.entries {
		if e.probeInUse() {
			inUse++
		}
	}
	if inUse != 4 {
		t.Errorf("probeInUse found %d in use, want 4", inUse)
	}
	l1.unlock()
	l2.unlock()
	l3.unlock()
	l4.unlock()
	rep = f.gc(gcOptions{Max: 0})
	if len(rep.Evicted) != 4 {
		t.Fatalf("evicted %v after release, want all four", evictedPaths(rep))
	}
	for _, p := range []string{ws, ws + ".lock", fw, fw + ".lock", fw + ".ready", asl, asl + ".lock", asl + ".use", aslBuilding} {
		if exists(p) {
			t.Errorf("%s survived", p)
		}
	}
}

// TestCacheGCGraceAndPins: recently used entries, the entries this process uses and the
// current framework's entries (Keep) survive even a zero budget; --all drops the Keep list only.
func TestCacheGCGraceAndPins(t *testing.T) {
	f := newGCFixture(t)
	recent := f.locked("consumer/fam/recent", 4096, time.Minute)
	pinned := f.locked("framework/pinned", 4096, 48*time.Hour, ".ready")
	kept := f.locked("asl/kept", 4096, 48*time.Hour)
	old := f.locked("consumer/fam/old", 4096, 48*time.Hour)
	gcPin(pinned)
	defer func() { gcPinMu.Lock(); delete(gcPins, pinned); gcPinMu.Unlock() }()
	rep := f.gc(gcOptions{Max: 0, Keep: []string{kept}})
	if got := evictedPaths(rep); len(got) != 1 || got[0] != old {
		t.Fatalf("evicted %v, want only %s", got, old)
	}
	for _, p := range []string{recent, pinned, kept} {
		if !exists(p) {
			t.Errorf("%s removed", p)
		}
	}
	// A use (touchUse on the lock file) restarts the grace period, even if the directory's own
	// time is old.
	f.age("consumer/fam/recent", 48*time.Hour)
	f.age("consumer/fam/recent.lock", 48*time.Hour)
	touchUse(recent + ".lock")
	if rep := f.gc(gcOptions{Max: 0, Keep: []string{kept}}); len(rep.Evicted) != 0 {
		t.Fatalf("evicted %v right after a use", evictedPaths(rep))
	}
	f.age("consumer/fam/recent.lock", 48*time.Hour)
	rep = f.gc(gcOptions{Max: 0, All: true, Keep: []string{kept}})
	got := evictedPaths(rep)
	sort.Strings(got)
	want := []string{kept, recent}
	sort.Strings(want)
	if fmt.Sprint(got) != fmt.Sprint(want) {
		t.Fatalf("--all evicted %v, want %v (the in-process pin stays)", got, want)
	}
	if !exists(pinned) {
		t.Errorf("--all removed the build this process uses")
	}
	// A zero grace period: everything not in use and not pinned goes.
	f.locked("consumer/fam/fresh", 4096, 0)
	if rep := f.gc(gcOptions{Max: 0, Grace: time.Nanosecond}); len(rep.Evicted) != 1 {
		t.Fatalf("grace 0 evicted %v", evictedPaths(rep))
	}
}

// TestCacheGCRetentionAndTemporary: retention evicts by age whatever the budget; temporary
// trees go after JANUS_CACHE_TMP_HOURS of no change; leftovers (trash, orphaned locks and
// stamps, empty families) are cleaned up; the result key is never touched.
func TestCacheGCRetentionAndTemporary(t *testing.T) {
	f := newGCFixture(t)
	day := 24 * time.Hour
	oldWS := f.locked("consumer/fam/old", 4096, 8*day)
	newWS := f.locked("consumer/fam/new", 4096, 6*day)
	oldFW := f.locked("framework/old", 4096, 8*day, ".ready")
	oldASL := f.locked("asl/old", 4096, 31*day)
	newASL := f.locked("asl/new", 4096, 29*day)
	tmpOld := f.file("tmp/consumer-1/x", 10, 25*time.Hour)
	f.age("tmp/consumer-1", 25*time.Hour)
	tmpNew := f.file("tmp/fresh-2/x", 10, time.Hour)
	runOld := f.file("run/trusted-3/x", 10, 30*time.Hour)
	f.age("run/trusted-3", 30*time.Hour)
	// A run directory whose top is old but whose content changed recently: still in use.
	runBusy := f.file("run/replay-4/deep/x", 10, time.Minute)
	f.age("run/replay-4/deep", 30*time.Hour)
	f.age("run/replay-4", 30*time.Hour)
	trash := f.file("tmp/gc-5/leftover", 10, time.Minute)
	orphanLock := f.file("framework/gone.lock", 0, time.Hour)
	orphanReady := f.file("framework/gone2.ready", 10, time.Hour)
	f.file("consumer/empty/.keep", 0, 0)
	os.Remove(f.p("consumer/empty/.keep"))
	f.age("consumer/empty", time.Hour)
	key := f.file("result/.key", 32, 100*day)
	os.Chmod(key, 0o600)
	res := f.file("result/ab/abcd.json", 100, 2*day)

	rep := f.gc(gcOptions{Max: -1})
	got := map[string]bool{}
	for _, p := range evictedPaths(rep) {
		got[p] = true
	}
	for _, p := range []string{oldWS, oldFW, oldASL, filepath.Dir(tmpOld), filepath.Dir(runOld)} {
		if !got[p] || exists(p) {
			t.Errorf("%s not evicted (evicted %v)", p, evictedPaths(rep))
		}
	}
	for _, p := range []string{newWS, newASL, tmpNew, runBusy, key, res} {
		if !exists(p) {
			t.Errorf("%s removed", p)
		}
	}
	for _, p := range []string{filepath.Dir(trash), orphanLock, orphanReady, f.p("consumer/empty")} {
		if exists(p) {
			t.Errorf("leftover %s not cleaned up", p)
		}
	}
	t.Setenv("JANUS_CACHE_RETENTION_DAYS", "5")
	if rep := f.gc(gcOptions{Max: -1}); len(rep.Evicted) != 1 || rep.Evicted[0].Path != newWS {
		t.Errorf("JANUS_CACHE_RETENTION_DAYS=5 evicted %v", evictedPaths(rep))
	}
	// A zero budget takes every lock-less entry too, never the key.
	f.file("trusted/ab/abcdef/manifest.json", 10, 2*day)
	f.age("trusted/ab/abcdef", 2*day)
	f.file("replay/ab/abcdef", 0, 2*day)
	f.file("replay/early/ab/abcdef", 0, 2*day)
	f.file("replay/locks/0123.lock", 0, 2*day)
	f.gc(gcOptions{Max: 0})
	for _, p := range []string{"trusted/ab/abcdef", "replay/ab/abcdef", "replay/early/ab/abcdef", "replay/locks/0123.lock", "result/ab/abcd.json"} {
		if exists(f.p(p)) {
			t.Errorf("%s survived a zero budget", p)
		}
	}
	if b, err := os.ReadFile(key); err != nil || len(b) != 32 {
		t.Errorf("the result key was touched: %v", err)
	}
	for _, d := range []string{"trusted/ab", "result/ab", "replay/ab"} {
		if !exists(f.p(d)) {
			t.Errorf("shard %s removed (a concurrent store creates entries in it)", d)
		}
	}
}

// TestCacheGCLowDisk: with less free space than min(20 GiB, 5%), the budget shrinks by the
// shortfall, even with JANUS_CACHE_MAX=off.
func TestCacheGCLowDisk(t *testing.T) {
	f := newGCFixture(t)
	a := f.locked("consumer/fam/a", 1<<20, 3*time.Hour)
	b := f.locked("consumer/fam/b", 1<<20, 2*time.Hour)
	defer func(old func(string) fsInfo) { cacheStatFS = old }(cacheStatFS)
	// 100 MiB filesystem, 5% = 5 MiB must stay free; 4.5 MiB are: 0.5 MiB short.
	cacheStatFS = func(string) fsInfo { return fsInfo{size: 100 << 20, avail: 9 << 19} }
	rep := f.gc(gcOptions{Max: -1})
	if got := evictedPaths(rep); len(got) != 1 || got[0] != a || !exists(b) {
		t.Fatalf("low disk evicted %v, want only %s", got, a)
	}
	if !strings.Contains(rep.Reason, "free") {
		t.Errorf("no reason given: %q", rep.Reason)
	}
}

// TestCacheGCRedTeam: what a planted tree can and cannot make the collector do.
func TestCacheGCRedTeam(t *testing.T) {
	f := newGCFixture(t)
	outside := filepath.Join(t.TempDir(), "precious")
	if err := os.MkdirAll(outside, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(outside, "f"), []byte("keep"), 0o644); err != nil {
		t.Fatal(err)
	}
	// A workspace (sandbox-writable for the consumer's own build) with a symbolic link out of the
	// cache, and a directory entry that is itself a symbolic link.
	ws := f.locked("consumer/fam/ws", 10, 48*time.Hour)
	if err := os.Symlink(outside, filepath.Join(ws, "escape")); err != nil {
		t.Fatal(err)
	}
	os.MkdirAll(f.p("asl"), 0o755)
	if err := os.Symlink(outside, f.p("asl/link")); err != nil {
		t.Fatal(err)
	}
	// A forged result entry (wrong MAC): never repaired or made authentic by the collector.
	t.Setenv("JANUS_RESULT_CACHE", "")
	if _, err := resultHMACKey(); err != nil {
		t.Fatal(err)
	}
	key := strings.Repeat("ab", 32)
	forged, _ := json.Marshal(resultEntry{Key: key, Report: json.RawMessage(`{"theorem":"forged"}`), MAC: strings.Repeat("0", 64)})
	writeFile(t, resultPath(key), string(forged))
	os.Chmod(resultPath(key), 0o600)
	keyBefore, _ := os.ReadFile(filepath.Join(resultCacheDir(), ".key"))

	snapshot := func() map[string]string {
		m := map[string]string{}
		filepath.WalkDir(f.root, func(p string, d fs.DirEntry, err error) error {
			if err == nil {
				fi, _ := d.Info()
				m[p] = fmt.Sprint(fi.Mode(), fi.Size(), fi.ModTime().UnixNano())
			}
			return nil
		})
		return m
	}
	before := snapshot()
	f.gc(gcOptions{Max: 0, DryRun: true, Grace: time.Nanosecond})
	after := snapshot()
	// Only the collector's own lock is new (and so its directory's time changed).
	for _, m := range []map[string]string{before, after} {
		delete(m, f.p("gc.lock"))
		delete(m, f.p(""))
	}
	for p, v := range before {
		if after[p] != v {
			t.Errorf("a dry run changed %s: %s -> %s", p, v, after[p])
		}
	}
	for p := range after {
		if _, ok := before[p]; !ok {
			t.Errorf("a dry run created %s", p)
		}
	}
	if lookupResult(key) != nil {
		t.Fatalf("the forged entry is accepted")
	}
	f.gc(gcOptions{Max: 0, Grace: time.Nanosecond, All: true})
	if b, err := os.ReadFile(filepath.Join(outside, "f")); err != nil || string(b) != "keep" {
		t.Fatalf("the collector followed a symbolic link out of the cache: %v", err)
	}
	if exists(ws) || exists(f.p("asl/link")) {
		t.Errorf("planted entries not collected")
	}
	if exists(resultPath(key)) {
		t.Errorf("the forged entry survived a zero budget")
	}
	// The collector writes nothing but its lock: every file left is one that was there before.
	for p := range snapshot() {
		if _, ok := before[p]; !ok && p != f.p("gc.lock") && p != f.p("tmp") && p != f.p("") {
			t.Errorf("the collector created %s", p)
		}
	}
	if k, _ := os.ReadFile(filepath.Join(resultCacheDir(), ".key")); string(k) != string(keyBefore) {
		t.Errorf("the result key changed")
	}

	// A cache another user could write is not collected at all (round 8 C1).
	victim := f.locked("consumer/fam/victim", 10, 48*time.Hour)
	if err := os.Chmod(f.root, 0o770); err != nil {
		t.Fatal(err)
	}
	if _, err := collectCache(gcOptions{Max: 0, Grace: time.Nanosecond}, true); err == nil || !strings.Contains(err.Error(), "not private") {
		t.Errorf("collected a non-private cache: %v", err)
	}
	code, _, stderr := runJanus(t, "cache", "gc", "--max", "0")
	if code == 0 || !strings.Contains(stderr, "Stage: cache safety") {
		t.Errorf("janus cache gc on a non-private cache: %d %s", code, stderr)
	}
	if !exists(victim) {
		t.Errorf("an entry of a non-private cache was removed")
	}
	os.Chmod(f.root, 0o700)
}

// TestCacheGCConcurrentHolders: while a collector loops with a zero budget and no grace period,
// processes' worth of goroutines keep taking entries the way janus does (consumer workspace:
// lockEntry; framework build: shared lock; JanusASL: .use) and check that their entry stays
// whole for as long as they hold it.
func TestCacheGCConcurrentHolders(t *testing.T) {
	f := newGCFixture(t)
	var stop atomic.Bool
	var wg, cwg sync.WaitGroup
	var collections, evictions atomic.Int64
	cwg.Add(1)
	go func() {
		defer cwg.Done()
		for !stop.Load() {
			rep, err := collectCache(gcOptions{Max: 0, Grace: time.Nanosecond, All: true}, true)
			if err != nil {
				t.Errorf("collect: %v", err)
				return
			}
			collections.Add(1)
			evictions.Add(int64(len(rep.Evicted)))
		}
	}()
	var failures atomic.Int64
	holder := func(id int, kind string) {
		defer wg.Done()
		for i := 0; i < 60; i++ {
			var dir string
			var release func()
			switch kind {
			case "consumer":
				dir = f.p(fmt.Sprintf("consumer/fam%d/ws", id%2))
				lk, err := lockEntry(dir, dir+".lock")
				if err != nil {
					t.Errorf("lockEntry: %v", err)
					return
				}
				release = lk.unlock
			case "framework":
				dir = f.p("framework/base")
				if err := os.MkdirAll(filepath.Dir(dir), 0o755); err != nil {
					t.Error(err)
					return
				}
				// framework.acquire: shared lock; if the build is missing, upgrade, build,
				// downgrade (not atomic) and check again.
				lk, err := lockFileMode(dir+".lock", true, true)
				if err != nil {
					t.Errorf("lock: %v", err)
					return
				}
				for !exists(filepath.Join(dir, "content", "built")) {
					lk.unlock()
					if lk, err = lockFile(dir+".lock", true); err != nil {
						t.Error(err)
						return
					}
					if !exists(filepath.Join(dir, "content", "built")) {
						os.MkdirAll(filepath.Join(dir, "content"), 0o755)
						os.WriteFile(filepath.Join(dir, "content", "built"), []byte("x"), 0o644)
					}
					if err := lk.share(); err != nil {
						t.Error(err)
						return
					}
				}
				release = lk.unlock
			case "asl":
				dir = f.p("asl/build")
				lk, err := lockEntry(dir, dir+".lock")
				if err != nil {
					t.Errorf("lockEntry: %v", err)
					return
				}
				use, err := lockFileMode(dir+".use", true, true)
				lk.unlock()
				if err != nil {
					t.Errorf("use: %v", err)
					return
				}
				release = use.unlock
			}
			// Holding the entry: (re)build it if it is not there, then use it for a while.
			marker := filepath.Join(dir, "content", "built")
			if kind != "framework" {
				marker = filepath.Join(dir, "content", fmt.Sprintf("m%d", id))
				os.MkdirAll(filepath.Dir(marker), 0o755)
				if err := os.WriteFile(marker, []byte("x"), 0o644); err != nil {
					t.Errorf("%s: write while holding: %v", kind, err)
				}
			}
			touchUse(dir, dir+".lock")
			time.Sleep(time.Duration(1+id%3) * time.Millisecond)
			if !exists(marker) {
				failures.Add(1)
				t.Errorf("%s holder %d: entry removed while held", kind, id)
			}
			release()
			time.Sleep(time.Millisecond)
		}
	}
	for i := 0; i < 4; i++ {
		for _, k := range []string{"consumer", "framework", "asl"} {
			wg.Add(1)
			go holder(i, k)
		}
	}
	wg.Wait()
	stop.Store(true)
	cwg.Wait()
	if collections.Load() < 5 || evictions.Load() < 5 {
		t.Errorf("only %d collections ran, evicting %d entries", collections.Load(), evictions.Load())
	}
	if failures.Load() > 0 {
		t.Fatalf("%d uses lost their entry", failures.Load())
	}
}

// TestCacheCLI: janus cache du / gc output and errors.
func TestCacheCLI(t *testing.T) {
	f := newGCFixture(t)
	ws := f.locked("consumer/fam/ws", 1<<20, 48*time.Hour)
	f.locked("framework/fw", 1<<20, time.Minute, ".ready")
	code, out, stderr := runJanus(t, "cache", "du")
	if code != 0 || !strings.Contains(out, "consumer") || !strings.Contains(out, "Total:") || !strings.Contains(out, "budget") {
		t.Fatalf("cache du: %d\n%s%s", code, out, stderr)
	}
	code, out, stderr = runJanus(t, "cache", "du", "--json")
	var du struct {
		Total int64 `json:"total"`
		Kinds []struct {
			Kind    string `json:"kind"`
			Entries int    `json:"entries"`
		} `json:"kinds"`
	}
	if code != 0 || json.Unmarshal([]byte(out), &du) != nil || du.Total <= 2<<20 || du.Kinds[0].Kind != "consumer" || du.Kinds[0].Entries != 1 {
		t.Fatalf("cache du --json: %d\n%s%s", code, out, stderr)
	}
	code, out, _ = runJanus(t, "cache", "gc", "--max", "0", "--dry-run")
	if code != 0 || !strings.Contains(out, "Would remove 1 entries") || !exists(ws) {
		t.Fatalf("gc --dry-run: %d\n%s", code, out)
	}
	code, out, _ = runJanus(t, "cache", "gc", "--max", "0", "--json")
	var rep gcReport
	if code != 0 || json.Unmarshal([]byte(out), &rep) != nil || len(rep.Evicted) != 1 || rep.Evicted[0].Path != ws || exists(ws) {
		t.Fatalf("gc --max 0 --json: %d\n%s", code, out)
	}
	code, out, _ = runJanus(t, "cache", "gc", "--max", "0", "--grace", "0s")
	if code != 0 || !strings.Contains(out, "Removed 1 entries") {
		t.Fatalf("gc --grace 0s: %d\n%s", code, out)
	}
	for _, bad := range [][]string{{"cache"}, {"cache", "gc", "--max", "lots"}, {"cache", "gc", "--grace", "soon"},
		{"cache", "nope"}, {"cache", "du", "--max", "1G"}, {"cache", "gc", "extra"}} {
		if code, _, stderr := runJanus(t, bad...); code == 0 || !strings.Contains(stderr, "Stage: command line") {
			t.Errorf("%v: %d %s", bad, code, stderr)
		}
	}
	t.Setenv("JANUS_CACHE_MAX", "lots")
	if code, _, stderr := runJanus(t, "cache", "du"); code == 0 || !strings.Contains(stderr, "JANUS_CACHE_MAX") {
		t.Errorf("JANUS_CACHE_MAX=lots: %d %s", code, stderr)
	}
}

// TestAutoCollect: after a command the collector runs (rate-limited), unless JANUS_CACHE_GC=off.
func TestAutoCollect(t *testing.T) {
	f := newGCFixture(t)
	ws := f.locked("consumer/fam/ws", 4096, 30*24*time.Hour) // past retention
	t.Setenv("JANUS_CACHE_GC", "off")
	autoCollect(os.Stderr)
	if !exists(ws) {
		t.Fatalf("JANUS_CACHE_GC=off collected")
	}
	t.Setenv("JANUS_CACHE_GC", "")
	autoCollect(os.Stderr)
	if exists(ws) {
		t.Fatalf("the automatic collection did not run")
	}
	ws2 := f.locked("consumer/fam/ws2", 4096, 30*24*time.Hour)
	autoCollect(os.Stderr) // within a minute of the last one: skipped
	if !exists(ws2) {
		t.Fatalf("the automatic collection ran twice within %v", gcAutoInterval)
	}
	f.age("gc.lock", 2*gcAutoInterval)
	// verify (even a failing one) triggers it.
	runJanus(t, "verify", filepath.Join(t.TempDir(), "missing"))
	if exists(ws2) {
		t.Fatalf("janus verify did not collect")
	}
}

// TestTestCacheOffTmpfs: the test suite's cache is not in RAM by default (round 8 C1 still
// holds for it), and JANUS_TEST_CACHE_DIR overrides it.
func TestTestCacheOffTmpfs(t *testing.T) {
	if d := resolveTestCacheDir("/x/y"); d != "/x/y" {
		t.Errorf("JANUS_TEST_CACHE_DIR ignored: %s", d)
	}
	d := resolveTestCacheDir("")
	if strings.HasPrefix(d, filepath.Clean(os.TempDir())+string(filepath.Separator)) && statFSExisting(os.TempDir()).ram {
		t.Errorf("the default test cache %s is on the RAM filesystem %s", d, os.TempDir())
	}
	if statFSExisting(d).ram {
		t.Errorf("the default test cache %s is on a RAM filesystem", d)
	}
	t.Setenv("JANUS_CACHE_DIR", testCacheDir())
	if err := checkCacheRoot(); err != nil {
		t.Errorf("the test cache fails the round-8 check: %v", err)
	}
}

// TestCacheGCConcurrentVerify: real verifications in separate processes while `janus cache gc
// --max 0 --grace 0s` runs in a loop (every result, trusted-compile and replay entry, and every
// workspace not in use, is removed as soon as it is written). Every verification must succeed;
// afterwards a re-verification from an emptied cache gives the same theorem, statement and
// axioms (the rebuilt entries are equivalent).
func TestCacheGCConcurrentVerify(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	// A private copy of the test cache (seed_test.go): this test empties its cache, which must not
	// disturb the tests and agents sharing the test cache.
	cache := seededCache(t)
	bin := buildJanusBinary(t)
	sb := sandboxArgs()
	arts := map[string]string{}
	for _, n := range []string{"Add", "Max", "Mul64"} {
		arts[n] = mustExtract(t, "example.com/basic."+n)
	}
	verifyArgs := func(n string) []string {
		return append([]string{"verify", arts[n], "--proof", filepath.Join(repoRoot, "examples", "proofs", n+".lean"), "--json"}, sb...)
	}
	env := cacheEnv(cache)
	run1 := func(args ...string) (int, string) {
		cmd := exec.Command(bin, args...)
		cmd.Env = env
		out, err := cmd.CombinedOutput()
		if ee, ok := err.(*exec.ExitError); ok {
			return ee.ExitCode(), string(out)
		}
		if err != nil {
			return 1, err.Error()
		}
		return 0, string(out)
	}
	// Prime the framework build (kept: the collector keeps the current framework's entries).
	if code, out := run1(verifyArgs("Add")...); code != 0 {
		t.Fatalf("priming verify: %s", out)
	}
	first := readReport(t, arts["Add"])

	var stop atomic.Bool
	var gcRuns atomic.Int64
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for !stop.Load() {
			if code, out := run1("cache", "gc", "--max", "0", "--grace", "0s"); code != 0 {
				t.Errorf("cache gc: %s", out)
				return
			}
			gcRuns.Add(1)
			time.Sleep(200 * time.Millisecond)
		}
	}()
	// A consumer package too (its workspace is collected whenever it is not in use).
	pkg := consumerCopy(t, "toml")
	consumerArt := mustExtract(t, "example.com/basic.Add")
	consumerArgs := append([]string{"verify", consumerArt, "--proof", filepath.Join(pkg, "ConsumerExample/Add.lean"), "--proof-root", pkg,
		"--theorem", "ConsumerExample.Add.correctness", "--json"}, sb...)
	var procs []*janusProc
	for i, n := range []string{"Add", "Max", "Mul64", "Add", "Max", "Add"} {
		procs = append(procs, &janusProc{name: fmt.Sprintf("verify#%d %s", i, n), args: verifyArgs(n), wait: time.Duration(i) * 700 * time.Millisecond})
	}
	procs = append(procs, &janusProc{name: "consumer verify", args: consumerArgs, wait: time.Second})
	runConcurrently(bin, env, procs)
	stop.Store(true)
	wg.Wait()
	for _, p := range procs {
		if p.code != 0 || !strings.Contains(p.out, `"theorem"`) {
			t.Errorf("%s failed under the collector (exit %d):\n%s", p.name, p.code, p.out)
		}
	}
	if gcRuns.Load() < 3 {
		t.Errorf("only %d collections ran during the verifications", gcRuns.Load())
	}

	// Empty everything but the framework build, then verify again: same theorem.
	if code, out := run1("cache", "gc", "--max", "0", "--grace", "0s"); code != 0 {
		t.Fatalf("cache gc: %s", out)
	}
	if code, out := run1(verifyArgs("Add")...); code != 0 {
		t.Fatalf("verify from an emptied cache: %s", out)
	}
	if code, out := run1(consumerArgs...); code != 0 {
		t.Fatalf("consumer verify from an emptied cache: %s", out)
	}
	if r := readReport(t, consumerArt); r.Theorem != "ConsumerExample.Add.correctness" || r.KernelReplay.Status != "passed" {
		t.Errorf("consumer re-verification: %+v", r)
	}
	again := readReport(t, arts["Add"])
	if again.Cached {
		t.Errorf("the result entry survived the collection")
	}
	if again.Theorem != first.Theorem || again.Statement != first.Statement || fmt.Sprint(again.Axioms) != fmt.Sprint(first.Axioms) ||
		again.ExtractedSha256 != first.ExtractedSha256 || again.KernelReplay.Status != "passed" {
		t.Errorf("the re-verification differs:\nfirst %+v\nagain %+v", first, again)
	}
}

// TestArtifactsLib runs the self-test of scripts/lib/artifacts.sh, the pruning of oracle dumps
// shared by the oracle drivers (needs bash and zstd).
func TestArtifactsLib(t *testing.T) {
	if _, err := exec.LookPath("zstd"); err != nil {
		t.Skip("zstd not installed")
	}
	cmd := exec.Command("bash", filepath.Join(repoRoot, "scripts", "lib", "test-artifacts.sh"))
	cmd.Env = append(os.Environ(), "KEEP=")
	if out, err := cmd.CombinedOutput(); err != nil || !strings.Contains(string(out), "all checks passed") {
		t.Fatalf("scripts/lib/test-artifacts.sh: %v\n%s", err, out)
	}
}

// TestTheoremsLib runs the self-test of scripts/lib/theorems.sh (the example scripts' verify of
// several theorems of one proof at once): concurrent items do not share copies, and a second run
// on the same extraction in the same tree fails loudly instead of racing the first.
func TestTheoremsLib(t *testing.T) {
	if _, err := exec.LookPath("flock"); err != nil {
		t.Skip("flock not installed")
	}
	cmd := exec.Command("bash", filepath.Join(repoRoot, "scripts", "lib", "test-theorems.sh"))
	cmd.Env = append(os.Environ(), "TMPDIR="+t.TempDir())
	if out, err := cmd.CombinedOutput(); err != nil || !strings.Contains(string(out), "all checks passed") {
		t.Fatalf("scripts/lib/test-theorems.sh: %v\n%s", err, out)
	}
}

// TestItemTimeoutLib runs the self-test of scripts/lib/itemtimeout.sh (jv, the per-item wall-clock
// limit of the verify-* scripts): a hung `janus verify` is killed, fails with status 124 and
// prints TIMEOUT, and the other theorems of the example are not affected.
func TestItemTimeoutLib(t *testing.T) {
	if _, err := exec.LookPath("flock"); err != nil {
		t.Skip("flock not installed")
	}
	cmd := exec.Command("bash", filepath.Join(repoRoot, "scripts", "lib", "test-itemtimeout.sh"))
	cmd.Env = append(os.Environ(), "TMPDIR="+t.TempDir())
	if out, err := cmd.CombinedOutput(); err != nil || !strings.Contains(string(out), "all checks passed") {
		t.Fatalf("scripts/lib/test-itemtimeout.sh: %v\n%s", err, out)
	}
}

// TestPoolLib and TestSpeedcheckLib run the self-tests of the gate's work queue (scripts/lib/pool.sh:
// longest first, streamed PASS/FAIL/TIMEOUT lines, failure and missing results fail the pool, needs)
// and of the speed-regression check (scripts/gate-speedcheck.py).
func TestPoolLib(t *testing.T) { runLibSelfTest(t, "test-pool.sh") }

func TestSpeedcheckLib(t *testing.T) { runLibSelfTest(t, "test-speedcheck.sh") }

// TestGateCancelLib: the gate cancels through its own process group only (two runs, one cancelled).
func TestGateCancelLib(t *testing.T) { runLibSelfTest(t, "test-pgcancel.sh") }

func runLibSelfTest(t *testing.T, name string) {
	t.Helper()
	cmd := exec.Command("bash", filepath.Join(repoRoot, "scripts", "lib", name))
	// never the running gate's out dir or timeline (the gotest lane runs inside a gate that exports them)
	var env []string
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "POOL_") && !strings.HasPrefix(e, "JANUS_POOL_DIR=") && !strings.HasPrefix(e, "JANUS_GATE_") && !strings.HasPrefix(e, "JANUS_VERIFY_MEM_BUDGET_GIB=") {
			env = append(env, e)
		}
	}
	cmd.Env = append(env, "TMPDIR="+t.TempDir())
	if out, err := cmd.CombinedOutput(); err != nil || !strings.Contains(string(out), "all checks passed") {
		t.Fatalf("scripts/lib/%s: %v\n%s", name, err, out)
	}
}

// TestPoolMemLib: per-item memory admission of the work queue (heavy items limit themselves, small ones run wide).
func TestPoolMemLib(t *testing.T) { runLibSelfTest(t, "test-poolmem.sh") }

// TestSelfTestIsolation: the queue self-tests ignore an inherited gate timeline / pool dir (nothing leaks into a running gate).
func TestSelfTestIsolation(t *testing.T) { runLibSelfTest(t, "test-isolation.sh") }

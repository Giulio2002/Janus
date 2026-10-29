package main

import (
	"bytes"
	"crypto/rand"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Seeding a cache with another cache's framework build (docs/TESTING.md "Go tests"): a test that
// needs a cache of its own (it empties the cache, or damages or rebuilds the framework build)
// starts from a copy of the test cache's ready build instead of building the framework again, and
// the test cache itself starts from the user's cache when that has a ready build of the same
// framework. The copy is accepted only if framework.ready holds for it: the sources are
// byte-identical to the embedded framework, and every framework module-data file and the compiled
// auditor hash as the build's stamp records. The framework replay verdict of those bytes is
// carried over only if it is authentic in the source cache (its HMAC verifies under the source's
// key); it is then recorded under the destination's own key, exactly as the destination would
// record it after replaying the same bytes itself.

// seedFramework copies the ready build of the embedded framework from cache src into cache dst,
// unless dst already has a ready one or src has none (src is only read, under its shared lock).
// It reports whether dst has a ready build afterwards that came from src. Env-free (both caches
// are named explicitly).
func seedFramework(src, dst string) (bool, error) {
	fw, err := loadFramework("")
	if err != nil {
		return false, err
	}
	lake, err := findLake()
	if err != nil {
		return false, err
	}
	key := fw.Sha256[:24]
	srcDir := filepath.Join(src, "v1", "framework", key)
	dstDir := filepath.Join(dst, "v1", "framework", key)
	if fw.ready(dstDir, nil) {
		return false, nil
	}
	srcLock, srcStamp := fw.buildPaths(srcDir)
	if _, err := os.Stat(srcStamp); err != nil {
		return false, nil
	}
	slk, err := lockFileMode(srcLock, true, true)
	if err != nil {
		return false, err
	}
	defer slk.unlock()
	if !fw.ready(srcDir, nil) {
		return false, nil
	}
	dstLock, dstStamp := fw.buildPaths(dstDir)
	if err := os.MkdirAll(filepath.Dir(dstDir), 0o755); err != nil {
		return false, err
	}
	dlk, err := lockFileMode(dstLock, false, true)
	if err != nil {
		return false, err
	}
	defer dlk.unlock()
	if fw.ready(dstDir, nil) {
		return false, nil
	}
	tmp, err := os.MkdirTemp(filepath.Dir(dstDir), ".seed-")
	if err != nil {
		return false, err
	}
	defer os.RemoveAll(tmp)
	if err := copyTree(srcDir, filepath.Join(tmp, "b")); err != nil {
		return false, err
	}
	stamp, err := os.ReadFile(srcStamp)
	if err != nil {
		return false, err
	}
	_ = os.Remove(dstStamp)
	_ = os.RemoveAll(dstDir)
	if err := os.Rename(filepath.Join(tmp, "b"), dstDir); err != nil {
		return false, err
	}
	if err := writeFileAtomic(dstStamp, stamp); err != nil {
		return false, err
	}
	// The hash check: the copy must be exactly the stamped build.
	if !fw.ready(dstDir, nil) {
		_ = os.Remove(dstStamp)
		return false, fmt.Errorf("the copy of %s does not match its stamp", srcDir)
	}
	// The framework replay verdict of these bytes, if src has an authentic one.
	tc, err := findToolchain(lake, dstDir)
	if err != nil {
		return true, nil
	}
	fwPins, err := frameworkPins(filepath.Join(dstDir, ".lake", "build", "lib", "lean"), fw.Files)
	if err != nil {
		return true, nil
	}
	carryVerdict(src, dst, frameworkVerdictKey(tc.cacheID(), fwPins), len(frameworkModules(fwPins)))
	return true, nil
}

// seedCheckoutVerdict carries into cache dst the framework replay verdict of THIS CHECKOUT's own build
// (.lake/build, what `--janus-root <checkout>` verifications use; its module-data bytes, hence its
// pins and verdict key, are not the embedded build's) when cache src has an authentic one (a sandboxed
// `janus verify --janus-root` replayed it there). Without one, the first test that verifies with the
// checkout replays it, as before. Reports whether a verdict was carried.
func seedCheckoutVerdict(src, dst string) bool {
	fw, err := loadFramework(repoRoot)
	if err != nil {
		return false
	}
	lake, err := findLake()
	if err != nil {
		return false
	}
	lib := filepath.Join(repoRoot, ".lake", "build", "lib", "lean")
	tc, err := findToolchain(lake, repoRoot)
	if err != nil {
		return false
	}
	pins, err := frameworkPins(lib, fw.Files)
	if err != nil || len(pins.want) == 0 {
		return false
	}
	k := frameworkVerdictKey(tc.cacheID(), pins)
	carryVerdict(src, dst, k, len(frameworkModules(pins)))
	return fileExists(filepath.Join(dst, "v1", "replay", "framework", k[:2], k))
}

// carryVerdict records in cache dst the framework replay verdict k if cache src has an authentic
// one (its MAC verifies under src's key), under dst's key (created like resultHMACKey does if dst
// has none). Env-free: it names both caches explicitly, so parallel tests can use it.
func carryVerdict(src, dst, k string, nmods int) {
	rel := filepath.Join("v1", "replay", "framework", k[:2], k)
	srcKey, err := readPrivateFile(filepath.Join(src, "v1", "result", ".key"), true)
	if err != nil || len(srcKey) != 32 {
		return
	}
	b, err := readPrivateFile(filepath.Join(src, rel), false)
	if err != nil {
		return
	}
	line, _, _ := bytes.Cut(b, []byte("\n"))
	if string(line) != markerHeader+markerMAC(srcKey, "framework", k) {
		return
	}
	keyPath := filepath.Join(dst, "v1", "result", ".key")
	dstKey, err := readPrivateFile(keyPath, true)
	if err != nil {
		if os.MkdirAll(filepath.Dir(keyPath), 0o700) != nil {
			return
		}
		dstKey = make([]byte, 32)
		if _, err := rand.Read(dstKey); err != nil || os.WriteFile(keyPath, dstKey, 0o600) != nil {
			return
		}
	}
	if len(dstKey) != 32 || os.MkdirAll(filepath.Dir(filepath.Join(dst, rel)), 0o755) != nil {
		return
	}
	_ = writeFileAtomic(filepath.Join(dst, rel), []byte(fmt.Sprintf("%s%s\nleanchecker Janus passed: %d framework modules (seeded)\n",
		markerHeader, markerMAC(dstKey, "framework", k), nmods)))
}

// seededCache is a new private cache (not selected as JANUS_CACHE_DIR: parallel tests pass it to
// their janus processes) holding a copy of the test cache's framework build, built there first if
// needed, and its replay verdict.
func seededCache(t *testing.T) string {
	t.Helper()
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	lake, err := findLake()
	if err != nil {
		t.Skip("lake not installed")
	}
	if cacheRoot() != testCacheDir() {
		t.Fatal("seededCache: JANUS_CACHE_DIR is not the test cache")
	}
	lease, err := fw.frameworkBase(lake, nil)
	if err != nil {
		t.Fatalf("building the test cache's framework: %v", err)
	}
	lease.release()
	// On disk next to the test cache (a framework build is ~400 MB; t.TempDir is often a RAM
	// /tmp). v1/tmp trees are also collected by age if a killed test leaves one behind.
	parent := filepath.Join(testCacheDir(), "v1", "tmp")
	if err := os.MkdirAll(parent, 0o755); err != nil {
		t.Fatal(err)
	}
	c, err := os.MkdirTemp(parent, "seeded-")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { os.RemoveAll(c) })
	if err := os.Chmod(c, 0o700); err != nil {
		t.Fatal(err)
	}
	if ok, err := seedFramework(testCacheDir(), c); err != nil || !ok {
		t.Fatalf("seeding %s from the test cache: %v (seeded %v)", c, err, ok)
	}
	// and the replay verdict of this checkout's own build (for tests that verify with --janus-root)
	seedCheckoutVerdict(testCacheDir(), c)
	return c
}

// cacheEnv is the environment of janus subprocesses that use cache c (and no JANUS_ROOT).
func cacheEnv(c string) []string {
	var env []string
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "JANUS_ROOT=") && !strings.HasPrefix(e, "JANUS_CACHE_DIR=") {
			env = append(env, e)
		}
	}
	return append(env, "JANUS_CACHE_DIR="+c)
}

// TestSeedFramework: a seeded copy is used only when it is exactly the stamped build; the source
// cache is not written; a verdict is carried over only when authentic in the source.
func TestSeedFramework(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	c := seededCache(t)
	fw, _ := loadFramework("")
	dir := filepath.Join(c, "v1", "framework", fw.Sha256[:24])
	if !fw.ready(dir, nil) {
		t.Fatal("the seeded build is not ready")
	}
	// A damaged copy is refused: a module that differs from the stamp fails the hash check.
	mk := func() string {
		d, err := os.MkdirTemp(filepath.Dir(c), "seeded-")
		if err != nil {
			t.Fatal(err)
		}
		t.Cleanup(func() { os.RemoveAll(d) })
		return d
	}
	d2 := mk()
	if ok, err := seedFramework(c, d2); !ok || err != nil {
		t.Fatalf("seeding from a seeded cache: %v %v", ok, err)
	}
	olean := filepath.Join(d2, "v1", "framework", fw.Sha256[:24], ".lake", "build", "lib", "lean", "Janus", "GoABI.olean")
	f, err := os.OpenFile(olean, os.O_APPEND|os.O_WRONLY, 0)
	if err != nil {
		t.Fatal(err)
	}
	f.WriteString("forged")
	f.Close()
	if fw.ready(filepath.Join(d2, "v1", "framework", fw.Sha256[:24]), nil) {
		t.Fatal("a damaged copy passes framework.ready")
	}
	if ok, err := seedFramework(d2, mk()); ok || err != nil {
		t.Fatalf("seeded from a damaged build: %v %v", ok, err)
	}
	// A verdict is carried only if authentic in the source: a planted one is not.
	k := strings.Repeat("ab", 32)
	writeBytes(t, filepath.Join(c, "v1", "replay", "framework", k[:2], k), []byte(markerHeader+strings.Repeat("0", 64)+"\n"))
	d4 := mk()
	carryVerdict(c, d4, k, 1)
	if fileExists(filepath.Join(d4, "v1", "replay", "framework", k[:2], k)) {
		t.Error("a planted verdict was carried over")
	}
}

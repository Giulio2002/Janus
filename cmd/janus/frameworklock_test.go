package main

import (
	"os"
	"path/filepath"
	"testing"
)

// The lock and the ready stamp of a framework build belong to the DIRECTORY that holds it. A directory framework (--janus-root, the
// checkout) keeps them in its own .lake; the cached base of the same framework sources is leased by consumer workspaces,
// verify-batch and the ASL build (frameworkBase) also when the framework is a directory one, and must then use the cache's
// sibling <key>.lock / <key>.ready, the files every embedded-framework verification uses. With two different lock files the
// checkout-mode run rebuilt and re-stamped the cached base (dropping its Janus.Tools.Decode output) under the shared lease of
// a running verification (nightly a29b0783: "changed after the proof compile, missing Janus/Tools/Decode.olean").
func TestFrameworkBuildPathsFollowTheDirectory(t *testing.T) {
	root := t.TempDir()
	checkout := filepath.Join(root, "checkout")
	base := filepath.Join(root, "cache", "v1", "framework", "abcdef")
	dirFw := &framework{Source: "directory", Dir: checkout}
	embFw := &framework{Source: "embedded"}

	l, s := dirFw.buildPaths(checkout)
	if l != filepath.Join(checkout, ".lake", "janus-framework.lock") || s != filepath.Join(checkout, ".lake", "janus-framework.ready") {
		t.Errorf("a directory framework's own build: %s %s", l, s)
	}
	dl, ds := dirFw.buildPaths(base)
	el, es := embFw.buildPaths(base)
	if dl != base+".lock" || ds != base+".ready" {
		t.Errorf("the cached base leased by a directory framework uses %s %s, not the cache's sibling lock and stamp", dl, ds)
	}
	if dl != el || ds != es {
		t.Errorf("a directory and an embedded framework disagree on the cached base's lock/stamp: %s %s vs %s %s", dl, ds, el, es)
	}
	// and the two really exclude each other: a shared lease through one is a conflict for a writer through the other
	if err := os.MkdirAll(filepath.Dir(el), 0o755); err != nil {
		t.Fatal(err)
	}
	lk, err := lockFileMode(el, true, true)
	if err != nil {
		t.Fatal(err)
	}
	defer lk.unlock()
	if w, err := lockFileMode(dl, false, false); err == nil {
		w.unlock()
		t.Error("an exclusive (writer) lock through the directory framework's path was granted while a shared lease was held through the embedded one")
	}
}

// The same through the real lease: a directory framework (--janus-root repoRoot) that leases the cached base (consumer workspaces,
// verify-batch, the ASL build) builds and stamps it under the CACHE's lock and stamp. It must leave no second lock/stamp inside the
// base (.lake/janus-framework.*), and a second lease must not drop the decoder module the first one built (a checkout-mode stamp
// without Janus.Tools.Decode made the next run delete it under other runs' shared leases).
func TestDirectoryFrameworkLeaseOfTheCacheBase(t *testing.T) {
	needLeanSlow(t)
	c := seededCache(t)
	t.Setenv("JANUS_CACHE_DIR", c)
	dfw, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	efw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	if dfw.Sha256 != efw.Sha256 {
		t.Skip("the checkout's framework sources differ from the embedded ones: they do not share a cached base")
	}
	lake, err := findLake()
	if err != nil {
		t.Skip("lake not installed")
	}
	base := embeddedBase(t, c)
	for i, targets := range [][]string{{"janus-decode"}, nil, {"janus-decode"}} {
		lease, err := dfw.frameworkBase(lake, nil, targets...)
		if err != nil {
			t.Fatalf("lease %d: %v", i, err)
		}
		lease.release()
		for _, p := range []string{filepath.Join(base, ".lake", "janus-framework.ready"), filepath.Join(base, ".lake", "janus-framework.lock")} {
			if _, err := os.Stat(p); err == nil {
				t.Fatalf("lease %d: the cached base got a checkout-mode lock/stamp of its own: %s", i, p)
			}
		}
		if _, err := os.Stat(filepath.Join(base, ".lake", "build", "lib", "lean", "Janus", "Tools", "Decode.olean")); err != nil {
			t.Fatalf("lease %d: Janus.Tools.Decode.olean is gone from the cached base: %v", i, err)
		}
	}
	if _, err := os.Stat(base + ".ready"); err != nil {
		t.Fatalf("no cache stamp for the base: %v", err)
	}
}

package main

// J1c: the gate-private framework verdict store.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func newVerdictDir(t *testing.T) string {
	t.Helper()
	d := filepath.Join(t.TempDir(), "verdicts")
	if err := os.Mkdir(d, 0o700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_VERDICT_CACHE", d)
	return d
}

// A verdict is found for exactly the framework build and toolchain it was recorded for: a build
// with one changed module, an added module, a removed one, or another toolchain misses.
func TestJ1cVerdictStoreKeyedByPinsAndToolchain(t *testing.T) {
	newVerdictDir(t)
	vs, ok, err := externalVerdictStore(map[string]string{"fresh": "true"})
	if err != nil || !ok {
		t.Fatalf("store: %v %v", ok, err)
	}
	fw := &pinnedLib{who: "fw", want: pins{"Janus.olean": "aa", "Janus/A.olean": "bb"}}
	k := frameworkVerdictKey("tc1", fw)
	if vs.has(k) {
		t.Fatal("a verdict before any was recorded")
	}
	vs.record(k, fw)
	if !vs.has(k) {
		t.Fatal("the recorded verdict was not found")
	}
	for name, other := range map[string]string{
		"a module changed (a tampered olean)": frameworkVerdictKey("tc1", &pinnedLib{want: pins{"Janus.olean": "aa", "Janus/A.olean": "bX"}}),
		"a module added":                      frameworkVerdictKey("tc1", &pinnedLib{want: pins{"Janus.olean": "aa", "Janus/A.olean": "bb", "Janus/B.olean": "cc"}}),
		"a module removed":                    frameworkVerdictKey("tc1", &pinnedLib{want: pins{"Janus.olean": "aa"}}),
		"another toolchain":                   frameworkVerdictKey("tc2", fw),
	} {
		if other == k || vs.has(other) {
			t.Errorf("%s: the cached pass answered for other bytes", name)
		}
	}
}

// A marker that was not written under the store's key (planted, or from another store) is a miss,
// and the default replay cache is not the store.
func TestJ1cVerdictStoreAuthentic(t *testing.T) {
	d := newVerdictDir(t)
	privateCache(t)
	vs, _, _ := externalVerdictStore(map[string]string{"fresh": "true"})
	fw := &pinnedLib{want: pins{"Janus.olean": "aa"}}
	k := frameworkVerdictKey("tc", fw)
	vs.record(k, fw)
	good, _ := os.ReadFile(vs.path(k))
	// a verdict made under another store's key
	other := filepath.Join(t.TempDir(), "other")
	os.Mkdir(other, 0o700)
	t.Setenv("JANUS_VERDICT_CACHE", other)
	vs2, _, _ := externalVerdictStore(map[string]string{"fresh": "true"})
	writeBytes(t, vs2.path(k), good)
	if vs2.has(k) {
		t.Error("a marker from another store's key was accepted")
	}
	for name, body := range map[string]string{"empty": "", "no MAC": markerHeader + "\n", "bad MAC": markerHeader + strings.Repeat("0", 64) + "\n"} {
		writeBytes(t, vs2.path(k), []byte(body))
		if vs2.has(k) {
			t.Errorf("%s: planted marker accepted", name)
		}
	}
	// the cache root's own replay cache never answers for the store, nor the store for it
	if hasFrameworkVerdict(k) {
		t.Error("the default store holds the verdict")
	}
	_ = d
}

// An unsafe store directory is refused (not silently replaced by "no store"), --fresh-framework
// ignores the store, and an unset variable means no store.
func TestJ1cVerdictStoreSafety(t *testing.T) {
	t.Setenv("JANUS_VERDICT_CACHE", "")
	if _, ok, err := externalVerdictStore(nil); ok || err != nil {
		t.Fatalf("unset: %v %v", ok, err)
	}
	d := newVerdictDir(t)
	if _, ok, _ := externalVerdictStore(map[string]string{"fresh-framework": "true"}); ok {
		t.Error("--fresh-framework used the store")
	}
	if err := os.Chmod(d, 0o755); err != nil {
		t.Fatal(err)
	}
	if _, ok, err := externalVerdictStore(nil); ok || err == nil {
		t.Errorf("a world-readable store was accepted: %v %v", ok, err)
	}
	os.Chmod(d, 0o700)
	t.Setenv("JANUS_VERDICT_CACHE", "relative/dir")
	if _, ok, err := externalVerdictStore(nil); ok || err == nil {
		t.Error("a relative store path was accepted")
	}
	link := filepath.Join(t.TempDir(), "link")
	if err := os.Symlink(d, link); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_VERDICT_CACHE", link)
	if _, ok, err := externalVerdictStore(nil); ok || err == nil {
		t.Error("a store that is a link was accepted")
	}
}

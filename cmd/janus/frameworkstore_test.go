package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// fakeBuild writes a small stand-in for <dir>/.lake/build.
func fakeBuild(t *testing.T, dir string) {
	t.Helper()
	for p, b := range map[string]string{
		"lib/lean/Janus.olean":       "olean-bytes",
		"lib/lean/Janus/GoABI.olean": "goabi-bytes",
		"lib/lean/Janus/GoABI.ilean": "ilean",
		"bin/janus-audit":            "exe",
	} {
		writeFile(t, filepath.Join(dir, ".lake", "build", p), b)
	}
}

func newTestStore(t *testing.T) *frameworkStore {
	t.Helper()
	d := filepath.Join(t.TempDir(), "store")
	t.Setenv("JANUS_FRAMEWORK_STORE", d)
	s, err := externalFrameworkStore()
	if err != nil || s == nil {
		t.Fatalf("store: %v", err)
	}
	return s
}

func TestFrameworkStoreRoundTripAndTamper(t *testing.T) {
	s := newTestStore(t)
	src := t.TempDir()
	fakeBuild(t, src)
	key := strings.Repeat("ab", 32)
	s.publish(key, src)

	// an authentic entry restores byte for byte
	dst := t.TempDir()
	if !s.restore(key, dst) {
		t.Fatal("an authentic entry was not restored")
	}
	for _, p := range []string{"lib/lean/Janus.olean", "lib/lean/Janus/GoABI.olean", "bin/janus-audit"} {
		a, _ := os.ReadFile(filepath.Join(src, ".lake", "build", p))
		b, _ := os.ReadFile(filepath.Join(dst, ".lake", "build", p))
		if string(a) != string(b) || len(a) == 0 {
			t.Errorf("%s differs after the restore", p)
		}
	}
	// another key is a miss
	if s.restore(strings.Repeat("cd", 32), t.TempDir()) {
		t.Error("an unknown key was restored")
	}
	// a stored file with one byte changed: not restored, nothing left behind
	stored := filepath.Join(s.dir, "fw", key, "build", "lib", "lean", "Janus", "GoABI.olean")
	orig, _ := os.ReadFile(stored)
	writeFile(t, stored, string(orig)+"x")
	d2 := t.TempDir()
	if s.restore(key, d2) {
		t.Error("a tampered stored file was restored")
	}
	if _, err := os.Stat(filepath.Join(d2, ".lake", "build")); err == nil {
		t.Error("a refused restore left a build behind")
	}
	writeFile(t, stored, string(orig))
	if !s.restore(key, t.TempDir()) {
		t.Fatal("the repaired entry was not restored")
	}
	// an extra file in the stored build, a forged manifest (right hashes, wrong MAC)
	writeFile(t, filepath.Join(s.dir, "fw", key, "build", "extra"), "e")
	if s.restore(key, t.TempDir()) {
		t.Error("an entry with an extra file was restored")
	}
	_ = os.Remove(filepath.Join(s.dir, "fw", key, "build", "extra"))
	ep := filepath.Join(s.dir, "fw", key, "entry.json")
	eb, _ := os.ReadFile(ep)
	writeFile(t, ep, strings.Replace(string(eb), `"mac":"`, `"mac":"00`, 1))
	if s.restore(key, t.TempDir()) {
		t.Error("an entry with a wrong MAC was restored")
	}
	// an entry under another store key (a store copied from elsewhere) is refused
	writeFile(t, ep, string(eb))
	os.Remove(filepath.Join(s.dir, "key", ".key"))
	if s.restore(key, t.TempDir()) {
		t.Error("an entry made under another store key was restored")
	}
}

func TestFrameworkStoreRefusesNonRegularFiles(t *testing.T) {
	s := newTestStore(t)
	src := t.TempDir()
	fakeBuild(t, src)
	if err := os.Symlink("/etc/passwd", filepath.Join(src, ".lake", "build", "lib", "lean", "Link.olean")); err != nil {
		t.Skip(err)
	}
	key := strings.Repeat("ef", 32)
	s.publish(key, src)
	if _, err := os.Stat(filepath.Join(s.dir, "fw", key, "entry.json")); err == nil {
		t.Error("a build holding a symbolic link was published")
	}
}

func TestFrameworkStoreDirectoryMustBePrivate(t *testing.T) {
	d := filepath.Join(t.TempDir(), "s")
	if err := os.MkdirAll(d, 0o755); err != nil {
		t.Fatal(err)
	}
	os.Chmod(d, 0o755)
	t.Setenv("JANUS_FRAMEWORK_STORE", d)
	if s, err := externalFrameworkStore(); err == nil || s != nil {
		t.Error("a world-readable store directory was accepted")
	}
	t.Setenv("JANUS_FRAMEWORK_STORE", "relative/dir")
	if s, err := externalFrameworkStore(); err == nil || s != nil {
		t.Error("a relative store path was accepted")
	}
	t.Setenv("JANUS_FRAMEWORK_STORE", "off")
	if s, err := externalFrameworkStore(); err != nil || s != nil {
		t.Error("off must disable the store")
	}
}

// A different source byte, lake manifest, toolchain or janus is a different key: a miss, and a full compile.
func TestFrameworkStoreKeyCoversEveryInput(t *testing.T) {
	needLean(t)
	lake, err := findLake()
	if err != nil {
		t.Skip(err)
	}
	tc := findToolchainDirect(lake, repoRoot)
	if tc == nil {
		t.Skip("no direct toolchain lookup on this host")
	}
	files := map[string][]byte{"Janus/GoABI.lean": []byte("def x := 1\n"), "lake-manifest.json": []byte("{}"), "lakefile.toml": []byte("name = \"janus\"\n")}
	mk := func(f map[string][]byte) *framework {
		return &framework{Source: "embedded", Files: f, Sha256: frameworkSha(f)}
	}
	base := frameworkStoreKey(mk(files), tc)
	if base != frameworkStoreKey(mk(files), tc) {
		t.Fatal("the key is not deterministic")
	}
	tamper := map[string][]byte{}
	for k, v := range files {
		tamper[k] = v
	}
	tamper["Janus/GoABI.lean"] = []byte("def x := 2\n")
	if frameworkStoreKey(mk(tamper), tc) == base {
		t.Error("a changed source byte kept the key")
	}
	tamper["Janus/GoABI.lean"] = files["Janus/GoABI.lean"]
	tamper["lake-manifest.json"] = []byte("{ }")
	if frameworkStoreKey(mk(tamper), tc) == base {
		t.Error("a changed lake manifest kept the key")
	}
	tc3 := &toolchain{lean: tc.lean, leanchecker: tc.leanchecker, sysroot: tc.sysroot, libDir: tc.libDir, version: tc.version + "-other"}
	if frameworkStoreKey(mk(files), tc3) == base {
		t.Error("another toolchain version kept the key")
	}
}

func TestFrameworkStoreKeepsThreeEntries(t *testing.T) {
	s := newTestStore(t)
	src := t.TempDir()
	fakeBuild(t, src)
	var keys []string
	for i := 0; i < 5; i++ {
		k := strings.Repeat(string(rune('a'+i)), 64)
		keys = append(keys, k)
		s.publish(k, src)
		old := time.Now().Add(time.Duration(i-10) * time.Hour)
		os.Chtimes(filepath.Join(s.dir, "fw", k), old, old)
	}
	// the newest published key is always kept; of the others the three-entry budget keeps the most recent
	n := 0
	for _, k := range keys {
		if _, err := os.Stat(filepath.Join(s.dir, "fw", k, "entry.json")); err == nil {
			n++
		}
	}
	if n > 3 {
		t.Errorf("%d entries kept, want at most 3", n)
	}
	if _, err := os.Stat(filepath.Join(s.dir, "fw", keys[4], "entry.json")); err != nil {
		t.Error("the entry just published was pruned")
	}
}

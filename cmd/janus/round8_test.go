package main

// Round 8 unit rows (docs/AUDIT-ROUND8.md): L1 (the toolchain's cache identity covers its
// library), M1 (trusted-compile manifests are authenticated) and C1 (the cache root is private).

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// fakeToolchain lays out a toolchain prefix (bin/lean, bin/leanchecker, lib/lean/...) in a new
// temporary directory.
func fakeToolchain(t *testing.T) *toolchain {
	t.Helper()
	pfx := t.TempDir()
	for rel, data := range map[string]string{
		"bin/lean":                     "#!launcher",
		"bin/leanchecker":              "#!checker",
		"lib/lean/libleanshared.so":    "kernel-and-elaborator-v1",
		"lib/lean/Init/Prelude.olean":  "prelude",
		"lib/lean/Lean/Elab/Cmd.olean": "elab",
	} {
		writeBytes(t, filepath.Join(pfx, rel), []byte(data))
	}
	return newFakeTC(pfx)
}

func newFakeTC(pfx string) *toolchain {
	return &toolchain{lean: filepath.Join(pfx, "bin", "lean"), leanchecker: filepath.Join(pfx, "bin", "leanchecker"),
		sysroot: pfx, libDir: filepath.Join(pfx, "lib", "lean"), version: "Lean (version 4.34.1, test)", hasChecker: true}
}

// rewriteSameMeta overwrites p in place with data of the same length and restores its
// modification time: only the change time (and the content) differ.
func rewriteSameMeta(t *testing.T, p string, data []byte) {
	t.Helper()
	fi, err := os.Stat(p)
	if err != nil {
		t.Fatal(err)
	}
	if int64(len(data)) != fi.Size() {
		t.Fatalf("test data must keep the size of %s", p)
	}
	time.Sleep(10 * time.Millisecond) // a distinct change time even on coarse clocks
	f, err := os.OpenFile(p, os.O_WRONLY, 0)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := f.WriteAt(data, 0); err != nil {
		t.Fatal(err)
	}
	f.Close()
	if err := os.Chtimes(p, fi.ModTime(), fi.ModTime()); err != nil {
		t.Fatal(err)
	}
}

// L1: the cache identity, and so every key built from it, changes when a library file changes
// under the same version string and the same lean/leanchecker binaries.
func TestRound8ToolchainCacheID(t *testing.T) {
	tc := fakeToolchain(t)
	fw := &pinnedLib{want: pins{"Janus.olean": "00"}}
	id0 := tc.cacheID()
	key0 := trustedCacheKey(tc, fw, []byte("x"), []byte("y"))
	if !strings.HasPrefix(id0, tc.version+" ") {
		t.Fatalf("cache ID %q does not start with the version", id0)
	}
	if again := newFakeTC(tc.sysroot); again.cacheID() != id0 || trustedCacheKey(again, fw, []byte("x"), []byte("y")) != key0 {
		t.Fatal("cache ID not deterministic")
	}
	cases := []struct {
		name   string
		change func(pfx string)
	}{
		{"libleanshared.so rewritten in place, mtime restored", func(pfx string) {
			rewriteSameMeta(t, filepath.Join(pfx, "lib/lean/libleanshared.so"), []byte("kernel-and-elaborator-v2"))
		}},
		{"core .olean replaced (new inode)", func(pfx string) {
			p := filepath.Join(pfx, "lib/lean/Init/Prelude.olean")
			writeBytes(t, p+".new", []byte("PRELUDE"))
			if err := os.Rename(p+".new", p); err != nil {
				t.Fatal(err)
			}
		}},
		{"library file added", func(pfx string) {
			writeBytes(t, filepath.Join(pfx, "lib/lean/Extra.olean"), []byte("extra"))
		}},
		{"bin/ tool changed", func(pfx string) {
			writeBytes(t, filepath.Join(pfx, "bin/leanc"), []byte("cc"))
		}},
		{"library file made a symbolic link", func(pfx string) {
			p := filepath.Join(pfx, "lib/lean/Lean/Elab/Cmd.olean")
			writeBytes(t, p+".real", []byte("elab"))
			os.Remove(p)
			if err := os.Symlink("Cmd.olean.real", p); err != nil {
				t.Fatal(err)
			}
		}},
	}
	seen := map[string]string{id0: "original"}
	for _, c := range cases {
		c.change(tc.sysroot)
		fresh := newFakeTC(tc.sysroot)
		id := fresh.cacheID()
		if prev, dup := seen[id]; dup {
			t.Errorf("%s: cache ID unchanged (same as after %q)", c.name, prev)
		}
		if trustedCacheKey(fresh, fw, []byte("x"), []byte("y")) == key0 {
			t.Errorf("%s: trusted-compile key unchanged", c.name)
		}
		seen[id] = c.name
	}
	// The ID is computed once per toolchain value (a run's keys agree with each other).
	if tc.cacheID() != id0 {
		t.Error("cacheID of one toolchain value changed during the run")
	}
	// An unreadable library makes every key unique: the caches always miss.
	gone := newFakeTC(filepath.Join(t.TempDir(), "no-such-toolchain"))
	if gone.cacheID() == newFakeTC(gone.sysroot).cacheID() {
		t.Error("a toolchain that cannot be walked got a reproducible cache ID")
	}
}

// privateCache points JANUS_CACHE_DIR at a new private directory (mode 0700, under the test's
// temporary directory) and returns it.
func privateCache(t *testing.T) string {
	t.Helper()
	c := filepath.Join(t.TempDir(), "cache")
	if err := os.Mkdir(c, 0o700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_CACHE_DIR", c)
	return c
}

// M1: a trusted-compile entry is used only if its manifest's MAC verifies.
func TestRound8TrustedManifestMAC(t *testing.T) {
	privateCache(t)
	src := t.TempDir()
	data := []byte("compiled Extracted")
	writeBytes(t, filepath.Join(src, "Extracted.olean"), data)
	files := pins{"Extracted.olean": sha256Hex(data)}
	key := strings.Repeat("ab", 32)
	storeTrustedCache(key, src, files)
	manifest := filepath.Join(trustedCacheDir(), key[:2], key, "manifest.json")
	load := func() bool {
		dst := t.TempDir()
		ok := loadTrustedCache(key, dst)
		if _, err := os.Stat(filepath.Join(dst, "Extracted.olean")); (err == nil) != ok {
			t.Fatalf("load reported %v but the copy exists: %v", ok, err == nil)
		}
		return ok
	}
	if !load() {
		t.Fatal("an authentic entry missed")
	}
	orig, err := os.ReadFile(manifest)
	if err != nil {
		t.Fatal(err)
	}
	var m map[string]any
	if err := json.Unmarshal(orig, &m); err != nil || m["mac"] == "" || m["mac"] == nil {
		t.Fatalf("stored manifest has no MAC: %s", orig)
	}
	rewrite := func(edit func(map[string]any)) {
		var mm map[string]any
		_ = json.Unmarshal(orig, &mm)
		edit(mm)
		b, _ := json.Marshal(mm)
		if err := os.WriteFile(manifest, b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	for _, c := range []struct {
		name string
		edit func(map[string]any)
	}{
		{"missing MAC (a pre-round-8 or planted manifest)", func(m map[string]any) { delete(m, "mac") }},
		{"empty MAC", func(m map[string]any) { m["mac"] = "" }},
		{"bad MAC", func(m map[string]any) { m["mac"] = strings.Repeat("0", 64) }},
		{"MAC of another entry", func(m map[string]any) {
			hk, _ := resultHMACKey()
			m["mac"] = trustedMAC(hk, strings.Repeat("cd", 32), files)
		}},
		{"files swapped under the old MAC", func(m map[string]any) {
			m["files"] = map[string]string{"Extracted.olean": sha256Hex([]byte("forged"))}
		}},
	} {
		rewrite(c.edit)
		if load() {
			t.Errorf("%s: the entry was used", c.name)
		}
	}
	// A forged manifest that is internally consistent (planted data and its hash) is a miss too.
	writeBytes(t, filepath.Join(filepath.Dir(manifest), "Extracted.olean"), []byte("forged"))
	rewrite(func(m map[string]any) {
		m["files"] = map[string]string{"Extracted.olean": sha256Hex([]byte("forged"))}
		delete(m, "mac")
	})
	if load() {
		t.Error("a self-consistent manifest without a MAC was used")
	}
	// The next store replaces the unauthentic entry, and it hits again.
	storeTrustedCache(key, src, files)
	if !load() {
		t.Error("an unauthentic entry was not replaced by the next store")
	}
	if b, _ := os.ReadFile(filepath.Join(filepath.Dir(manifest), "Extracted.olean")); !bytes.Equal(b, data) {
		t.Errorf("replaced entry holds %q", b)
	}
	// With another cache key (another user's cache, a new key) the old MAC fails.
	keyFile := filepath.Join(resultCacheDir(), ".key")
	if err := os.WriteFile(keyFile, bytes.Repeat([]byte{7}, 32), 0o600); err != nil {
		t.Fatal(err)
	}
	if load() {
		t.Error("an entry verified under another key")
	}
}

// C1: an unsafe cache root, a symbolic link among its directories or a readable key is refused
// with a diagnostic that says what is wrong.
func TestRound8CacheRootPrivate(t *testing.T) {
	expect := func(t *testing.T, err error, want ...string) {
		t.Helper()
		if err == nil {
			t.Fatalf("accepted (want an error mentioning %q)", want)
		}
		d, ok := err.(*diag)
		if !ok || d.Stage != "cache safety" || !d.Invalid || d.Next == "" {
			t.Fatalf("not a cache-safety diagnostic: %#v", err)
		}
		for _, w := range append(want, "round 8 C1") {
			if !strings.Contains(d.Msg, w) {
				t.Errorf("message %q lacks %q", d.Msg, w)
			}
		}
	}
	t.Run("private root accepted and created 0700", func(t *testing.T) {
		c := filepath.Join(t.TempDir(), "new", "cache")
		t.Setenv("JANUS_CACHE_DIR", c)
		if err := checkCacheRoot(); err != nil {
			t.Fatal(err)
		}
		if fi, err := os.Stat(c); err != nil || fi.Mode().Perm() != 0o700 {
			t.Fatalf("root not created private: %v %v", fi, err)
		}
		if _, err := resultHMACKey(); err != nil {
			t.Fatal(err)
		}
		if fi, err := os.Lstat(filepath.Join(c, "v1", "result", ".key")); err != nil || fi.Mode().Perm() != 0o600 {
			t.Fatalf("key not 0600: %v %v", fi, err)
		}
	})
	t.Run("root reached through a symbolic link accepted", func(t *testing.T) {
		c := privateCache(t)
		link := filepath.Join(t.TempDir(), "link")
		if err := os.Symlink(c, link); err != nil {
			t.Fatal(err)
		}
		t.Setenv("JANUS_CACHE_DIR", link)
		if err := checkCacheRoot(); err != nil {
			t.Fatal(err)
		}
	})
	t.Run("group-writable root", func(t *testing.T) {
		c := privateCache(t)
		if err := os.Chmod(c, 0o770); err != nil {
			t.Fatal(err)
		}
		expect(t, checkCacheRoot(), "writable by group or others", "mode 770")
		_, err := resultHMACKey()
		expect(t, err, "writable by group or others")
	})
	t.Run("other-writable root", func(t *testing.T) {
		c := privateCache(t)
		if err := os.Chmod(c, 0o707); err != nil {
			t.Fatal(err)
		}
		expect(t, checkCacheRoot(), "writable by group or others")
	})
	t.Run("group-writable parent without the sticky bit", func(t *testing.T) {
		parent := filepath.Join(t.TempDir(), "shared")
		if err := os.Mkdir(parent, 0o700); err != nil {
			t.Fatal(err)
		}
		c := filepath.Join(parent, "cache")
		if err := os.Mkdir(c, 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.Chmod(parent, 0o775); err != nil {
			t.Fatal(err)
		}
		t.Setenv("JANUS_CACHE_DIR", c)
		expect(t, checkCacheRoot(), "its parent", "without the sticky bit")
		if err := os.Chmod(parent, 0o777|os.ModeSticky); err != nil { // like /tmp: accepted
			t.Fatal(err)
		}
		if err := checkCacheRoot(); err != nil {
			t.Fatalf("sticky shared parent refused: %v", err)
		}
	})
	t.Run("symlinked subdirectory", func(t *testing.T) {
		for _, sub := range []string{"v1", "v1/result", "v1/trusted"} {
			c := privateCache(t)
			elsewhere := t.TempDir()
			if err := os.MkdirAll(filepath.Dir(filepath.Join(c, sub)), 0o700); err != nil {
				t.Fatal(err)
			}
			if err := os.Symlink(elsewhere, filepath.Join(c, sub)); err != nil {
				t.Fatal(err)
			}
			expect(t, checkCacheRoot(), filepath.Base(sub), "is a symbolic link")
		}
	})
	t.Run("group-writable subdirectory", func(t *testing.T) {
		c := privateCache(t)
		if err := os.MkdirAll(filepath.Join(c, "v1", "trusted"), 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.Chmod(filepath.Join(c, "v1", "trusted"), 0o775); err != nil {
			t.Fatal(err)
		}
		expect(t, checkCacheRoot(), "trusted", "writable by group or others")
	})
	t.Run("subdirectory that is a file", func(t *testing.T) {
		c := privateCache(t)
		writeBytes(t, filepath.Join(c, "v1", "replay"), []byte("x"))
		expect(t, checkCacheRoot(), "replay", "is not a directory")
	})
	t.Run("0644 key", func(t *testing.T) {
		c := privateCache(t)
		if _, err := resultHMACKey(); err != nil {
			t.Fatal(err)
		}
		key := filepath.Join(c, "v1", "result", ".key")
		if err := os.Chmod(key, 0o644); err != nil {
			t.Fatal(err)
		}
		_, err := resultHMACKey()
		expect(t, err, ".key", "mode is 0644")
		// The verification and the trusted cache refuse it too (no silent use of a leaked key).
		if lookupResult(strings.Repeat("ab", 32)) != nil {
			t.Error("lookup with a 0644 key")
		}
		if _, ok := readTrustedManifest(t.TempDir(), strings.Repeat("ab", 32)); ok {
			t.Error("trusted manifest accepted with a 0644 key")
		}
	})
	t.Run("key that is a symbolic link", func(t *testing.T) {
		c := privateCache(t)
		dir := filepath.Join(c, "v1", "result")
		if err := os.MkdirAll(dir, 0o700); err != nil {
			t.Fatal(err)
		}
		target := filepath.Join(t.TempDir(), "k")
		if err := os.WriteFile(target, bytes.Repeat([]byte{1}, 32), 0o600); err != nil {
			t.Fatal(err)
		}
		if err := os.Symlink(target, filepath.Join(dir, ".key")); err != nil {
			t.Fatal(err)
		}
		_, err := resultHMACKey()
		expect(t, err, "is a symbolic link")
	})
	t.Run("key of the wrong length", func(t *testing.T) {
		c := privateCache(t)
		dir := filepath.Join(c, "v1", "result")
		if err := os.MkdirAll(dir, 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, ".key"), []byte("short"), 0o600); err != nil {
			t.Fatal(err)
		}
		_, err := resultHMACKey()
		expect(t, err, "5 bytes, not 32")
	})
	t.Run("result directory readable by others", func(t *testing.T) {
		c := privateCache(t)
		dir := filepath.Join(c, "v1", "result")
		if err := os.MkdirAll(dir, 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.Chmod(dir, 0o755); err != nil {
			t.Fatal(err)
		}
		_, err := resultHMACKey()
		expect(t, err, "mode 755")
	})
	t.Run("cache files are opened without following links", func(t *testing.T) {
		d := t.TempDir()
		target := filepath.Join(d, "real")
		writeBytes(t, target, []byte("{}"))
		if err := os.Symlink(target, filepath.Join(d, "link")); err != nil {
			t.Fatal(err)
		}
		if _, err := readPrivateFile(filepath.Join(d, "link"), false); err == nil {
			t.Error("readPrivateFile followed a symbolic link")
		}
		if _, err := readPrivateFile(target, false); err != nil {
			t.Error(err)
		}
	})
}

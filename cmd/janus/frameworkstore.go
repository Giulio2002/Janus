package main

// A content-keyed store for the build of the EMBEDDED framework (JANUS_FRAMEWORK_STORE=<dir>).
//
// The embedded framework is compiled by Lake into <cache>/v1/framework/<sha>, once per cache. A host with
// several caches (the gate's user cache and the Go tests' fixture cache, a CI worker with a fresh cache per job)
// compiles the same sources with the same toolchain once per cache, about 270 s of CPU each. With the store, the
// first build is published under a key naming EVERY input of the compilation, and later builds restore it
// instead of compiling; Lake is still run afterwards and finds nothing to do, and the build is stamped from the
// files as they are on disk, exactly as after a compile.
//
// Why this trusts nothing it did not trust before:
//   - the key is SHA-256 over: the schema, the framework's source identity (every Lean source and the lake manifest,
//     frameworkSha), the toolchain identity (toolchain.cacheID: version, lean and leanchecker bytes, stat data of the
//     toolchain's bin/ and lib/), and the SHA-256 of this janus executable (the program that drove the build). A
//     different source byte, toolchain or janus is a different key: a miss, and a full compile;
//   - an entry is only ever written by janus after its own successful Lake build, and carries a manifest of every
//     file of the build (SHA-256, mode, size) under an HMAC with the store's private key (mode 0600, directory 0700,
//     owned by this user, hidden from sandboxed processes like the result cache). A restore recomputes the manifest of
//     the stored files, checks the MAC and the key, copies, and recomputes the manifest of the copy; ANY difference,
//     a non-regular file, or an unreadable store falls back to the full compile;
//   - the restored build is untrusted exactly as a compiled one: the framework pins, the stamp and the kernel replay
//     (leanchecker on every module) are unchanged, and the replay verdict is never stored here;
//   - --fresh and --fresh-framework build in a new temporary directory (freshBase) and never read or write the store.

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"syscall"
)

const frameworkStoreSchema = "janus-framework-store-v1"

// privateStoreDirs are the gate-private stores sandboxed processes must not see.
func privateStoreDirs() []string {
	var ds []string
	for _, env := range []string{"JANUS_VERDICT_CACHE", "JANUS_FRAMEWORK_STORE"} {
		d := os.Getenv(env)
		if d != "" && d != "off" && filepath.IsAbs(d) {
			ds = append(ds, d)
		}
	}
	return ds
}

type frameworkStore struct{ dir string }

// externalFrameworkStore returns the store named by JANUS_FRAMEWORK_STORE (nil when unset or "off"). An unsafe
// directory is an error, never a silent fallback.
func externalFrameworkStore() (*frameworkStore, error) {
	dir := os.Getenv("JANUS_FRAMEWORK_STORE")
	if dir == "" || dir == "off" {
		return nil, nil
	}
	if !filepath.IsAbs(dir) {
		return nil, keyDiag("JANUS_FRAMEWORK_STORE is not an absolute path")
	}
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return nil, err
	}
	fi, err := os.Lstat(dir)
	if err != nil || !fi.IsDir() || fi.Mode().Perm()&0o077 != 0 {
		return nil, keyDiag("the framework store " + dir + " is not a private directory (mode 0700, not a link)")
	}
	if st, ok := fi.Sys().(*syscall.Stat_t); !ok || int(st.Uid) != os.Getuid() {
		return nil, keyDiag("the framework store " + dir + " is not owned by this user")
	}
	return &frameworkStore{dir: dir}, nil
}

// storeKey names every input of the compilation of the embedded framework (see the header).
func frameworkStoreKey(fw *framework, tc *toolchain) string {
	h := sha256.New()
	fmt.Fprintf(h, "%s\nsources %s\nmanifest %s\ntoolchain %s\njanus %s\n", frameworkStoreSchema, fw.Sha256,
		sha256Hex(fw.Files["lake-manifest.json"]), tc.cacheID(), executableSha())
	return hex.EncodeToString(h.Sum(nil))
}

type storeFile struct {
	Path string `json:"p"`
	Sha  string `json:"s"`
	Mode uint32 `json:"m"`
	Size int64  `json:"z"`
}

type storeEntry struct {
	Key   string      `json:"key"`
	Files []storeFile `json:"files"`
	MAC   string      `json:"mac"`
}

func (e *storeEntry) mac(hk []byte) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "%s\n%s\n", frameworkStoreSchema, e.Key)
	for _, f := range e.Files {
		fmt.Fprintf(m, "%s %s %o %d\n", f.Path, f.Sha, f.Mode, f.Size)
	}
	return hex.EncodeToString(m.Sum(nil))
}

// manifestOf hashes every file under root (which must hold only directories and regular files).
func manifestOf(root string) ([]storeFile, error) {
	var fs_ []storeFile
	err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		if !d.Type().IsRegular() {
			return fmt.Errorf("%s is not a regular file", p)
		}
		fi, err := d.Info()
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(root, p)
		fs_ = append(fs_, storeFile{Path: filepath.ToSlash(rel), Sha: regularFileSha(p), Mode: uint32(fi.Mode().Perm()), Size: fi.Size()})
		return nil
	})
	if err != nil {
		return nil, err
	}
	for _, f := range fs_ {
		if f.Sha == "" {
			return nil, fmt.Errorf("%s cannot be read", f.Path)
		}
	}
	sort.Slice(fs_, func(i, j int) bool { return fs_[i].Path < fs_[j].Path })
	return fs_, nil
}

func sameManifest(a, b []storeFile) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// copyBuildTree copies src (directories and regular files only) to dst, keeping modes and modification times.
func copyBuildTree(src, dst string) error {
	return filepath.WalkDir(src, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(src, p)
		t := filepath.Join(dst, rel)
		if d.IsDir() {
			return os.MkdirAll(t, 0o755)
		}
		if !d.Type().IsRegular() {
			return fmt.Errorf("%s is not a regular file", p)
		}
		fi, err := d.Info()
		if err != nil {
			return err
		}
		in, err := os.Open(p)
		if err != nil {
			return err
		}
		defer in.Close()
		out, err := os.OpenFile(t, os.O_CREATE|os.O_WRONLY|os.O_EXCL, fi.Mode().Perm())
		if err != nil {
			return err
		}
		if _, err := io.Copy(out, in); err != nil {
			out.Close()
			return err
		}
		if err := out.Close(); err != nil {
			return err
		}
		return os.Chtimes(t, fi.ModTime(), fi.ModTime())
	})
}

// restore copies the stored build of key into dir/.lake/build when the entry is authentic and complete. It reports
// whether it did; on any doubt it leaves dir/.lake/build absent and returns false (the caller compiles).
func (s *frameworkStore) restore(key, dir string) bool {
	entryDir := filepath.Join(s.dir, "fw", key)
	b, err := os.ReadFile(filepath.Join(entryDir, "entry.json"))
	if err != nil {
		return false
	}
	var e storeEntry
	if json.Unmarshal(b, &e) != nil || e.Key != key {
		return false
	}
	hk, err := hmacKeyInDir(filepath.Join(s.dir, "key"))
	if err != nil || !hmac.Equal([]byte(e.MAC), []byte(e.mac(hk))) {
		return false
	}
	src := filepath.Join(entryDir, "build")
	if have, err := manifestOf(src); err != nil || !sameManifest(have, e.Files) {
		return false
	}
	dst := filepath.Join(dir, ".lake", "build")
	_ = os.RemoveAll(dst)
	if err := copyBuildTree(src, dst); err != nil {
		_ = os.RemoveAll(dst)
		return false
	}
	if have, err := manifestOf(dst); err != nil || !sameManifest(have, e.Files) {
		_ = os.RemoveAll(dst)
		return false
	}
	return true
}

// publish stores dir/.lake/build under key (a no-op when an entry exists). Errors are not fatal: the build stays usable.
func (s *frameworkStore) publish(key, dir string) {
	entryDir := filepath.Join(s.dir, "fw", key)
	if _, err := os.Stat(filepath.Join(entryDir, "entry.json")); err == nil {
		return
	}
	hk, err := hmacKeyInDir(filepath.Join(s.dir, "key"))
	if err != nil {
		return
	}
	if err := os.MkdirAll(filepath.Join(s.dir, "fw"), 0o700); err != nil {
		return
	}
	tmp, err := os.MkdirTemp(filepath.Join(s.dir, "fw"), ".tmp-")
	if err != nil {
		return
	}
	defer os.RemoveAll(tmp)
	if err := copyBuildTree(filepath.Join(dir, ".lake", "build"), filepath.Join(tmp, "build")); err != nil {
		return
	}
	files, err := manifestOf(filepath.Join(tmp, "build"))
	if err != nil {
		return
	}
	e := storeEntry{Key: key, Files: files}
	e.MAC = e.mac(hk)
	b, _ := json.Marshal(e)
	if os.WriteFile(filepath.Join(tmp, "entry.json"), b, 0o600) != nil {
		return
	}
	_ = os.RemoveAll(entryDir) // an incomplete leftover
	if os.Rename(tmp, entryDir) != nil {
		return
	}
	s.prune(key, 3)
}

// prune keeps the keep most recently used entries (the one just published is never removed); a restore that races a removal
// fails its manifest check and the caller compiles.
func (s *frameworkStore) prune(except string, keep int) {
	ents, err := os.ReadDir(filepath.Join(s.dir, "fw"))
	if err != nil {
		return
	}
	type ent struct {
		name string
		mod  int64
	}
	var es []ent
	for _, e := range ents {
		if !e.IsDir() || strings.HasPrefix(e.Name(), ".") || e.Name() == except {
			continue
		}
		if fi, err := e.Info(); err == nil {
			es = append(es, ent{e.Name(), fi.ModTime().UnixNano()})
		}
	}
	sort.Slice(es, func(i, j int) bool { return es[i].mod > es[j].mod })
	for i := keep - 1; i >= 0 && i < len(es); i++ {
		_ = os.RemoveAll(filepath.Join(s.dir, "fw", es[i].name))
	}
}

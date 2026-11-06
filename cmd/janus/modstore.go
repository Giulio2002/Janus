package main

// The module store: Lake's build outputs of the consumer's Extracted-free modules, shared across
// extractions, workspaces and framework builds of one cache (docs/CLI.md, "Cache").
//
// A consumer workspace is one extraction's: its Lake build directory is seeded from the newest sibling of
// its family only, and a family exists per framework build, so a module the sibling lacks, or any module
// after a framework change, was built again although nothing it reads had changed (String amd64: 68
// modules, 55 min, the Dec and udivrem/Knuth chains among them). Lake itself rebuilds exactly the modules
// whose traces differ, and the traces of two builds of one module from the same inputs are the same bytes;
// so a module's Lake outputs can be reused wherever the module's inputs are the same.
//
// An entry is keyed by everything the module's Lake build reads: the toolchain, the package, the module and
// its source, the package's Lake configuration and options, the keys of the package modules it imports (so,
// transitively, its whole package closure) and the digest of the framework modules in its import closure
// (fwClosureDigest, which includes the olean hash of each). A module whose import closure contains Extracted
// or JanusTrusted is never keyed: its inputs change with every extraction, and the trusted compile of
// Extracted is untouched. An entry is a directory (module data files plus a manifest authenticated with the
// cache's hidden key, like the trusted-compile entries): written once, by an atomic rename, and never
// replaced; read with the manifest's MAC and the SHA-256 of every file, so a changed byte is a miss.
//
// Soundness: these are build outputs of the untrusted Lake build, used only to skip rebuilding it. What the
// audit and the kernel replay judge is janus's own compile of the closure (provenance.go), never Lake's
// oleans; Lake rechecks its own traces on whatever it finds, so a stale or inconsistent copy is rebuilt.

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strings"
)

func modstoreDir() string { return filepath.Join(cacheRoot(), "v1", "modstore") }

// modstoreExts are the files of a module in a Lake build directory (rel is the module path, `A/B/C`).
var modstoreFiles = []string{
	"lib/lean/%s.olean", "lib/lean/%s.ilean", "lib/lean/%s.trace", "lib/lean/%s.olean.hash", "lib/lean/%s.ilean.hash",
	"ir/%s.c", "ir/%s.c.hash", "ir/%s.setup.json",
}

// modstoreRequired are the ones an entry must have.
var modstoreRequired = []string{"lib/lean/%s.olean", "lib/lean/%s.ilean", "lib/lean/%s.trace"}

type modstoreManifest struct {
	Key   string `json:"key"`
	Files pins   `json:"files"` // build-dir-relative slash path -> SHA-256
	MAC   string `json:"mac"`
}

func modstoreMAC(hk []byte, key string, files pins) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-modstore-entry-v1\n%q\n%q\n", key, pinsDigest(files))
	return hex.EncodeToString(m.Sum(nil))
}

// modstoreRelOK: a manifest path is `lib/lean/…` or `ir/…`, clean, with a module-data or Lake extension.
func modstoreRelOK(rel string) bool {
	if path.Clean(rel) != rel || strings.HasPrefix(rel, "/") || strings.Contains(rel, "..") {
		return false
	}
	if !strings.HasPrefix(rel, "lib/lean/") && !strings.HasPrefix(rel, "ir/") {
		return false
	}
	for _, e := range []string{".olean", ".ilean", ".trace", ".hash", ".c", ".setup.json"} {
		if strings.HasSuffix(rel, e) {
			return true
		}
	}
	return false
}

func modstoreEntry(key string) string { return filepath.Join(modstoreDir(), key[:2], key) }

func readModstoreManifest(entry, key string) (modstoreManifest, bool) {
	var m modstoreManifest
	b, err := readPrivateFile(filepath.Join(entry, "manifest.json"), false)
	if err != nil {
		return m, false
	}
	if json.Unmarshal(b, &m) != nil || m.Key != key || len(m.Files) == 0 || m.MAC == "" {
		return m, false
	}
	hk, err := resultHMACKey()
	if err != nil || !hmac.Equal([]byte(m.MAC), []byte(modstoreMAC(hk, key, m.Files))) {
		return m, false
	}
	return m, true
}

// modstoreLoad copies the entry of key into the build directory dst. Every file is verified against the
// authenticated manifest as it is read; any mismatch is a miss and the partial copy is removed.
func modstoreLoad(key, dst string) bool {
	ok, _ := modstoreLoadX(key, dst)
	return ok
}

// modstoreLoadX is modstoreLoad, also reporting whether an entry directory exists for key (so that a miss
// of an existing, damaged entry can be repaired by the harvest).
func modstoreLoadX(key, dst string) (loaded, exists bool) {
	if len(key) < 3 {
		return false, false
	}
	entry := modstoreEntry(key)
	if _, err := os.Lstat(entry); err == nil {
		exists = true
	}
	m, ok := readModstoreManifest(entry, key)
	if !ok {
		return false, exists
	}
	var copied []string
	undo := func() (bool, bool) {
		for _, p := range copied {
			_ = os.Remove(p)
		}
		return false, true
	}
	rels := make([]string, 0, len(m.Files))
	for rel := range m.Files {
		rels = append(rels, rel)
	}
	sort.Strings(rels)
	for _, rel := range rels {
		if !modstoreRelOK(rel) {
			return undo()
		}
		data, err := readPrivateFile(filepath.Join(entry, filepath.FromSlash(rel)), false)
		if err != nil || sha256Hex(data) != m.Files[rel] {
			return undo()
		}
		p := filepath.Join(dst, filepath.FromSlash(rel))
		if os.MkdirAll(filepath.Dir(p), 0o755) != nil || os.WriteFile(p, data, 0o644) != nil {
			return undo()
		}
		copied = append(copied, p)
	}
	touchHit(entry)
	return true, true
}

func modstoreIntact(entry string, m modstoreManifest) bool {
	for rel, want := range m.Files {
		if !modstoreRelOK(rel) {
			return false
		}
		data, err := readPrivateFile(filepath.Join(entry, filepath.FromSlash(rel)), false)
		if err != nil || sha256Hex(data) != want {
			return false
		}
	}
	return true
}

// modstorePut records the Lake outputs of the module modRel (`A/B/C`) found in the build directory src
// under key. It never replaces an authentic, intact entry (a concurrent writer of the same key wins, both
// wrote the same inputs' outputs); an entry that is not is moved aside first. Atomic: a complete entry or none.
// It reports whether the entry exists afterwards.
func modstorePut(key, src, modRel string) bool {
	if len(key) < 3 {
		return false
	}
	files := pins{}
	data := map[string][]byte{}
	for _, f := range modstoreFiles {
		rel := fmt.Sprintf(f, modRel)
		b, err := os.ReadFile(filepath.Join(src, filepath.FromSlash(rel)))
		if err != nil {
			continue
		}
		files[rel] = sha256Hex(b)
		data[rel] = b
	}
	for _, f := range modstoreRequired {
		if _, ok := files[fmt.Sprintf(f, modRel)]; !ok {
			return false
		}
	}
	parent := filepath.Join(modstoreDir(), key[:2])
	final := filepath.Join(parent, key)
	if os.MkdirAll(parent, 0o755) != nil {
		return false
	}
	if _, err := os.Lstat(final); err == nil {
		if m, ok := readModstoreManifest(final, key); ok && modstoreIntact(final, m) {
			return true
		}
		old, err := os.MkdirTemp(parent, ".stale-")
		if err != nil {
			return false
		}
		if os.Rename(final, filepath.Join(old, "entry")) != nil {
			os.Remove(old)
			return false
		}
		os.RemoveAll(old)
	}
	tmp, err := os.MkdirTemp(parent, ".tmp-")
	if err != nil {
		return false
	}
	for rel, b := range data {
		p := filepath.Join(tmp, filepath.FromSlash(rel))
		if os.MkdirAll(filepath.Dir(p), 0o755) != nil || os.WriteFile(p, b, 0o644) != nil {
			os.RemoveAll(tmp)
			return false
		}
	}
	hk, err := resultHMACKey()
	if err != nil {
		os.RemoveAll(tmp)
		return false
	}
	mb, _ := json.Marshal(modstoreManifest{Key: key, Files: files, MAC: modstoreMAC(hk, key, files)})
	if os.WriteFile(filepath.Join(tmp, "manifest.json"), mb, 0o644) != nil {
		os.RemoveAll(tmp)
		return false
	}
	if err := os.Rename(tmp, final); err != nil {
		// lost the race to a concurrent writer (the target exists and is not empty): theirs stands
		os.RemoveAll(tmp)
		m, ok := readModstoreManifest(final, key)
		return ok && modstoreIntact(final, m)
	}
	return true
}

// ---- the keys of a package's modules ----

// storePkg is one package whose Extracted-free modules the store covers.
type storePkg struct {
	name    string // "" for the consumer
	files   map[string][]byte
	config  string
	srcDirs []string
	dopts   []string
	build   string // its Lake build directory in the workspace
}

// storeMod is a module the store covers.
type storeMod struct {
	name string
	key  string
	rel  string // A/B/C
	pkg  *storePkg
}

// storeModules returns the modules of pkg and its dependencies whose import closure excludes Extracted
// and JanusTrusted, with their keys. files are the sources of the framework package (including Extracted,
// which a module may import), want the pins of its trusted build. It returns nil when some package is outside
// the strict lakefile subset (the options Lake would pass are then not known), or has an unreadable
// header: the store then does nothing.
// lakefileBuildDigest digests what in a (strict-subset) lakefile.toml can change how a module compiles: every
// setting except the `[[require]]` tables. A dependency's revision or location does not: what a module reads of
// it is its import closure, which the key covers by content (so a framework bump that leaves the closure's oleans
// unchanged keeps the key). It returns "" when the file is not parseable.
func lakefileBuildDigest(src []byte) string {
	pairs, ok := parseLakefileToml(string(src))
	if !ok {
		return ""
	}
	h := sha256.New()
	for _, p := range pairs {
		if p.table == "require" {
			continue
		}
		fmt.Fprintf(h, "%q %q %q\n", p.table, p.key, p.raw)
	}
	return hex.EncodeToString(h.Sum(nil))
}

func storeModules(tcID string, ws *consumerWS, pkg *consumerPkg, fwFiles map[string][]byte, want pins) map[string]*storeMod {
	var pkgs []*storePkg
	add := func(name string, files map[string][]byte, config, build string) bool {
		sd, do, ok := compileConfig(files, config)
		if !ok {
			return false
		}
		pkgs = append(pkgs, &storePkg{name: name, files: files, config: config, srcDirs: sd, dopts: do, build: build})
		return true
	}
	if !add("", pkg.Files, pkg.Lakefile, filepath.Join(ws.Root, ".lake", "build")) {
		return nil
	}
	for _, d := range pkg.Deps {
		if !add(d.Info.Name, d.Files, d.Config, filepath.Join(ws.DepsDir, d.Info.Name, ".lake", "build")) {
			return nil
		}
	}
	// module -> (package, source path)
	type loc struct {
		p   *storePkg
		rel string
	}
	where := map[string]loc{}
	dup := map[string]bool{}
	for _, p := range pkgs {
		for f := range p.files {
			if !strings.HasSuffix(f, ".lean") {
				continue
			}
			for _, sd := range p.srcDirs {
				base := sd
				if base != "" {
					base += "/"
				}
				if !strings.HasPrefix(f, base) {
					continue
				}
				m := strings.ReplaceAll(strings.TrimSuffix(strings.TrimPrefix(f, base), ".lean"), "/", ".")
				if _, ok := where[m]; ok {
					dup[m] = true
				}
				where[m] = loc{p, f}
			}
		}
	}
	type res struct {
		key string
		ok  bool
	}
	memo := map[string]res{}
	var resolve func(m string) res
	resolve = func(m string) res {
		if r, ok := memo[m]; ok {
			return r
		}
		memo[m] = res{} // a cycle is ineligible
		l, ok := where[m]
		if !ok || dup[m] {
			return res{}
		}
		src := l.p.files[l.rel]
		imps, ok := parseImports(src)
		if !ok {
			return res{}
		}
		var own, ext []string
		for _, i := range imps {
			if i == "Extracted" || i == "JanusTrusted" {
				return res{}
			}
			if _, isPkg := where[i]; isPkg {
				r := resolve(i)
				if !r.ok {
					return res{}
				}
				own = append(own, i+" "+r.key)
				continue
			}
			if _, isFw := fwFiles[strings.ReplaceAll(i, ".", "/")+".lean"]; isFw {
				ext = append(ext, i)
				continue
			}
			if r := moduleRoot(i); r == "Init" || r == "Std" || r == "Lean" || r == "Lake" {
				continue
			}
			return res{} // neither a package module nor the framework's nor the toolchain's
		}
		// the framework closure must not reach Extracted either
		if fwReaches(fwFiles, ext, "Extracted") || fwReaches(fwFiles, ext, "JanusTrusted") {
			return res{}
		}
		sort.Strings(own)
		h := sha256.New()
		fmt.Fprintf(h, "janus-modstore-key-v1\n%q\npackage %q\nmodule %q\nsource %q %s\nconfig %q %s\nopts %q\nimports %q\nframework %s\n",
			tcID, l.p.name, m, l.rel, sha256Hex(src), l.p.config, lakefileBuildDigest(l.p.files[l.p.config]), l.p.dopts, own,
			fwClosureDigestX(fwFiles, want, ext, true))
		r := res{hex.EncodeToString(h.Sum(nil)), true}
		memo[m] = r
		return r
	}
	out := map[string]*storeMod{}
	for m, l := range where {
		if r := resolve(m); r.ok {
			out[m] = &storeMod{name: m, key: r.key, rel: strings.ReplaceAll(m, ".", "/"), pkg: l.p}
		}
	}
	return out
}

// fwReaches: does the framework import closure of imps contain module target?
func fwReaches(files map[string][]byte, imps []string, target string) bool {
	seen := map[string]bool{}
	var visit func(m string) bool
	visit = func(m string) bool {
		if m == target {
			return true
		}
		if seen[m] {
			return false
		}
		seen[m] = true
		src, ok := files[strings.ReplaceAll(m, ".", "/")+".lean"]
		if !ok {
			return false
		}
		is, ok := parseImports(src)
		if !ok {
			return true // unreadable: assume it does
		}
		for _, i := range is {
			if visit(i) {
				return true
			}
		}
		return false
	}
	for _, i := range imps {
		if visit(i) {
			return true
		}
	}
	return false
}

// modstoreSeed copies into the workspace's Lake build directories every covered module that is missing
// there and has a store entry; it returns the modules it seeded.
func (ws *consumerWS) modstoreSeed(mods map[string]*storeMod) []string {
	var seeded []string
	ws.storeDamaged = map[string]bool{}
	names := make([]string, 0, len(mods))
	for m := range mods {
		names = append(names, m)
	}
	sort.Strings(names)
	for _, m := range names {
		sm := mods[m]
		if _, err := os.Stat(filepath.Join(sm.pkg.build, "lib", "lean", filepath.FromSlash(sm.rel)+".olean")); err == nil {
			continue
		}
		loaded, exists := modstoreLoadX(sm.key, sm.pkg.build)
		if loaded {
			seeded = append(seeded, m)
		} else if exists {
			ws.storeDamaged[sm.key] = true // an entry that does not verify: the harvest replaces it
		}
	}
	return seeded
}

// modstoreHarvest records the Lake outputs of every covered module that has them and no entry yet.
func (ws *consumerWS) modstoreHarvest(mods map[string]*storeMod) int {
	n := 0
	for _, sm := range mods {
		if _, ok := readModstoreManifest(modstoreEntry(sm.key), sm.key); ok && !ws.storeDamaged[sm.key] {
			continue
		}
		if modstorePut(sm.key, sm.pkg.build, sm.rel) {
			n++
		}
	}
	return n
}

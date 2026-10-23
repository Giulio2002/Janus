package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	"runtime/debug"
	"sort"
	"strings"
	"time"

	janus "github.com/Giulio2002/Janus"
)

// The Janus Lean framework the verifier builds proofs against. By default it is the copy
// embedded in this binary (package github.com/Giulio2002/Janus); --janus-root or
// $JANUS_ROOT selects a checkout instead (framework development).
type framework struct {
	Source    string            // "embedded" or "directory"
	Dir       string            // the checkout, for "directory"
	Files     map[string][]byte // slash-separated path -> bytes
	Sha256    string            // over the identity files, see frameworkSha
	Toolchain string            // trimmed lean-toolchain
}

// frameworkInfo is the framework's record in verified.json.
type frameworkInfo struct {
	Source    string `json:"source"`
	Sha256    string `json:"sha256"`
	Files     int    `json:"files"`
	Toolchain string `json:"toolchain"`
	Revision  string `json:"revision,omitempty"`
	Modified  bool   `json:"modified,omitempty"`
	Dir       string `json:"dir,omitempty"`
}

const janusRepoURL = "https://github.com/Giulio2002/Janus"

// isFrameworkFile selects the files that make up the framework. Its identity (what a
// consumer's dependency is compared against) is everything but lake-manifest.json.
func isFrameworkFile(p string) bool {
	switch p {
	case "Janus.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain":
		return true
	}
	return strings.HasPrefix(p, "Janus/") && strings.HasSuffix(p, ".lean")
}

func isIdentityFile(p string) bool { return isFrameworkFile(p) && p != "lake-manifest.json" }

func readFramework(fsys fs.FS) (map[string][]byte, error) {
	files := map[string][]byte{}
	for _, p := range []string{"Janus.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"} {
		b, err := fs.ReadFile(fsys, p)
		if err != nil {
			return nil, err
		}
		files[p] = b
	}
	err := fs.WalkDir(fsys, "Janus", func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() && p != "Janus" && strings.HasPrefix(d.Name(), ".") {
			return fs.SkipDir
		}
		if !d.IsDir() && isFrameworkFile(p) {
			b, err := fs.ReadFile(fsys, p)
			if err != nil {
				return err
			}
			files[p] = b
		}
		return nil
	})
	return files, err
}

// frameworkSha hashes the identity files in sha256sum format, sorted by path, with LF line
// endings (the same normalisation the dependency comparison allows).
func frameworkSha(files map[string][]byte) string {
	var paths []string
	for p := range files {
		if isIdentityFile(p) {
			paths = append(paths, p)
		}
	}
	sort.Strings(paths)
	h := sha256.New()
	for _, p := range paths {
		fmt.Fprintf(h, "%s  %s\n", sha256Hex(normalizeEOL(files[p])), p)
	}
	return hex.EncodeToString(h.Sum(nil))
}

func normalizeEOL(b []byte) []byte { return bytes.ReplaceAll(b, []byte("\r\n"), []byte("\n")) }

var janusLakefileRE = regexp.MustCompile(`(?m)^name\s*=\s*"janus"\s*$`)

// loadFramework returns the framework selected by --janus-root / $JANUS_ROOT, else the
// embedded one.
func loadFramework(flag string) (*framework, error) {
	dir := flag
	if dir == "" {
		dir = os.Getenv("JANUS_ROOT")
	}
	fw := &framework{Source: "embedded"}
	var err error
	if dir != "" {
		abs, aerr := filepath.Abs(dir)
		b, rerr := os.ReadFile(filepath.Join(abs, "lakefile.toml"))
		if aerr != nil || rerr != nil || !janusLakefileRE.Match(b) {
			return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s is not the Janus Lean project (no lakefile.toml with name = \"janus\").", dir),
				Stage: "toolchain", Next: "Pass --janus-root pointing at a Janus checkout (or set JANUS_ROOT), or omit both to use the framework embedded in janus."}
		}
		fw.Source, fw.Dir = "directory", abs
		fw.Files, err = readFramework(os.DirFS(abs))
	} else {
		fw.Files, err = readFramework(janus.Framework)
	}
	if err != nil {
		return nil, &diag{Invalid: true, Msg: "Cannot read the Janus framework sources: " + err.Error(), Stage: "toolchain"}
	}
	fw.Sha256 = frameworkSha(fw.Files)
	fw.Toolchain = strings.TrimSpace(string(fw.Files["lean-toolchain"]))
	return fw, nil
}

func (fw *framework) info() *frameworkInfo {
	n := 0
	for p := range fw.Files {
		if isIdentityFile(p) {
			n++
		}
	}
	fi := &frameworkInfo{Source: fw.Source, Sha256: fw.Sha256, Files: n, Toolchain: fw.Toolchain}
	if fw.Source == "embedded" {
		fi.Revision, fi.Modified, _ = buildRevision()
	} else {
		fi.Dir = fw.Dir
		fi.Revision, fi.Modified = gitRevision(fw.Dir)
	}
	return fi
}

// buildRevision is the Janus commit this binary was built from: the VCS stamp of a build
// in a checkout, or the commit of a pseudo-version (`go install …@<commit>`; 12 hex digits).
func buildRevision() (rev string, modified bool, version string) {
	bi, ok := debug.ReadBuildInfo()
	if !ok {
		return "", false, ""
	}
	version = bi.Main.Version
	for _, s := range bi.Settings {
		switch s.Key {
		case "vcs.revision":
			rev = s.Value
		case "vcs.modified":
			modified = s.Value == "true"
		}
	}
	if rev == "" {
		if m := regexp.MustCompile(`-([0-9a-f]{12})(\+incompatible)?$`).FindStringSubmatch(version); m != nil {
			rev = m[1]
		}
	}
	return rev, modified, version
}

func gitRevision(dir string) (string, bool) {
	c, err := exec.Command("git", "-C", dir, "rev-parse", "HEAD").Output()
	if err != nil {
		return "", false
	}
	st, _ := exec.Command("git", "-C", dir, "status", "--porcelain", "--", "Janus", "Janus.lean", "lakefile.toml", "lean-toolchain").Output()
	return strings.TrimSpace(string(c)), len(bytes.TrimSpace(st)) > 0
}

// cacheRoot is $JANUS_CACHE_DIR, else <user cache dir>/janus.
func cacheRoot() string {
	if d := os.Getenv("JANUS_CACHE_DIR"); d != "" {
		if abs, err := filepath.Abs(d); err == nil {
			return abs
		}
		return d
	}
	if d, err := os.UserCacheDir(); err == nil {
		return filepath.Join(d, "janus")
	}
	return filepath.Join(os.TempDir(), "janus-cache")
}

func sleepBriefly() { time.Sleep(200 * time.Millisecond) }

// syncTree makes dir contain exactly files (slash paths), plus whatever keep accepts at the
// top level (e.g. ".lake"). Files whose bytes already match are left untouched.
func syncTree(dir string, files map[string][]byte, keep func(top string) bool) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	want := map[string]bool{}
	for p := range files {
		for q := p; q != "." && q != "/"; q = path.Dir(q) {
			want[q] = true
		}
	}
	var stale []string
	err := filepath.WalkDir(dir, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if p == dir {
			return nil
		}
		rel, _ := filepath.Rel(dir, p)
		rel = filepath.ToSlash(rel)
		if !strings.Contains(rel, "/") && keep != nil && keep(rel) {
			if d.IsDir() {
				return fs.SkipDir
			}
			return nil
		}
		if !want[rel] {
			stale = append(stale, p)
			if d.IsDir() {
				return fs.SkipDir
			}
			return nil
		}
		if _, isFile := files[rel]; isFile == d.IsDir() || d.Type()&fs.ModeSymlink != 0 {
			stale = append(stale, p)
			if d.IsDir() {
				return fs.SkipDir
			}
		}
		return nil
	})
	if err != nil {
		return err
	}
	for _, p := range stale {
		if err := os.RemoveAll(p); err != nil {
			return err
		}
	}
	for p, b := range files {
		full := filepath.Join(dir, filepath.FromSlash(p))
		if old, err := os.ReadFile(full); err == nil && bytes.Equal(old, b) {
			continue
		}
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(full, b, 0o644); err != nil {
			return err
		}
	}
	return nil
}

// copyTree copies the regular files and directories of src into dst (which must not exist).
func copyTree(src, dst string) error {
	return filepath.WalkDir(src, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(src, p)
		target := filepath.Join(dst, rel)
		if d.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		if !d.Type().IsRegular() {
			return nil
		}
		in, err := os.Open(p)
		if err != nil {
			return err
		}
		defer in.Close()
		out, err := os.OpenFile(target, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0o644)
		if err != nil {
			return err
		}
		if _, err := io.Copy(out, in); err != nil {
			out.Close()
			return err
		}
		return out.Close()
	})
}

// frameworkBase materializes the framework in the cache (<cache>/v1/framework/<sha>) and
// builds its Janus library there once. Every use re-synchronises the sources with the
// framework's bytes first, so a damaged copy is repaired before Lake decides what to rebuild.
func (fw *framework) frameworkBase(lake string, progress io.Writer) (string, error) {
	dir := filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])
	if err := os.MkdirAll(filepath.Dir(dir), 0o755); err != nil {
		return "", &diag{Invalid: true, Msg: "Cannot create the Janus cache: " + err.Error(), Stage: "Janus library build",
			Next: "Set JANUS_CACHE_DIR to a writable directory."}
	}
	lk, err := lockFile(dir+".lock", true)
	if err != nil {
		return "", &diag{Invalid: true, Msg: "Cannot lock the Janus cache: " + err.Error(), Stage: "Janus library build"}
	}
	defer lk.unlock()
	if err := syncTree(dir, fw.Files, func(top string) bool { return top == ".lake" }); err != nil {
		return "", &diag{Invalid: true, Msg: "Cannot write the Janus framework to the cache: " + err.Error(), Stage: "Janus library build",
			Next: "Set JANUS_CACHE_DIR to a writable directory."}
	}
	if _, err := os.Stat(filepath.Join(dir, ".lake", "build", "lib", "lean", "Janus.olean")); err != nil && progress != nil {
		fmt.Fprintf(progress, "Building the Janus framework (%s, %s) in %s; this happens once per framework version.\n",
			fw.Source, fw.Sha256[:12], displayPath(dir))
	}
	lr := &leanRunner{lake: lake, root: dir}
	if out, err := lr.run("build", "Janus", "Janus.Tools.Audit"); err != nil {
		return "", &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(), Stage: "Janus library build",
			Next: "Run lake build Janus in " + dir + " and fix the reported errors.", Details: out}
	}
	now := time.Now()
	_ = os.Chtimes(dir, now, now)
	return dir, nil
}

// libraryRoot is the Lake project in which the Janus library is built and proofs are
// compiled: the checkout for a directory framework (built in place, as before), else the
// cached copy of the embedded framework. With fresh, the embedded framework is built from
// scratch in a temporary directory that cleanup removes.
func (fw *framework) libraryRoot(lake string, fresh bool, progress io.Writer) (string, func(), error) {
	if fw.Source == "directory" {
		// Build the library and the trusted auditor in place (as the old verifier did).
		lr := &leanRunner{lake: lake, root: fw.Dir}
		if out, err := lr.run("build", "Janus", "Janus.Tools.Audit"); err != nil {
			return "", func() {}, &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(),
				Stage: "Janus library build", Next: "Run lake build Janus Janus.Tools.Audit in " + fw.Dir + ".", Details: out}
		}
		return fw.Dir, func() {}, nil
	}
	if !fresh {
		dir, err := fw.frameworkBase(lake, progress)
		return dir, func() {}, err
	}
	tmp, err := fw.freshBase(lake, progress)
	if err != nil {
		return "", func() {}, err
	}
	return tmp, func() { os.RemoveAll(tmp) }, nil
}

// freshBase builds the framework in a new temporary directory, reusing nothing.
func (fw *framework) freshBase(lake string, progress io.Writer) (string, error) {
	parent := filepath.Join(cacheRoot(), "v1", "tmp")
	_ = os.MkdirAll(parent, 0o755)
	tmp, err := os.MkdirTemp(parent, "fresh-")
	if err != nil {
		return "", &diag{Invalid: true, Msg: "Cannot create a build directory: " + err.Error(), Stage: "Janus library build",
			Next: "Set JANUS_CACHE_DIR to a writable directory."}
	}
	if err := syncTree(tmp, fw.Files, nil); err != nil {
		os.RemoveAll(tmp)
		return "", &diag{Invalid: true, Msg: err.Error(), Stage: "Janus library build"}
	}
	if progress != nil {
		fmt.Fprintf(progress, "Building the Janus framework from scratch (--fresh) in %s.\n", displayPath(tmp))
	}
	lr := &leanRunner{lake: lake, root: tmp}
	if out, err := lr.run("build", "Janus", "Janus.Tools.Audit"); err != nil {
		os.RemoveAll(tmp)
		return "", &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(), Stage: "Janus library build", Details: out}
	}
	return tmp, nil
}

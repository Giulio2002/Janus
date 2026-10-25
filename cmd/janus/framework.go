package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
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
func copyTree(src, dst string) error { return copyTreeSkipTop(src, dst) }

// copyTreeSkipTop is copyTree without the top-level entries of src named in skip.
func copyTreeSkipTop(src, dst string, skip ...string) error {
	return filepath.WalkDir(src, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(src, p)
		for _, s := range skip {
			if rel == s {
				if d.IsDir() {
					return fs.SkipDir
				}
				return nil
			}
		}
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
		// keep the permission bits (an executable such as the compiled auditor stays one)
		mode := os.FileMode(0o644)
		if info, err := d.Info(); err == nil {
			mode = info.Mode().Perm()
		}
		out, err := os.OpenFile(target, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, mode)
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

// The framework build is shared by every janus process on the machine: the cached base
// (<cache>/v1/framework/<sha>) for the embedded framework, the checkout itself for a directory
// framework. A verification pins that build's compiled modules and re-checks them after every
// step, so nothing may write to it while a verification uses it. Every user therefore holds a
// shared lock on it for as long as it reads it (a verification: until it ends), and every writer
// (the sync and Lake build below, `janus blockers`' decoder build, cache eviction) holds the
// exclusive lock. A writer records what it built in a ready stamp; a reader whose sources and
// compiled modules match the stamp uses the build without writing anything, so concurrent
// verifications never wait for each other, and any other change to the build still fails the
// pins ("framework integrity").

// baseTargets are the Lake targets every framework build has: the library, the auditor module
// (for the consumer path's Audit.lean) and the compiled auditor executable janus verify runs.
var baseTargets = []string{"Janus", "Janus.Tools.Audit", auditExeTarget}

// auditExeTarget is the Lake target of the compiled auditor (Janus/Tools/AuditMain.lean).
const auditExeTarget = "janus-audit"

// auditExePath is the compiled auditor in the framework build dir.
func auditExePath(dir string) string {
	return filepath.Join(dir, ".lake", "build", "bin", auditExeTarget)
}

// regularFileSha is the SHA-256 of a regular file ("" if it cannot be read).
func regularFileSha(p string) string {
	f, err := os.Open(p)
	if err != nil {
		return ""
	}
	defer f.Close()
	if st, err := f.Stat(); err != nil || !st.Mode().IsRegular() {
		return ""
	}
	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		return ""
	}
	return hex.EncodeToString(h.Sum(nil))
}

// frameworkStamp is the ready stamp of a framework build.
type frameworkStamp struct {
	Sha256   string   `json:"sha256"`   // frameworkSha of the sources built
	Manifest string   `json:"manifest"` // SHA-256 of their lake-manifest.json (not in Sha256)
	Targets  []string `json:"targets"`  // the Lake targets built
	Pins     pins     `json:"pins"`     // the framework modules' data files as built
	AuditExe string   `json:"auditExe"` // SHA-256 of the compiled auditor as built
}

// stampedAuditExe is the auditor executable's SHA-256 recorded in the ready stamp of the build
// in dir ("" if there is none). The caller holds the build's lease, so the stamp is stable.
func (fw *framework) stampedAuditExe(dir string) string {
	_, stampPath := fw.buildPaths(dir)
	b, err := os.ReadFile(stampPath)
	if err != nil {
		return ""
	}
	var st frameworkStamp
	if json.Unmarshal(b, &st) != nil {
		return ""
	}
	return st.AuditExe
}

// frameworkLease is a framework build in use: release ends the use (drops the shared lock).
type frameworkLease struct {
	dir string
	lk  *fileLock
}

func (l *frameworkLease) release() {
	if l != nil {
		l.lk.unlock()
	}
}

// buildPaths are the lock and ready-stamp files of the framework build in dir: next to the
// cached base, inside .lake/ of a directory framework (the checkout).
func (fw *framework) buildPaths(dir string) (lockPath, stampPath string) {
	if fw.Source == "directory" {
		return filepath.Join(dir, ".lake", "janus-framework.lock"), filepath.Join(dir, ".lake", "janus-framework.ready")
	}
	return dir + ".lock", dir + ".ready"
}

// ready reports whether the build in dir is complete for targets and untouched since its
// writer stamped it: the sources are exactly the framework's (embedded framework), the stamp is
// for these sources and targets, and every framework module's data files hash as stamped.
func (fw *framework) ready(dir string, targets []string) bool {
	_, stampPath := fw.buildPaths(dir)
	b, err := os.ReadFile(stampPath)
	if err != nil {
		return false
	}
	var st frameworkStamp
	if json.Unmarshal(b, &st) != nil || st.Sha256 != fw.Sha256 || st.Manifest != sha256Hex(fw.Files["lake-manifest.json"]) {
		return false
	}
	have := map[string]bool{}
	for _, t := range st.Targets {
		have[t] = true
	}
	for _, t := range targets {
		if !have[t] {
			return false
		}
	}
	if dir != fw.Dir && !sameTree(dir, fw.Files, func(top string) bool { return top == ".lake" }) {
		return false
	}
	p, err := frameworkPins(filepath.Join(dir, ".lake", "build", "lib", "lean"), fw.Files)
	if err != nil || len(p.want) == 0 || len(diffPins(st.Pins, p.want)) > 0 {
		return false
	}
	if _, ok := p.want["Janus.olean"]; !ok {
		return false
	}
	// The compiled auditor must be the one the stamped build produced.
	return st.AuditExe != "" && regularFileSha(auditExePath(dir)) == st.AuditExe
}

// acquire returns the framework build in dir, built for targets, under a shared lock. If it is
// not ready it takes the exclusive lock, synchronises the sources (embedded framework), runs
// Lake, stamps the result and goes back to the shared lock.
func (fw *framework) acquire(dir, lake string, targets []string, progress io.Writer) (*frameworkLease, error) {
	lockPath, stampPath := fw.buildPaths(dir)
	if err := os.MkdirAll(filepath.Dir(lockPath), 0o755); err != nil {
		return nil, &diag{Invalid: true, Msg: "Cannot create the Janus cache: " + err.Error(), Stage: "Janus library build",
			Next: "Set JANUS_CACHE_DIR to a writable directory."}
	}
	lockErr := func(err error) error {
		return &diag{Invalid: true, Msg: "Cannot lock the Janus framework build: " + err.Error(), Stage: "Janus library build"}
	}
	lk, err := lockFileMode(lockPath, true, true)
	if err != nil {
		return nil, lockErr(err)
	}
	for attempt := 0; ; attempt++ {
		if fw.ready(dir, targets) {
			if dir != fw.Dir {
				gcPin(dir)
				touchUse(dir, lockPath)
			}
			return &frameworkLease{dir: dir, lk: lk}, nil
		}
		if attempt == 3 {
			lk.unlock()
			return nil, &diag{Invalid: true, Stage: "Janus library build",
				Msg:  "The Janus framework build in " + displayPath(dir) + " keeps changing after it is built.",
				Next: "Another program writes to it; stop it, or set JANUS_CACHE_DIR to a private directory."}
		}
		// Writer: drop the shared lock, take the exclusive one, (re)build.
		lk.unlock()
		if lk, err = lockFileMode(lockPath, false, true); err != nil {
			return nil, lockErr(err)
		}
		if !fw.ready(dir, targets) {
			if err := fw.build(dir, lake, targets, stampPath, progress); err != nil {
				lk.unlock()
				return nil, err
			}
		}
		if err := lk.share(); err != nil {
			lk.unlock()
			return nil, lockErr(err)
		}
	}
}

// build runs with the exclusive lock held: sync the sources (embedded framework), build the
// stamped targets plus targets with Lake, and write the new stamp.
func (fw *framework) build(dir, lake string, targets []string, stampPath string, progress io.Writer) error {
	// Build every target a previous writer built too, so the stamp never shrinks.
	var old frameworkStamp
	if b, err := os.ReadFile(stampPath); err == nil {
		_ = json.Unmarshal(b, &old)
	}
	if err := os.Remove(stampPath); err != nil && !os.IsNotExist(err) {
		return &diag{Invalid: true, Msg: "Cannot reset the framework build stamp: " + err.Error(), Stage: "Janus library build"}
	}
	// Lake does not re-hash its outputs, so a framework module whose data files no longer match
	// the stamp (written by something other than a stamped build) would be left as it is. Remove
	// such modules' outputs so that Lake compiles them again from the sources.
	libDir := filepath.Join(dir, ".lake", "build", "lib", "lean")
	if old.Sha256 == fw.Sha256 && len(old.Pins) > 0 {
		if now, err := frameworkPins(libDir, fw.Files); err == nil {
			for _, m := range changedModules(old.Pins, now.want) {
				removeModuleOutputs(libDir, m)
			}
		}
	}
	// Likewise an auditor executable that is not the stamped one: remove it and Lake's records
	// of it, so that Lake links it again.
	if exe := auditExePath(dir); old.AuditExe != "" && regularFileSha(exe) != old.AuditExe {
		for _, ext := range []string{"", ".hash", ".trace", ".rsp"} {
			_ = os.Remove(exe + ext)
		}
	}
	// A copy (the cached base of the embedded framework, or of a --janus-root checkout for a
	// consumer workspace) gets the framework's sources first; a checkout is built in place.
	if dir != fw.Dir {
		if err := syncTree(dir, fw.Files, func(top string) bool { return top == ".lake" }); err != nil {
			return &diag{Invalid: true, Msg: "Cannot write the Janus framework to the cache: " + err.Error(), Stage: "Janus library build",
				Next: "Set JANUS_CACHE_DIR to a writable directory."}
		}
		if _, err := os.Stat(filepath.Join(dir, ".lake", "build", "lib", "lean", "Janus.olean")); err != nil && progress != nil {
			fmt.Fprintf(progress, "Building the Janus framework (%s, %s) in %s; this happens once per framework version.\n",
				fw.Source, fw.Sha256[:12], displayPath(dir))
		}
	}
	all := append([]string{}, baseTargets...)
	seen := map[string]bool{}
	for _, t := range all {
		seen[t] = true
	}
	for _, t := range append(old.Targets, targets...) {
		if !seen[t] {
			seen[t] = true
			all = append(all, t)
		}
	}
	lr := &leanRunner{lake: lake, root: dir}
	if out, err := lr.run(append([]string{"build"}, all...)...); err != nil {
		next := "Run lake build " + strings.Join(all, " ") + " in " + dir + " and fix the reported errors."
		return &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(), Stage: "Janus library build",
			Next: next, Details: out}
	}
	// Round 10 F1: the stamp says "built from fw.Files". Lake compiled whatever the sources were
	// while it ran; a checkout built in place (--janus-root) can change under it (a git checkout
	// in another terminal). Stamping that build would let a later run with fw's sources reuse
	// modules compiled from others, and report fw's SHA-256 for them.
	if dir == fw.Dir {
		now, err := readFramework(os.DirFS(dir))
		if err != nil || frameworkSha(now) != fw.Sha256 || !bytes.Equal(now["lake-manifest.json"], fw.Files["lake-manifest.json"]) {
			return &diag{Invalid: true, Stage: "Janus library build",
				Msg:  "The Janus framework sources in " + displayPath(dir) + " changed while they were being built; the build is not used.",
				Next: "Rerun janus verify once the checkout is no longer changing."}
		}
	} else if !sameTree(dir, fw.Files, func(top string) bool { return top == ".lake" }) {
		return &diag{Invalid: true, Stage: "Janus library build",
			Msg:  "The Janus framework sources in " + displayPath(dir) + " changed while they were being built; the build is not used.",
			Next: "Another program writes to the cache; stop it, or set JANUS_CACHE_DIR to a private directory."}
	}
	p, err := frameworkPins(filepath.Join(dir, ".lake", "build", "lib", "lean"), fw.Files)
	if err != nil {
		return &diag{Invalid: true, Msg: "Cannot read the framework build: " + err.Error(), Stage: "Janus library build"}
	}
	exeSha := regularFileSha(auditExePath(dir))
	if exeSha == "" {
		return &diag{Invalid: true, Msg: "The framework build has no auditor executable " + displayPath(auditExePath(dir)) + ".", Stage: "Janus library build",
			Next: "Run lake build " + auditExeTarget + " in " + dir + " and fix the reported errors."}
	}
	st := frameworkStamp{Sha256: fw.Sha256, Manifest: sha256Hex(fw.Files["lake-manifest.json"]), Targets: all, Pins: p.want, AuditExe: exeSha}
	b, _ := json.Marshal(st)
	if err := writeFileAtomic(stampPath, b); err != nil {
		return &diag{Invalid: true, Msg: "Cannot write the framework build stamp: " + err.Error(), Stage: "Janus library build"}
	}
	if dir != fw.Dir {
		touchUse(dir)
	}
	return nil
}

// changedModules are the modules with a data file that differs between want and got (modified,
// missing or extra).
func changedModules(want, got pins) []string {
	set := map[string]bool{}
	for rel, h := range want {
		if got[rel] != h {
			set[moduleOfRel(rel)] = true
		}
	}
	for rel := range got {
		if _, ok := want[rel]; !ok {
			set[moduleOfRel(rel)] = true
		}
	}
	var ms []string
	for m := range set {
		ms = append(ms, m)
	}
	sort.Strings(ms)
	return ms
}

// removeModuleOutputs removes every build output of module m in libDir (its module data, .ilean,
// Lake's .trace and .hash files), so the next Lake build compiles it again.
func removeModuleOutputs(libDir, m string) {
	base := filepath.Join(libDir, filepath.FromSlash(strings.ReplaceAll(m, ".", "/")))
	ents, err := os.ReadDir(filepath.Dir(base))
	if err != nil {
		return
	}
	prefix := filepath.Base(base) + "."
	for _, e := range ents {
		if !e.IsDir() && strings.HasPrefix(e.Name(), prefix) {
			_ = os.Remove(filepath.Join(filepath.Dir(base), e.Name()))
		}
	}
}

// writeFileAtomic writes b to p through a temporary file and a rename.
func writeFileAtomic(p string, b []byte) error {
	f, err := os.CreateTemp(filepath.Dir(p), "."+filepath.Base(p)+".tmp-")
	if err != nil {
		return err
	}
	if _, err := f.Write(b); err != nil {
		f.Close()
		os.Remove(f.Name())
		return err
	}
	if err := f.Close(); err != nil {
		os.Remove(f.Name())
		return err
	}
	if err := os.Rename(f.Name(), p); err != nil {
		os.Remove(f.Name())
		return err
	}
	return nil
}

// sameTree is syncTree's read-only check: dir holds exactly files (plus keep's top-level
// entries), byte for byte.
func sameTree(dir string, files map[string][]byte, keep func(top string) bool) bool {
	n := 0
	ok := true
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
		if d.IsDir() {
			return nil
		}
		want, isFile := files[rel]
		if !isFile || !d.Type().IsRegular() {
			ok = false
			return fs.SkipAll
		}
		got, err := os.ReadFile(p)
		if err != nil || !bytes.Equal(got, want) {
			ok = false
			return fs.SkipAll
		}
		n++
		return nil
	})
	return err == nil && ok && n == len(files)
}

// frameworkBase materializes the framework in the cache (<cache>/v1/framework/<sha>), builds
// its Janus library (and targets) there once, and returns it under a shared lock (see above). A
// damaged copy (sources or compiled modules not as stamped) is repaired before use.
func (fw *framework) frameworkBase(lake string, progress io.Writer, targets ...string) (*frameworkLease, error) {
	dir := filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])
	return fw.acquire(dir, lake, targets, progress)
}

// libraryRoot is the Lake project in which the Janus library is built and proofs are
// compiled: the checkout for a directory framework (built in place, as before), else the
// cached copy of the embedded framework. With fresh, the embedded framework is built from
// scratch in a temporary directory that cleanup removes. cleanup also ends the use of a shared
// build (its shared lock), so it must run only after the last check of the framework pins.
func (fw *framework) libraryRoot(lake string, fresh bool, progress io.Writer) (string, func(), error) {
	if err := checkCacheRoot(); err != nil {
		return "", func() {}, err
	}
	if fw.Source == "directory" || !fresh {
		dir := fw.Dir
		var lease *frameworkLease
		var err error
		if fw.Source == "directory" {
			lease, err = fw.acquire(dir, lake, nil, progress)
		} else {
			lease, err = fw.frameworkBase(lake, progress)
		}
		if err != nil {
			return "", func() {}, err
		}
		return lease.dir, lease.release, nil
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
	if out, err := lr.run(append([]string{"build"}, baseTargets...)...); err != nil {
		os.RemoveAll(tmp)
		return "", &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(), Stage: "Janus library build", Details: out}
	}
	return tmp, nil
}

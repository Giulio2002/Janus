package main

// Consumer packages: proofs that live in the user's own Lake package, which depends on the
// `janus` Lean library. See docs/CONSUMERS.md for what is checked and what is reused.

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
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

type fileHash struct {
	Path   string `json:"path"`
	Sha256 string `json:"sha256"`
}

type dependencyInfo struct {
	Name     string `json:"name"`
	Type     string `json:"type"` // "git" or "path"
	URL      string `json:"url,omitempty"`
	Rev      string `json:"rev,omitempty"`
	InputRev string `json:"inputRev,omitempty"`
	Dir      string `json:"dir"` // the checkout that was compared with the framework (janus) or copied (others)
	// Extra dependencies only:
	SubDir    string `json:"subDir,omitempty"`
	Inherited bool   `json:"inherited,omitempty"` // required by another dependency, not by the consumer
	Sha256    string `json:"sha256,omitempty"`    // tree hash of the files copied into the workspace
	Files     int    `json:"files,omitempty"`     // number of files copied
}

func (d dependencyInfo) describe() string {
	if d.Type == "git" {
		s := "git " + d.URL + " @ " + d.Rev
		if d.SubDir != "" {
			s += " (subDir " + d.SubDir + ")"
		}
		return s
	}
	return "path " + d.Dir
}

// consumerInfo is the consumer package's record in verified.json.
type consumerInfo struct {
	Root           string         `json:"root"`
	Lakefile       string         `json:"lakefile"`
	Module         string         `json:"module"`
	SnapshotSha256 string         `json:"snapshotSha256"`
	Files          []fileHash     `json:"files"`
	Dependency     dependencyInfo `json:"dependency"`
	// Dependencies are the package's other Lake dependencies (transitively), each pinned and
	// copied as recorded; empty for a janus-only package.
	Dependencies  []dependencyInfo `json:"dependencies"`
	AllowPathDeps bool             `json:"allowPathDeps,omitempty"`
	Workspace     string           `json:"workspace"`
	Rebuilt       []string         `json:"rebuilt"`
}

type lakeManifest struct {
	Version     json.RawMessage `json:"version"`
	PackagesDir string          `json:"packagesDir"`
	Packages    []lakeEntry     `json:"packages"`
	Name        string          `json:"name"`
	LakeDir     string          `json:"lakeDir"`
}

type lakeEntry struct {
	Type      string  `json:"type"`
	Name      string  `json:"name"`
	URL       string  `json:"url"`
	Rev       string  `json:"rev"`
	InputRev  *string `json:"inputRev"`
	SubDir    *string `json:"subDir"`
	Dir       string  `json:"dir"`
	Inherited bool    `json:"inherited"`
}

// consumerPkg is a validated consumer package and the snapshot of its sources.
type consumerPkg struct {
	Root     string
	Lakefile string
	Dep      dependencyInfo
	Deps     []*extraDep       // other dependencies, in manifest order
	Files    map[string][]byte // snapshot: slash path relative to Root -> bytes
	Sha256   string
	excluded []string // absolute directories left out of the snapshot
	opts     loadOpts
}

func (pkg *consumerPkg) depInfos() []dependencyInfo {
	out := []dependencyInfo{}
	for _, d := range pkg.Deps {
		out = append(out, d.Info)
	}
	return out
}

var fullRevRE = regexp.MustCompile(`^[0-9a-f]{40}$`)

// Directories never copied from a consumer package.
var skippedDirs = map[string]bool{".lake": true, ".git": true, "artifacts": true, "generated": true, "bin": true, "obj": true}

func isSourceFile(name string) bool {
	return strings.HasSuffix(name, ".lean") || strings.HasSuffix(name, ".toml") || strings.HasSuffix(name, ".json") || name == "lean-toolchain"
}

func pkgDiag(stage, msg, next string) error {
	return &diag{Invalid: true, Msg: msg, Stage: stage, Next: next}
}

// loadConsumer checks that root is a resolved Lake package depending on the framework fw (and
// on other packages only as permitted, see deps.go), with fw's toolchain, and takes a snapshot
// of its sources and of every other dependency. Directories in exclude (artifact outputs) are
// left out of the snapshot.
func loadConsumer(root string, fw *framework, exclude []string, lo loadOpts) (*consumerPkg, error) {
	abs, err := filepath.Abs(root)
	if err != nil {
		return nil, err
	}
	if real, err := filepath.EvalSymlinks(abs); err == nil {
		abs = real
	}
	st, err := os.Stat(abs)
	if err != nil || !st.IsDir() {
		return nil, pkgDiag("consumer package", fmt.Sprintf("%s is not a directory.", displayPath(root)),
			"Pass --proof-root pointing at the Lake package that contains the proof (janus init creates one).")
	}
	pkg := &consumerPkg{Root: abs, opts: lo}
	for _, e := range exclude {
		if a, err := filepath.Abs(e); err == nil {
			if r, err := filepath.EvalSymlinks(a); err == nil {
				a = r
			}
			pkg.excluded = append(pkg.excluded, a)
		}
	}

	// Lake configuration.
	_, tomlErr := os.Stat(filepath.Join(abs, "lakefile.toml"))
	_, leanErr := os.Stat(filepath.Join(abs, "lakefile.lean"))
	switch {
	case tomlErr == nil && leanErr == nil:
		return nil, pkgDiag("consumer package", fmt.Sprintf("%s has both lakefile.toml and lakefile.lean.", displayPath(abs)),
			"Keep exactly one Lake configuration file.")
	case tomlErr == nil:
		pkg.Lakefile = "lakefile.toml"
	case leanErr == nil:
		pkg.Lakefile = "lakefile.lean"
	default:
		return nil, pkgDiag("consumer package", fmt.Sprintf("%s has no lakefile.toml or lakefile.lean.", displayPath(abs)),
			"Pass --proof-root pointing at the root of a Lake package (janus init creates one).")
	}

	// Toolchain.
	tc, err := os.ReadFile(filepath.Join(abs, "lean-toolchain"))
	if err != nil {
		return nil, pkgDiag("toolchain", fmt.Sprintf("%s has no lean-toolchain file.", displayPath(abs)),
			fmt.Sprintf("Write %q to %s.", fw.Toolchain, filepath.Join(displayPath(abs), "lean-toolchain")))
	}
	if got := strings.TrimSpace(string(tc)); got != fw.Toolchain {
		return nil, pkgDiag("toolchain", fmt.Sprintf("The consumer package uses toolchain %s, the Janus framework uses %s.", got, fw.Toolchain),
			fmt.Sprintf("Set lean-toolchain to %s (the toolchain of the janus dependency) and rerun lake update.", fw.Toolchain))
	}

	// Manifest: resolved, janus pinned; any other dependency pinned and clean (deps.go).
	mpath := filepath.Join(abs, "lake-manifest.json")
	mb, err := os.ReadFile(mpath)
	if err != nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("%s has no lake-manifest.json; its dependencies are not resolved.", displayPath(abs)),
			"Run lake update in "+displayPath(abs)+".")
	}
	var man lakeManifest
	if err := json.Unmarshal(mb, &man); err != nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("Cannot parse %s: %v", displayPath(mpath), err), "Run lake update in "+displayPath(abs)+".")
	}
	var dep *lakeEntry
	var others []lakeEntry
	seen := map[string]bool{}
	for i, e := range man.Packages {
		if seen[e.Name] {
			return nil, pkgDiag("consumer manifest", fmt.Sprintf("lake-manifest.json lists %s twice.", e.Name), "Run lake update in "+displayPath(abs)+".")
		}
		seen[e.Name] = true
		if e.Name != "janus" {
			others = append(others, e)
			continue
		}
		dep = &man.Packages[i]
	}
	pkgsDir := man.PackagesDir
	if pkgsDir == "" {
		pkgsDir = ".lake/packages"
	}
	if filepath.IsAbs(pkgsDir) || strings.HasPrefix(path.Clean(filepath.ToSlash(pkgsDir)), "..") {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("lake-manifest.json has packagesDir %q outside the package.", pkgsDir), "Use the default .lake/packages.")
	}
	if dep == nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("%s does not list janus; the package does not depend on the Janus library.", displayPath(mpath)),
			"Require janus in the lakefile (see docs/CONSUMERS.md) and run lake update.")
	}
	info := dependencyInfo{Name: "janus", Type: dep.Type}
	switch dep.Type {
	case "git":
		info.URL, info.Rev = dep.URL, dep.Rev
		if dep.InputRev != nil {
			info.InputRev = *dep.InputRev
		}
		if !fullRevRE.MatchString(dep.Rev) || info.InputRev != dep.Rev {
			pinned := info.InputRev
			if pinned == "" {
				pinned = "(none)"
			}
			return nil, pkgDiag("consumer manifest", fmt.Sprintf("janus is not pinned to a full revision: the lakefile asks for %s.", pinned),
				"Require janus with rev = \"<40-hex commit>\" (janus framework prints the commit this verifier carries) and run lake update janus.")
		}
		if dep.SubDir != nil && *dep.SubDir != "" {
			return nil, pkgDiag("consumer manifest", "The janus dependency uses a subDir; the framework is the repository root.", "Require janus without subDir.")
		}
		info.Dir = filepath.Join(abs, filepath.FromSlash(pkgsDir), "janus")
		if _, err := os.Stat(info.Dir); err != nil {
			return nil, pkgDiag("consumer manifest", fmt.Sprintf("The janus dependency is not checked out at %s.", displayPath(info.Dir)),
				"Run lake update janus (or lake build) in "+displayPath(abs)+".")
		}
		if _, err := os.Stat(filepath.Join(info.Dir, ".git")); err == nil {
			head, err := exec.Command("git", "-C", info.Dir, "rev-parse", "HEAD").Output()
			if err != nil || strings.TrimSpace(string(head)) != dep.Rev {
				return nil, pkgDiag("consumer manifest", fmt.Sprintf("The janus checkout %s is at %s, lake-manifest.json pins %s.",
					displayPath(info.Dir), strings.TrimSpace(string(head)), dep.Rev), "Run lake update janus in "+displayPath(abs)+".")
			}
		}
	case "path":
		info.Dir = filepath.FromSlash(dep.Dir)
		if !filepath.IsAbs(info.Dir) {
			info.Dir = filepath.Join(abs, info.Dir)
		}
		info.Dir = filepath.Clean(info.Dir)
	default:
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("Unsupported janus dependency type %q.", dep.Type), "Require janus from git (or a local path).")
	}
	pkg.Dep = info

	// The dependency must be exactly the framework this verifier builds against.
	if err := compareFramework(info.Dir, fw); err != nil {
		return nil, err
	}
	if rel, err := filepath.Rel(abs, info.Dir); err == nil && !strings.HasPrefix(rel, "..") {
		pkg.excluded = append(pkg.excluded, info.Dir)
	}

	// Every other dependency: pinned, clean and snapshotted (deps.go).
	for _, e := range others {
		d, err := loadExtraDep(abs, pkgsDir, e, lo)
		if err != nil {
			return nil, err
		}
		pkg.Deps = append(pkg.Deps, d)
		if rel, err := filepath.Rel(abs, d.pkgDir); err == nil && !strings.HasPrefix(rel, "..") && rel != "." {
			pkg.excluded = append(pkg.excluded, d.pkgDir)
		}
	}

	if err := pkg.snapshot(); err != nil {
		return nil, err
	}
	if _, ok := pkg.Files["Extracted.lean"]; ok {
		return nil, pkgDiag("consumer package", "The consumer package contains Extracted.lean; that module name is reserved for the extraction being verified.",
			"Remove or rename "+filepath.Join(displayPath(abs), "Extracted.lean")+"; janus verify supplies Extracted from the artifact directory.")
	}
	return pkg, nil
}

// compareFramework byte-compares the framework files of the dependency checkout with fw,
// allowing LF/CRLF differences.
func compareFramework(dir string, fw *framework) error {
	dep, err := readFramework(os.DirFS(dir))
	if err != nil {
		return pkgDiag("framework identity", fmt.Sprintf("Cannot read the janus dependency at %s: %v", displayPath(dir), err),
			"Run lake update janus in the consumer package.")
	}
	var problems []string
	var paths []string
	for p := range fw.Files {
		if isIdentityFile(p) {
			paths = append(paths, p)
		}
	}
	sort.Strings(paths)
	for _, p := range paths {
		b, ok := dep[p]
		switch {
		case !ok:
			problems = append(problems, "missing "+p)
		case !bytes.Equal(normalizeEOL(b), normalizeEOL(fw.Files[p])):
			problems = append(problems, "differs "+p)
		}
	}
	var extra []string
	for p := range dep {
		if _, ok := fw.Files[p]; !ok && isIdentityFile(p) {
			extra = append(extra, "extra "+p)
		}
	}
	sort.Strings(extra)
	problems = append(problems, extra...)
	if len(problems) == 0 {
		return nil
	}
	shown := problems
	if len(shown) > 8 {
		shown = append(append([]string{}, shown[:8]...), fmt.Sprintf("… and %d more", len(problems)-8))
	}
	want := "the framework embedded in this janus binary"
	if fw.Source == "directory" {
		want = "the framework at " + displayPath(fw.Dir)
	}
	next := "Pin janus to the revision this verifier carries (janus framework prints it) and run lake update janus, or verify with a janus built from the pinned revision."
	if rev, modified, _ := buildRevision(); fw.Source == "embedded" && rev != "" && !modified {
		next = "Pin janus to " + rev + " (the revision this verifier carries) and run lake update janus, or verify with a janus built from the pinned revision."
	}
	return &diag{Invalid: true, Stage: "framework identity", Next: next,
		Msg: fmt.Sprintf("The janus dependency at %s does not match %s (SHA-256 %s):\n  %s",
			displayPath(dir), want, fw.Sha256, strings.Join(shown, "\n  "))}
}

// snapshot reads the package's Lean sources, Lake configuration, JSON and toolchain files.
func (pkg *consumerPkg) snapshot() error {
	files, err := snapshotDir(pkg.Root, pkg.excluded)
	if err != nil {
		return err
	}
	pkg.Files = files
	pkg.Sha256 = treeSha(files)
	return nil
}

// snapshotDir reads the Lean sources, Lake configuration, JSON and toolchain files under root,
// skipping build/VCS/artifact directories, dotfiles and the excluded directories.
func snapshotDir(root string, excluded []string) (map[string][]byte, error) {
	files := map[string][]byte{}
	err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if p == root {
			return nil
		}
		name := d.Name()
		if d.IsDir() {
			if skippedDirs[name] || strings.HasPrefix(name, ".") {
				return fs.SkipDir
			}
			for _, e := range excluded {
				if p == e {
					return fs.SkipDir
				}
			}
			return nil
		}
		rel, _ := filepath.Rel(root, p)
		rel = filepath.ToSlash(rel)
		if d.Type()&fs.ModeSymlink != 0 {
			if isSourceFile(name) {
				return pkgDiag("consumer package", fmt.Sprintf("%s is a symbolic link; consumer sources must be regular files.", rel),
					"Replace the link with the file it points to.")
			}
			if fi, err := os.Stat(p); err == nil && fi.IsDir() {
				return pkgDiag("consumer package", fmt.Sprintf("%s is a symbolic link to a directory; consumer sources must be regular files.", rel),
					"Replace the link with the directory, or move it out of the package.")
			}
			return nil
		}
		if !d.Type().IsRegular() || !isSourceFile(name) {
			return nil
		}
		b, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		files[rel] = b
		return nil
	})
	if err != nil {
		if _, ok := err.(*diag); ok {
			return nil, err
		}
		return nil, pkgDiag("consumer package", "Cannot read the consumer package: "+err.Error(), "")
	}
	return files, nil
}

func treeSha(files map[string][]byte) string {
	var paths []string
	for p := range files {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	h := sha256.New()
	for _, p := range paths {
		fmt.Fprintf(h, "%s  %s\n", sha256Hex(files[p]), p)
	}
	return hex.EncodeToString(h.Sum(nil))
}

func (pkg *consumerPkg) fileHashes() []fileHash {
	var out []fileHash
	for p, b := range pkg.Files {
		out = append(out, fileHash{p, sha256Hex(b)})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Path < out[j].Path })
	return out
}

// proofRel is the proof's path inside the snapshot, or a diagnostic.
func (pkg *consumerPkg) proofRel(proof string) (string, error) {
	abs, err := filepath.Abs(proof)
	if err == nil {
		if r, err := filepath.EvalSymlinks(abs); err == nil {
			abs = r
		}
	}
	rel, err := filepath.Rel(pkg.Root, abs)
	if err != nil || strings.HasPrefix(rel, "..") {
		return "", pkgDiag("proof selection", fmt.Sprintf("The proof %s is not inside the consumer package %s.", displayPath(proof), displayPath(pkg.Root)),
			"Pass a --proof inside --proof-root.")
	}
	rel = filepath.ToSlash(rel)
	if _, ok := pkg.Files[rel]; !ok || !strings.HasSuffix(rel, ".lean") {
		return "", pkgDiag("proof selection", fmt.Sprintf("The proof %s is not a Lean source of the consumer package (it is missing, or in an excluded directory such as .lake or artifacts).", displayPath(proof)),
			"Pass a .lean file of the package.")
	}
	return rel, nil
}

// consumerWS is a Lake workspace in the support cache: root/ holds the consumer snapshot,
// janus/ the framework plus the selected Extracted module. Its build directories persist,
// so Lake only rebuilds modules whose inputs changed.
type consumerWS struct {
	Dir, Root, JanusDir string
	DepsDir             string // deps/<name>: the copied extra dependencies
	lake                string
	sb                  *sandbox
	tc                  *toolchain
	lock                *fileLock
	temp                bool
	janusFiles          map[string][]byte // what janus/ must contain: framework + Extracted
	// pins are the SHA-256 of every module-data file of janus/.lake/build/lib/lean (the trusted
	// framework build copied from the base, plus the trusted Extracted and JanusTrusted),
	// recorded before any untrusted code runs in the workspace.
	pins      *pinnedLib
	framework pins     // the trusted base's framework pins (Janus.* modules with a framework source)
	prepBuilt []string // modules the trusted Extracted build compiled
	// replayCache: reuse cached passing kernel replays (off with --fresh or without a
	// sandbox); replayFresh: also replay each theorem module with leanchecker --fresh.
	replayCache, replayFresh bool
}

// janusLib is the workspace's framework library directory.
func (ws *consumerWS) janusLib() string {
	return filepath.Join(ws.JanusDir, ".lake", "build", "lib", "lean")
}

// protected are the workspace trees untrusted (and trusted) sandboxed processes must not
// write: the trusted framework package, always; with readOnlyBuilds, the consumer and
// dependency packages too (after their build, for the audit and the replay).
func (ws *consumerWS) protected(readOnlyBuilds bool) []string {
	dirs := []string{ws.JanusDir}
	if readOnlyBuilds {
		dirs = append(dirs, ws.Root)
		if _, err := os.Stat(ws.DepsDir); err == nil {
			dirs = append(dirs, ws.DepsDir)
		}
	}
	return dirs
}

// workspaceFamily groups the workspaces of one consumer package and framework; members
// differ only in Extracted, and a new member starts from a sibling's build.
func workspaceFamily(fw *framework, pkg *consumerPkg) string {
	h := sha256.Sum256([]byte(fw.Sha256 + "\x00" + pkg.Root))
	return filepath.Join(cacheRoot(), "v1", "consumer", hex.EncodeToString(h[:])[:24])
}

func wsDiag(err error) error {
	return &diag{Invalid: true, Msg: "Cannot prepare the consumer workspace: " + err.Error(), Stage: "consumer workspace",
		Next: "Set JANUS_CACHE_DIR to a writable directory, or pass --fresh."}
}

func openWorkspace(fw *framework, pkg *consumerPkg, extracted []byte, fresh bool, lake string, sb *sandbox, tc *toolchain, progress io.Writer) (*consumerWS, error) {
	ws := &consumerWS{lake: lake, sb: sb, tc: tc, replayCache: sb.mode != "none" && !fresh}
	family := workspaceFamily(fw, pkg)
	if fresh {
		parent := filepath.Join(cacheRoot(), "v1", "tmp")
		if err := os.MkdirAll(parent, 0o755); err != nil {
			return nil, wsDiag(err)
		}
		d, err := os.MkdirTemp(parent, "consumer-")
		if err != nil {
			return nil, wsDiag(err)
		}
		ws.Dir, ws.temp = d, true
	} else {
		ws.Dir = filepath.Join(family, sha256Hex(extracted)[:24])
		if err := os.MkdirAll(ws.Dir, 0o755); err != nil {
			return nil, wsDiag(err)
		}
		lk, err := lockFile(ws.Dir+".lock", true)
		if err != nil {
			return nil, wsDiag(err)
		}
		ws.lock = lk
	}
	ws.Root, ws.JanusDir, ws.DepsDir = filepath.Join(ws.Dir, "root"), filepath.Join(ws.Dir, "janus"), filepath.Join(ws.Dir, "deps")
	fail := func(err error) (*consumerWS, error) { ws.close(); return nil, err }

	// The framework library comes from the trusted framework build (the cached base, or one
	// built from scratch for --fresh), never from a build in the workspace: the workspace's copy
	// is replaced whenever its framework modules differ from the base's in any byte, or it holds
	// any module that is not the framework's, Extracted or JanusTrusted.
	var base string
	var err error
	if fresh {
		base, err = fw.freshBase(lake, progress)
		if err == nil {
			defer os.RemoveAll(base)
		}
	} else {
		// The base stays in use (shared lock) until its build has been copied and compared.
		var lease *frameworkLease
		if lease, err = fw.frameworkBase(lake, progress); err == nil {
			base = lease.dir
			defer lease.release()
		}
	}
	if err != nil {
		return fail(err)
	}
	basePins, err := frameworkPins(filepath.Join(base, ".lake", "build", "lib", "lean"), fw.Files)
	if err != nil || len(basePins.want) == 0 {
		return fail(wsDiag(fmt.Errorf("cannot read the framework build in %s: %v", base, err)))
	}
	janusBuild := filepath.Join(ws.JanusDir, ".lake", "build")
	notExtracted := func(m string) bool { return m != "Extracted" && m != "JanusTrusted" }
	tampered := false
	if got, err := pinLib(ws.janusLib(), notExtracted); err != nil || len(diffPins(basePins.want, got)) > 0 {
		if _, err := os.Stat(janusBuild); err == nil {
			// A previous run's framework build differed from the trusted one: the consumer and
			// dependency modules built in this workspace may have been compiled against it, and
			// Lake's traces would not notice. Rebuild them too (the kernel replay would reject
			// them otherwise).
			tampered = true
			_ = os.RemoveAll(filepath.Join(ws.Root, ".lake", "build"))
			_ = os.RemoveAll(ws.DepsDir)
		}
		_ = os.RemoveAll(janusBuild)
		if err := copyTree(filepath.Join(base, ".lake", "build"), janusBuild); err != nil {
			return fail(wsDiag(err))
		}
	}

	if !fresh && !tampered {
		// Seed the consumer modules from the most recently used sibling workspace.
		rootBuild := filepath.Join(ws.Root, ".lake", "build")
		sib := ""
		if _, err := os.Stat(rootBuild); err != nil {
			var sibLock *fileLock
			if sib, sibLock = newestSibling(family, ws.Dir); sib != "" {
				_ = os.RemoveAll(rootBuild)
				if err := copyTree(filepath.Join(sib, "root", ".lake", "build"), rootBuild); err != nil {
					_ = os.RemoveAll(rootBuild)
				}
				sibLock.unlock()
			}
		}
		// Dependency builds too (they are as untrusted as the consumer's own; the kernel
		// replay covers every dependency module the theorem imports).
		for _, d := range pkg.Deps {
			depBuild := filepath.Join(ws.DepsDir, d.Info.Name, ".lake", "build")
			if _, err := os.Stat(depBuild); err == nil {
				continue
			}
			if sib == "" {
				var sibLock *fileLock
				if sib, sibLock = newestSibling(family, ws.Dir); sib != "" {
					sibLock.unlock()
				}
			}
			if sib == "" {
				break
			}
			// Copy only while the sibling is not in use (its lock held), never a build in progress.
			sibLock, err := lockFile(sib+".lock", false)
			if err != nil {
				continue
			}
			if _, err := os.Stat(filepath.Join(sib, "deps", d.Info.Name, ".lake", "build")); err == nil {
				if err := copyTree(filepath.Join(sib, "deps", d.Info.Name, ".lake", "build"), depBuild); err != nil {
					_ = os.RemoveAll(depBuild)
				}
			}
			sibLock.unlock()
		}
	}

	jfiles := map[string][]byte{}
	for p, b := range fw.Files {
		jfiles[p] = b
	}
	jfiles["lakefile.toml"] = append(append([]byte{}, fw.Files["lakefile.toml"]...),
		[]byte("\n# Added by janus verify: the extraction being verified.\n[[lean_lib]]\nname = \"Extracted\"\n")...)
	jfiles["Extracted.lean"] = extracted
	// JanusTrusted: an independently named copy of the extraction, compiled directly (not by
	// the untrusted Lake build) in verifyGroup, so the audit can check the imported Extracted
	// is definitionally this copy.
	jfiles["JanusTrusted.lean"] = janusTrustedSource(extracted)
	ws.janusFiles = jfiles
	keepLake := func(top string) bool { return top == ".lake" }
	if err := syncTree(ws.JanusDir, jfiles, keepLake); err != nil {
		return fail(wsDiag(err))
	}
	if err := syncTree(ws.Root, pkg.Files, keepLake); err != nil {
		return fail(wsDiag(err))
	}
	// Extra dependencies: exactly the pinned files, as path packages overriding the manifest.
	overrides := []map[string]any{{"type": "path", "scope": "", "name": "janus", "manifestFile": "lake-manifest.json",
		"inherited": false, "dir": ws.JanusDir, "configFile": "lakefile.toml"}}
	keep := map[string]bool{}
	for _, d := range pkg.Deps {
		keep[d.Info.Name] = true
		if err := syncTree(filepath.Join(ws.DepsDir, d.Info.Name), d.Files, keepLake); err != nil {
			return fail(wsDiag(err))
		}
		overrides = append(overrides, map[string]any{"type": "path", "scope": "", "name": d.Info.Name, "manifestFile": "lake-manifest.json",
			"inherited": d.Info.Inherited, "dir": filepath.Join(ws.DepsDir, d.Info.Name), "configFile": d.Config})
	}
	if ents, err := os.ReadDir(ws.DepsDir); err == nil {
		for _, e := range ents {
			if !keep[e.Name()] {
				_ = os.RemoveAll(filepath.Join(ws.DepsDir, e.Name()))
			}
		}
	}
	override, _ := json.Marshal(map[string]any{
		"schemaVersion": "1.2.0",
		"packages":      overrides,
	})
	if err := os.MkdirAll(filepath.Join(ws.Root, ".lake"), 0o755); err != nil {
		return fail(wsDiag(err))
	}
	if err := os.WriteFile(filepath.Join(ws.Root, ".lake", "package-overrides.json"), override, 0o644); err != nil {
		return fail(wsDiag(err))
	}
	// Trusted build of Extracted (Lake on our lakefile and sources only, unsandboxed: no
	// consumer code is involved) and of the independently named JanusTrusted copy, before any
	// untrusted code runs in the workspace. From here on janus/ is read-only to every
	// sandboxed process, and its compiled modules are pinned.
	lr := &leanRunner{lake: lake, root: ws.JanusDir}
	out, err := lr.run("build", "--no-ansi", "Extracted")
	if err != nil {
		return fail(&diag{Invalid: true, Msg: "Lean rejected the extracted program.\n" + summarizeLeanErrors(out, 2000), Stage: "extraction elaboration",
			Next: "Check that the Janus framework matches this extractor version.", Details: out})
	}
	for _, m := range builtModules(out) {
		if notExtracted(m) {
			continue
		}
		ws.prepBuilt = append(ws.prepBuilt, m)
	}
	if out, err := runLean(&sandbox{mode: "none"}, tc, ws.JanusDir, nil, tc.leanPathEnv(ws.janusLib()), tc.lean, "--root="+ws.JanusDir,
		filepath.Join(ws.JanusDir, "JanusTrusted.lean"), "-o", filepath.Join(ws.janusLib(), "JanusTrusted.olean")); err != nil {
		return fail(&diag{Invalid: true, Msg: "Lean rejected the trusted copy of the extracted program.\n" + summarizeLeanErrors(out, 2000),
			Stage: "extraction elaboration", Details: out})
	}
	if !samePins(basePins, ws.janusLib()) {
		return fail(&diag{Invalid: true, Stage: "framework integrity",
			Msg:  "Building Extracted changed the framework modules copied from the trusted framework build.",
			Next: "Rerun with --fresh; if it persists, the framework build is not reproducible."})
	}
	ws.framework = basePins.want
	if ws.pins, err = newPinnedLib("the Janus framework build", ws.janusLib(), nil); err != nil {
		return fail(wsDiag(err))
	}
	now := time.Now()
	_ = os.Chtimes(ws.Dir, now, now)
	return ws, nil
}

// newestSibling is the most recently used other workspace of the family with a consumer
// build that is not being used right now. It is returned locked (the caller copies from it and
// then unlocks), so no verification can write to it during the copy.
func newestSibling(family, self string) (string, *fileLock) {
	entries, err := os.ReadDir(family)
	if err != nil {
		return "", nil
	}
	best, bestTime := "", time.Time{}
	for _, e := range entries {
		d := filepath.Join(family, e.Name())
		if !e.IsDir() || d == self {
			continue
		}
		if _, err := os.Stat(filepath.Join(d, "root", ".lake", "build")); err != nil {
			continue
		}
		if fi, err := os.Stat(d); err == nil && fi.ModTime().After(bestTime) {
			best, bestTime = d, fi.ModTime()
		}
	}
	if best == "" {
		return "", nil
	}
	if lk, err := lockFile(best+".lock", false); err == nil {
		return best, lk
	}
	return "", nil
}

func (ws *consumerWS) close() {
	if ws == nil {
		return
	}
	if ws.temp {
		os.RemoveAll(ws.Dir)
	}
	ws.lock.unlock()
	ws.lock = nil
}

// run runs lake in the workspace root under the sandbox (the consumer's lakefile and modules
// are untrusted code), returning standard output and the combined output. Only ws.Dir is
// writable; the network is off and the rest of the filesystem, including the cache and the
// janus binary, is read-only.
func (ws *consumerWS) run(args ...string) (string, string, error) {
	var env []string
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "LEAN_PATH=") && !strings.HasPrefix(e, "LEAN_SRC_PATH=") {
			env = append(env, e)
		}
	}
	cmd := ws.sb.commandOverlay(ws.Root, []string{ws.Dir}, nil, ws.protected(false), append([]string{ws.lake}, args...), env)
	var out bytes.Buffer
	all := &lockedBuffer{}
	cmd.Stdout = io.MultiWriter(&out, all)
	cmd.Stderr = all
	err := cmd.Run()
	return out.String(), all.String(), err
}

// runLeanDirect runs a lean/leanchecker binary (not lake) under the sandbox with an explicit
// LEAN_PATH, used for the janus-audit script and leanchecker. Only the audit directory is
// writable; the framework, consumer and dependency builds are read-only.
func (ws *consumerWS) runLeanDirect(leanPath string, argv ...string) (string, error) {
	auditDir := filepath.Join(ws.Dir, "audit")
	_ = os.MkdirAll(auditDir, 0o755)
	return runLeanProtected(ws.sb, ws.tc, auditDir, nil, ws.protected(true), leanPath, argv...)
}

// lockedBuffer is written by the stdout and stderr copiers of one command concurrently.
type lockedBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (l *lockedBuffer) Write(p []byte) (int, error) {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.b.Write(p)
}

func (l *lockedBuffer) String() string {
	l.mu.Lock()
	defer l.mu.Unlock()
	return l.b.String()
}

// mapper maps workspace paths in Lean output back to the user's files.
func (ws *consumerWS) mapper(pkg *consumerPkg, extracted string) func(string) string {
	mapAbs := func(s string) string {
		s = strings.ReplaceAll(s, filepath.Join(ws.JanusDir, "Extracted.lean"), displayPath(extracted))
		s = strings.ReplaceAll(s, ws.Root+string(filepath.Separator), pkg.Root+string(filepath.Separator))
		for _, d := range pkg.Deps {
			s = strings.ReplaceAll(s, filepath.Join(ws.DepsDir, d.Info.Name)+string(filepath.Separator), d.pkgDir+string(filepath.Separator))
		}
		return s
	}
	return func(s string) string {
		// Lake prints "error: Rel/Path.lean:3:4: msg"; turn it into Lean's
		// "/abs/Rel/Path.lean:3:4: error: msg" so the Lean error summary applies.
		s = lakeMsgRE.ReplaceAllStringFunc(s, func(line string) string {
			m := lakeMsgRE.FindStringSubmatch(line)
			file := m[2]
			if !filepath.IsAbs(file) {
				file = filepath.Join(ws.Root, file)
			}
			return displayPath(mapAbs(file)) + ":" + m[3] + ": " + m[1] + ": "
		})
		return mapAbs(s)
	}
}

var lakeMsgRE = regexp.MustCompile(`(?m)^(error|warning|info): ([^\s:][^:\n]*\.lean):(\d+:\d+): `)

var builtRE = regexp.MustCompile(`(?m)Built (\S+)`)

func builtModules(out string) []string {
	var mods []string
	for _, m := range builtRE.FindAllStringSubmatch(out, -1) {
		mods = append(mods, m[1])
	}
	return mods
}

// consumerRequest is one proof to verify in a consumer package.
type consumerRequest struct {
	Outdir, Proof, Theorem, Binary string

	cr       *CheckResult
	proofSrc []byte
	rel      string // proof path inside the package snapshot
	module   string
	audit    *auditResult
	closure  []string // consumer modules the theorem's environment imports
	Report   *verifiedReport
	Err      error
}

// prepare checks the request's selection and its extraction.
func (r *consumerRequest) prepare() error {
	if r.Theorem == "" {
		r.Theorem = defaultTheorem
	}
	if !theoremNameRE.MatchString(r.Theorem) {
		return &diag{Invalid: true, Msg: fmt.Sprintf("%q is not a plain dotted Lean name.", r.Theorem), Stage: "proof selection",
			Next: "Pass --theorem Namespace.name."}
	}
	if r.Proof == "" {
		return &diag{Invalid: true, Msg: "A consumer verification needs --proof (a .lean file of the package).", Stage: "proof selection",
			Next: "Pass --proof path/to/Module.lean inside --proof-root."}
	}
	cr, err := check(r.Outdir, r.Binary)
	if err != nil {
		return err
	}
	r.cr = cr
	src, err := os.ReadFile(r.Proof)
	if err != nil {
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read proof %s: %v", displayPath(r.Proof), err),
			Stage: "proof selection", Next: "Pass --proof path/to/Module.lean inside --proof-root."}
	}
	r.proofSrc = src
	return nil
}

// verifyConsumer is janus verify with --proof-root: one request, one group.
func verifyConsumer(outdir string, opts map[string]string, stderr io.Writer) (*verifiedReport, error) {
	fw, err := loadFramework(opts["janus-root"])
	if err != nil {
		return nil, err
	}
	req := &consumerRequest{Outdir: outdir, Proof: opts["proof"], Theorem: opts["theorem"], Binary: opts["binary"]}
	if err := req.prepare(); err != nil {
		return nil, err
	}
	lake, err := findLake()
	if err != nil {
		return nil, err
	}
	sb, err := detectSandbox(opts["unsafe-no-sandbox"] != "")
	if err != nil {
		return nil, err
	}
	lease, err := fw.frameworkBase(lake, stderr)
	if err != nil {
		return nil, err
	}
	tc, err := findToolchain(lake, lease.dir)
	lease.release()
	if err != nil {
		return nil, err
	}
	pkg, err := loadConsumer(opts["proof-root"], fw, []string{outdir}, loadOpts{AllowPathDeps: opts["allow-path-deps"] != "", SB: sb})
	if err != nil {
		return nil, err
	}
	if req.rel, err = pkg.proofRel(req.Proof); err != nil {
		return nil, err
	}
	if !bytes.Equal(pkg.Files[req.rel], req.proofSrc) {
		return nil, &diag{Invalid: true, Msg: "The proof changed while the package was read.", Stage: "stale input", Next: "Rerun janus verify."}
	}
	ws, err := openWorkspace(fw, pkg, req.cr.Lean, opts["fresh"] != "", lake, sb, tc, stderr)
	if err != nil {
		return nil, err
	}
	defer ws.close()
	ws.replayFresh = opts["replay-fresh"] != ""
	verifyGroup(fw, pkg, ws, []*consumerRequest{req})
	evictStale()
	return req.Report, req.Err
}

// verifyGroup verifies requests that share one extraction (identical Extracted.lean) in one
// workspace: one Lake build of all their proof modules, one kernel replay of the union of
// their modules, and an audit and report per request. Each request's outcome lands in its
// Report or Err.
func verifyGroup(fw *framework, pkg *consumerPkg, ws *consumerWS, reqs []*consumerRequest) {
	failAll := func(err error) {
		for _, r := range reqs {
			if r.Err == nil {
				r.Err = err
			}
		}
	}
	extractedPath := reqs[0].cr.Extracted
	mapPaths := ws.mapper(pkg, extractedPath)

	leanVersion := ws.tc.version

	// One build of every proof module of the group (sandboxed: lakefile and modules are
	// untrusted).
	targets := []string{"build", "--no-ansi"}
	for _, r := range reqs {
		targets = append(targets, r.rel)
	}
	_, buildOut, _ := ws.run(targets...)
	rebuilt := append(builtModules(buildOut), ws.prepBuilt...)
	if strings.Contains(buildOut, "manifest out of date") || strings.Contains(buildOut, "not in manifest") {
		failAll(&diag{Invalid: true, Msg: "lake-manifest.json does not match the lakefile.", Stage: "consumer manifest",
			Next: "Run lake update in " + displayPath(pkg.Root) + ".", Details: mapPaths(buildOut)})
		return
	}
	// The framework build (with the trusted Extracted/JanusTrusted) must be exactly as pinned
	// before the untrusted build: no module replaced, corrupted, removed or added (R1).
	pinned := pinSet{ws.pins}
	if err := pinned.check("the consumer's Lake build"); err != nil {
		failAll(err)
		return
	}

	libDir := filepath.Join(ws.Root, ".lake", "build", "lib", "lean")
	janusLib := ws.janusLib()
	depLibs := map[string]string{}
	searchDirs := []string{janusLib, libDir}
	for _, d := range pkg.Deps {
		dl := filepath.Join(ws.DepsDir, d.Info.Name, ".lake", "build", "lib", "lean")
		depLibs[d.Info.Name] = dl
		searchDirs = append(searchDirs, dl)
	}
	leanPath := ws.tc.leanPathEnv(searchDirs...)

	// C1 defence in depth: no stray Extracted/JanusTrusted olean on the search path.
	if err := noForeignModule(map[string]string{"Extracted": janusLib, "JanusTrusted": janusLib},
		append(append([]string{}, searchDirs...), ws.tc.libDir)); err != nil {
		failAll(err)
		return
	}

	// Per request: its module (and, when it failed, its own diagnostics). lake query runs the
	// untrusted lakefile again, so the pins are re-checked after it.
	for _, r := range reqs {
		out, all, err := ws.run("query", "--no-ansi", r.rel+":olean")
		rebuilt = append(rebuilt, builtModules(all)...)
		if err != nil {
			r.Err = buildFailure(mapPaths(all), r, ws, pkg)
			continue
		}
		lines := strings.Fields(strings.TrimSpace(out))
		olean := ""
		if len(lines) > 0 {
			olean = lines[len(lines)-1]
		}
		rel, rerr := filepath.Rel(libDir, olean)
		if rerr != nil || strings.HasPrefix(rel, "..") || !strings.HasSuffix(rel, ".olean") {
			r.Err = &diag{Invalid: true, Msg: fmt.Sprintf("%s is not a module of the consumer package (Lake built %s).", r.rel, olean),
				Stage: "proof selection", Next: "Put the proof in a lean_lib of the consumer package."}
			continue
		}
		r.module = strings.ReplaceAll(strings.TrimSuffix(filepath.ToSlash(rel), ".olean"), "/", ".")
	}
	if err := pinned.check("the consumer's Lake build"); err != nil {
		failAll(err)
		return
	}

	// Module identity across the framework, the consumer and its dependencies (deps.go); the
	// dependency module roots tell the auditor which constants come from declared dependencies.
	depRoots, err := checkModuleLayout(janusLib, ws.janusFiles, libDir, depLibs, ws.tc.libDir)
	if err != nil {
		failAll(err)
		return
	}
	// The untrusted build outputs are final now (no untrusted code runs after this point):
	// pin them so the audit and the replay see the same bytes.
	untrusted := []*pinnedLib{}
	if l, err := newPinnedLib("the consumer package build", libDir, nil); err == nil {
		untrusted = append(untrusted, l)
	} else {
		failAll(wsDiag(err))
		return
	}
	for _, n := range sortedKeys(depLibs) {
		l, err := newPinnedLib("the build of dependency "+n, depLibs[n], nil)
		if err != nil {
			failAll(wsDiag(err))
			return
		}
		untrusted = append(untrusted, l)
	}
	pinned = append(pinned, untrusted...)

	// Theorem, axiom and statement audit by the trusted janus-audit (no proof code runs):
	// the generated Audit.lean imports only Janus.Tools.Audit, never the proof.
	auditDir := filepath.Join(ws.Dir, "audit")
	_ = os.MkdirAll(auditDir, 0o755)
	for i, r := range reqs {
		if r.Err != nil {
			continue
		}
		marker := "janus-audit-" + newNonce() + ": "
		af := filepath.Join(auditDir, fmt.Sprintf("Audit%d.lean", i))
		if err := os.WriteFile(af, []byte(auditScript(r.Theorem, r.module, marker, depRoots...)), 0o644); err != nil {
			r.Err = &diag{Invalid: true, Msg: err.Error(), Stage: "theorem audit"}
			continue
		}
		out, _ := ws.runLeanDirect(leanPath, ws.tc.lean, "--root="+auditDir, af)
		if err := pinned.check("the audit"); err != nil {
			failAll(err)
			return
		}
		ar, aerr := parseAuditRecord(mapPaths(out), marker)
		if aerr != nil {
			r.Err = aerr
			continue
		}
		r.audit = ar
	}

	// Kernel replay of every non-core module of each passing theorem's import closure (the
	// framework, Extracted, JanusTrusted, every consumer and dependency module), after checking
	// that each comes from its home: one leanchecker pass over the union, reusing cached passing
	// replays; on failure, each request's own closure separately.
	allDirs := append(append([]string{}, searchDirs...), ws.tc.libDir)
	homes := map[string]string{"Extracted": janusLib, "JanusTrusted": janusLib}
	union := map[string]string{}
	graph := map[string][]string{}
	for _, r := range reqs {
		if r.Err != nil {
			continue
		}
		resolved, err := closureCheck(r.audit.Modules, allDirs, ws.tc.libDir, &pinnedLib{dir: janusLib, want: ws.framework}, homes)
		if err != nil {
			r.Err = err
			continue
		}
		for m, f := range resolved {
			union[m] = f
			r.closure = append(r.closure, m)
		}
		sort.Strings(r.closure)
		for m, imps := range importGraph(r.audit.Imports) {
			graph[m] = imps
		}
	}
	replayed := map[*consumerRequest]kernelReplay{}
	var passing []*consumerRequest
	for _, r := range reqs {
		if r.Err == nil {
			passing = append(passing, r)
		}
	}
	if len(passing) > 0 {
		if !ws.tc.hasChecker {
			for _, r := range passing {
				replayed[r] = kernelReplay{Tool: "leanchecker", Status: "unavailable", Modules: []string{}, Note: "leanchecker not found in the Lean toolchain"}
			}
		} else if plan, err := planReplay(union, graph, ws.tc.version, ws.replayCache); err != nil {
			failAll(err)
			return
		} else {
			run := func(argv ...string) (string, error) { return ws.runLeanDirect(leanPath, argv...) }
			var all []string
			for m := range union {
				all = append(all, m)
			}
			sort.Strings(all)
			_, unionErr := plan.replay(ws.tc.leanchecker, run, all)
			for _, r := range passing {
				if unionErr != nil {
					if out, err := plan.replay(ws.tc.leanchecker, run, r.closure); err != nil {
						r.Err = replayDiag(mapPaths(out))
						continue
					}
				}
				fresh := ""
				if ws.replayFresh {
					if out, err := plan.replayFresh(ws.tc.leanchecker, run, r.module); err != nil {
						r.Err = replayDiag(mapPaths(out))
						continue
					}
					fresh = r.module
				}
				replayed[r] = plan.report(r.closure, fresh)
			}
		}
	}
	if err := pinned.check("the kernel replay"); err != nil {
		failAll(err)
		return
	}

	// Inputs must still be the ones that were checked.
	staleErr := func() error {
		if err := pinned.check("the verification"); err != nil {
			return err
		}
		now := &consumerPkg{Root: pkg.Root, excluded: pkg.excluded}
		if err := now.snapshot(); err != nil || now.Sha256 != pkg.Sha256 {
			return &diag{Invalid: true, Msg: "The consumer package sources changed during verification.", Stage: "stale input", Next: "Rerun janus verify."}
		}
		if err := compareFramework(pkg.Dep.Dir, fw); err != nil {
			d := err.(*diag)
			d.Msg = "The janus dependency changed during verification: " + d.Msg
			d.Stage = "stale input"
			return d
		}
		for _, dep := range pkg.Deps {
			if err := dep.recheck(pkg.opts.SB); err != nil {
				d := err.(*diag)
				d.Msg = "A dependency changed during verification: " + d.Msg
				d.Stage = "stale input"
				return d
			}
		}
		for p, b := range ws.janusFiles {
			if got, err := os.ReadFile(filepath.Join(ws.JanusDir, filepath.FromSlash(p))); err != nil || !bytes.Equal(got, b) {
				return &diag{Invalid: true, Msg: "The framework sources in the workspace changed during verification.", Stage: "stale input", Next: "Rerun janus verify."}
			}
		}
		return nil
	}()

	sort.Strings(rebuilt)
	rebuilt = dedup(rebuilt)
	fi := fw.info()
	for _, r := range reqs {
		if r.Err != nil {
			continue
		}
		if staleErr != nil {
			r.Err = staleErr
			continue
		}
		cr2, err := check(r.Outdir, r.Binary)
		if err != nil {
			d := err.(*diag)
			d.Msg = "Artifacts changed during verification: " + d.Msg
			r.Err = d
			continue
		}
		wsExtracted, _ := os.ReadFile(filepath.Join(ws.JanusDir, "Extracted.lean"))
		if !bytes.Equal(cr2.Lean, r.cr.Lean) || !bytes.Equal(wsExtracted, r.cr.Lean) || !bytes.Equal(pkg.Files[r.rel], r.proofSrc) {
			r.Err = &diag{Invalid: true, Msg: "The proof or Extracted.lean changed during verification.", Stage: "stale input", Next: "Rerun janus verify."}
			continue
		}
		idBytes, _ := os.ReadFile(filepath.Join(r.Outdir, "identity.json"))
		wsRef := ws.Dir
		if ws.temp {
			wsRef = "(temporary, --fresh)"
		}
		commit := fi.Revision
		if fi.Modified {
			commit += "+dirty"
		}
		r.Report = &verifiedReport{
			Schema:                1,
			Theorem:               r.audit.Name,
			Kind:                  r.audit.Kind,
			Module:                r.audit.Module,
			Statement:             r.audit.Statement,
			StatementExplicit:     r.audit.StatementExplicit,
			Axioms:                r.audit.Axioms,
			AllowedAxioms:         allowedAxioms,
			KernelReplay:          replayed[r],
			Proof:                 binaryRef(r.Outdir, r.Proof),
			ProofSha256:           sha256Hex(r.proofSrc),
			Extracted:             "Extracted.lean",
			ExtractedSha256:       sha256Hex(r.cr.Lean),
			IdentitySha256:        sha256Hex(idBytes),
			Binary:                binaryRef(r.Outdir, r.cr.BinPath),
			BinarySha256:          r.cr.Identity.BinarySha256,
			Symbol:                r.cr.Identity.Symbol,
			Address:               r.cr.Identity.Address,
			GoVersion:             r.cr.Identity.GoVersion,
			MainModule:            r.cr.Identity.MainModule,
			LeanVersion:           leanVersion,
			JanusRoot:             ws.JanusDir,
			JanusCommit:           commit,
			ExtractorVersion:      extractorVersion,
			Timestamp:             time.Now().UTC().Format(time.RFC3339),
			Framework:             fi,
			Sandbox:               ws.sb.info(),
			Definitions:           r.audit.Definitions,
			DependencyConsts:      r.audit.External,
			DependencyDefinitions: r.audit.ExternalDefs,
			Notes:                 r.audit.Notes,
			Consumer: &consumerInfo{
				Root: pkg.Root, Lakefile: pkg.Lakefile, Module: r.module, SnapshotSha256: pkg.Sha256,
				Files: pkg.fileHashes(), Dependency: pkg.Dep, Dependencies: pkg.depInfos(), AllowPathDeps: pkg.opts.AllowPathDeps,
				Workspace: wsRef, Rebuilt: nonNil(rebuilt),
			},
		}
	}
}

// buildFailure classifies a failed build of a request's module by where Lean reported errors.
func buildFailure(out string, r *consumerRequest, ws *consumerWS, pkg *consumerPkg) error {
	summary := summarizeLeanErrors(out, 2000)
	if summary == "" {
		summary = lastLines(out, 20)
	}
	ex := displayPath(r.cr.Extracted)
	switch {
	case strings.Contains(out, ex+":") && regexp.MustCompile(regexp.QuoteMeta(ex)+`:\d+:\d+: error`).MatchString(out):
		return &diag{Invalid: true, Msg: "Lean rejected the extracted program " + ex + ".\n" + summary, Stage: "extraction elaboration",
			Next: "Check that the Janus framework matches this extractor version.", Details: out}
	case regexp.MustCompile(`(?m)Janus/[^\s:]+\.lean:\d+:\d+: error`).MatchString(out) && !strings.Contains(out, pkg.Root):
		return &diag{Invalid: true, Msg: "Building the Janus framework failed.\n" + summary, Stage: "Janus library build", Details: out}
	}
	return &diag{Invalid: true, Msg: "Lean rejected the proof module " + r.rel + " (or a module it imports).\n" + summary, Stage: "proof checking",
		Next: "Fix the proof. It must import Extracted and prove " + r.Theorem + ".", Details: out}
}

func lastLines(s string, n int) string {
	lines := strings.Split(strings.TrimRight(s, "\n"), "\n")
	if len(lines) > n {
		lines = lines[len(lines)-n:]
	}
	return strings.Join(lines, "\n")
}

func fileSha(p string) string {
	b, err := os.ReadFile(p)
	if err != nil {
		return ""
	}
	return sha256Hex(b)
}

func dedup(s []string) []string {
	var out []string
	for i, v := range s {
		if i == 0 || v != s[i-1] {
			out = append(out, v)
		}
	}
	return out
}

func nonNil(s []string) []string {
	if s == nil {
		return []string{}
	}
	return s
}

// evictStale removes consumer workspaces and framework builds unused for
// $JANUS_CACHE_RETENTION_DAYS (default 7) and temporary directories older than a day,
// skipping any in use.
func evictStale() {
	days := 7.0
	if v, err := strconv.ParseFloat(os.Getenv("JANUS_CACHE_RETENTION_DAYS"), 64); err == nil && v > 0 {
		days = v
	}
	cutoff := time.Now().Add(-time.Duration(days * 24 * float64(time.Hour)))
	base := filepath.Join(cacheRoot(), "v1")
	families, _ := os.ReadDir(filepath.Join(base, "consumer"))
	for _, f := range families {
		fdir := filepath.Join(base, "consumer", f.Name())
		members, _ := os.ReadDir(fdir)
		for _, m := range members {
			d := filepath.Join(fdir, m.Name())
			fi, err := os.Stat(d)
			if err != nil || !fi.IsDir() || fi.ModTime().After(cutoff) {
				continue
			}
			if lk, err := lockFile(d+".lock", false); err == nil {
				os.RemoveAll(d)
				os.Remove(d + ".lock")
				lk.unlock()
			}
		}
	}
	bases, _ := os.ReadDir(filepath.Join(base, "framework"))
	for _, b := range bases {
		d := filepath.Join(base, "framework", b.Name())
		fi, err := os.Stat(d)
		if err != nil || !fi.IsDir() || fi.ModTime().After(cutoff) {
			continue
		}
		// A framework build in use is share-locked, so the exclusive try fails and it is kept.
		// Removing the lock file under the lock is safe: lockFileMode re-checks the inode.
		if lk, err := lockFile(d+".lock", false); err == nil {
			os.RemoveAll(d)
			os.Remove(d + ".ready")
			os.Remove(d + ".lock")
			lk.unlock()
		}
	}
	tmps, _ := os.ReadDir(filepath.Join(base, "tmp"))
	for _, t := range tmps {
		d := filepath.Join(base, "tmp", t.Name())
		if fi, err := os.Stat(d); err == nil && fi.ModTime().Before(time.Now().Add(-24*time.Hour)) {
			os.RemoveAll(d)
		}
	}
}

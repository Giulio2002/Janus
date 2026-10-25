package main

// janus verify --asl: the same guarantee, transferred to Arm's ASL (docs/ASL.md, section
// "janus verify --asl"; threat model in docs/SOUNDNESS.md).
//
// After the main verification has passed, the ASL stage
//
//  1. builds the JanusASL package (the vendored ArmASL model, lean-sail and JanusASL's proofs) once
//     per framework and JanusASL version in the trusted cache (<cache>/v1/asl/<key>), trusted and
//     unsandboxed (only Janus' own sources are involved), and pins its compiled modules;
//  2. compiles, trusted, JanusASLWords: `JanusASL.Classify.covered Extracted.program = true` by
//     `decide +kernel` on the identity-checked Extracted, with a report of every word outside the
//     proved subset (the stage fails with Invalid and that list if there is one);
//  3. compiles, sandboxed (it imports the untrusted proof), JanusASLCorollary: the command
//     `janus_asl_corollary` adds `Ensures.toASL` applied to the user's theorem;
//  4. audits the corollary with the trusted auditor (JanusAudit.runASL: the type must be exactly the
//     derivation from the user's theorem, no untrusted module may declare a JanusASL/ArmASL/Sail/
//     JanusASLWords name, clean-environment print, round-trip, instance checks, axioms);
//  5. kernel-replays the corollary's whole import closure (ArmASL, Sail and JanusASL included) with
//     leanchecker, through the replay cache;
//  6. records the statement, axioms, model version and hash and the assumptions in verified.json
//     under "asl".
//
// A failure of the ASL stage never changes the main result: verified.json keeps the verified
// theorem and records the ASL failure, and janus exits with status 1.

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	janus "github.com/Giulio2002/Janus"
)

const (
	aslCorollaryModule = "JanusASLCorollary"
	aslCorollaryName   = "JanusASLCorollary.correctness_asl"
	aslWordsModule     = "JanusASLWords"
	aslWordsName       = "JanusASLWords.covered"
)

// aslRoots are the module roots of the trusted JanusASL build (the package, the generated model
// and lean-sail). No other directory on the search path may provide a module under them.
var aslRoots = []string{"JanusASL", "ArmASL", "Sail"}

// aslReservedRoots additionally include the two modules janus writes for the ASL stage.
var aslReservedRoots = append(append([]string{}, aslRoots...), aslWordsModule, aslCorollaryModule)

// aslReport is the "asl" record of verified.json.
type aslReport struct {
	Status string `json:"status"` // "verified" or "invalid"
	// Of is the verified theorem the corollary is derived from.
	Of                string   `json:"of"`
	Theorem           string   `json:"theorem,omitempty"`
	Module            string   `json:"module,omitempty"`
	Derivation        string   `json:"derivation"`
	Statement         string   `json:"statement,omitempty"`
	StatementExplicit string   `json:"statementExplicit,omitempty"`
	Definitions       []string `json:"definitions,omitempty"`
	// DependencyDefinitions and Notes as in the main report (round 7 J1, K1).
	DependencyDefinitions []string      `json:"dependencyDefinitions,omitempty"`
	Notes                 []string      `json:"notes,omitempty"`
	Axioms                []string      `json:"axioms,omitempty"`
	KernelReplay          *kernelReplay `json:"kernelReplay,omitempty"`
	Coverage              *aslCoverage  `json:"coverage,omitempty"`
	Model                 aslModelInfo  `json:"model"`
	Assumptions           []string      `json:"assumptions"`
	Failure               *failureJSON  `json:"failure,omitempty"`
}

// aslCoverage is the result of the trusted coverage check (JanusASLWords).
type aslCoverage struct {
	Words     int            `json:"words"`
	Classes   map[string]int `json:"classes"`
	Uncovered []string       `json:"uncovered"`
}

// aslModelInfo identifies the ASL model and the JanusASL proofs the corollary is about.
type aslModelInfo struct {
	Source         string            `json:"source"` // "embedded" or "directory"
	Version        map[string]string `json:"version"`
	ArmASLSha256   string            `json:"armASLSha256"`   // vendor/ArmASL.tar.gz
	JanusASLSha256 string            `json:"janusASLSha256"` // every JanusASL source file
	Build          string            `json:"build,omitempty"`
}

// aslPackage is the JanusASL Lake package: the copy embedded in janus, or <janus-root>/JanusASL.
type aslPackage struct {
	Source, Dir string
	Files       map[string][]byte // slash paths relative to the package
	Sha256      string
	ModelSha256 string
	Version     map[string]string
}

func isASLFile(p string) bool {
	switch p {
	case "lakefile.toml", "lake-manifest.json", "lean-toolchain",
		"vendor/ArmASL.tar.gz", "vendor/ArmASL.tar.gz.sha256", "vendor/ArmASL.version":
		return true
	}
	return strings.HasPrefix(p, "JanusASL/") && strings.HasSuffix(p, ".lean")
}

func aslDiag(msg, next string) error {
	return &diag{Invalid: true, Msg: msg, Stage: "ASL build", Next: next}
}

// loadASL reads the JanusASL package of the framework: <dir>/JanusASL for a directory framework,
// else the copy embedded in this binary. The vendored model must match its recorded SHA-256.
func loadASL(fw *framework) (*aslPackage, error) {
	pkg := &aslPackage{Source: fw.Source, Files: map[string][]byte{}}
	var fsys fs.FS
	if fw.Source == "directory" {
		pkg.Dir = filepath.Join(fw.Dir, "JanusASL")
		fsys = os.DirFS(pkg.Dir)
	} else {
		sub, err := fs.Sub(janus.ASL, "JanusASL")
		if err != nil {
			return nil, aslDiag("Cannot read the embedded JanusASL package: "+err.Error(), "")
		}
		fsys = sub
	}
	err := fs.WalkDir(fsys, ".", func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if p != "." && (strings.HasPrefix(d.Name(), ".") || p == "ArmASL" || p == "sail" || p == "tools") {
				return fs.SkipDir
			}
			return nil
		}
		if isASLFile(p) {
			b, err := fs.ReadFile(fsys, p)
			if err != nil {
				return err
			}
			pkg.Files[p] = b
		}
		return nil
	})
	if err != nil {
		return nil, aslDiag("Cannot read the JanusASL package: "+err.Error(),
			"--asl needs the JanusASL package: the copy embedded in janus, or JanusASL/ in the --janus-root checkout.")
	}
	for _, p := range []string{"lakefile.toml", "lake-manifest.json", "vendor/ArmASL.tar.gz", "vendor/ArmASL.tar.gz.sha256", "vendor/ArmASL.version"} {
		if _, ok := pkg.Files[p]; !ok {
			return nil, aslDiag("The JanusASL package has no "+p+".",
				"--asl needs the JanusASL package: the copy embedded in janus, or JanusASL/ in the --janus-root checkout.")
		}
	}
	pkg.ModelSha256 = sha256Hex(pkg.Files["vendor/ArmASL.tar.gz"])
	if want := strings.TrimSpace(string(pkg.Files["vendor/ArmASL.tar.gz.sha256"])); want != pkg.ModelSha256 {
		return nil, aslDiag(fmt.Sprintf("The vendored ASL model JanusASL/vendor/ArmASL.tar.gz has SHA-256 %s, not the recorded %s.", pkg.ModelSha256, want),
			"Restore the vendored model (git checkout JanusASL/vendor), or regenerate it with scripts/asl.sh gen.")
	}
	pkg.Version = map[string]string{}
	for _, l := range strings.Split(string(pkg.Files["vendor/ArmASL.version"]), "\n") {
		if k, v, ok := strings.Cut(strings.TrimSpace(l), "="); ok {
			pkg.Version[k] = v
		}
	}
	pkg.Sha256 = frameworkShaOf(pkg.Files, func(string) bool { return true })
	return pkg, nil
}

// frameworkShaOf is frameworkSha over the files keep accepts.
func frameworkShaOf(files map[string][]byte, keep func(string) bool) string {
	var paths []string
	for p := range files {
		if keep(p) {
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

func (pkg *aslPackage) info(build string) aslModelInfo {
	return aslModelInfo{Source: pkg.Source, Version: pkg.Version, ArmASLSha256: pkg.ModelSha256, JanusASLSha256: pkg.Sha256, Build: build}
}

// unpackModel expands vendor/ArmASL.tar.gz (ArmASL.lean and ArmASL/*.lean) into memory.
func unpackModel(tgz []byte) (map[string][]byte, error) {
	zr, err := gzip.NewReader(bytes.NewReader(tgz))
	if err != nil {
		return nil, err
	}
	tr := tar.NewReader(zr)
	out := map[string][]byte{}
	for {
		h, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		if h.Typeflag == tar.TypeDir {
			continue
		}
		name := path.Clean(h.Name)
		if h.Typeflag != tar.TypeReg || path.IsAbs(name) || strings.HasPrefix(name, "..") ||
			!(name == "ArmASL.lean" || (strings.HasPrefix(name, "ArmASL/") && strings.HasSuffix(name, ".lean"))) {
			return nil, fmt.Errorf("unexpected entry %q", h.Name)
		}
		b, err := io.ReadAll(tr)
		if err != nil {
			return nil, err
		}
		out[name] = b
	}
	if _, ok := out["ArmASL.lean"]; !ok {
		return nil, fmt.Errorf("no ArmASL.lean")
	}
	return out, nil
}

// aslBuild is the built JanusASL package in the cache, with its compiled modules pinned.
type aslBuild struct {
	pkg  *aslPackage
	Dir  string
	Libs []string // the package's lib dir (JanusASL.*, ArmASL*) and lean-sail's (Sail*)
	pins []*pinnedLib
	use  *fileLock // shared lock on <Dir>.use while the build is in use (cachegc.go)
}

// release ends the use of the build: the cache collector may remove it again.
func (b *aslBuild) release() {
	if b != nil {
		b.use.unlock()
		b.use = nil
	}
}

// aslCacheDir is the cache directory of the JanusASL build for a framework: keyed by the
// framework's identity, every JanusASL source (with the model), the toolchain and the framework
// build it requires (janusDir), so that builds against different framework directories never
// share (and keep re-pointing) one Lake workspace.
func aslCacheDir(fw *framework, pkg *aslPackage, janusDir string) string {
	h := sha256.Sum256([]byte("janus-asl-v1\n" + fw.Sha256 + "\n" + pkg.Sha256 + "\n" + fw.Toolchain + "\n" + janusDir + "\n"))
	return filepath.Join(cacheRoot(), "v1", "asl", hex.EncodeToString(h[:])[:24])
}

// buildASL materializes the JanusASL package in the cache, requiring janus from janusDir (the
// trusted framework build of this verification), and builds ArmASL and JanusASL there with Lake.
// This is trusted (only Janus' own sources and the pinned lean-sail are involved) and runs
// unsandboxed; the first build fetches lean-sail from GitHub and takes about an hour, later runs
// only check Lake's traces. The sources are re-synchronised with the package's bytes on every
// run, so a damaged copy is repaired before Lake decides what to rebuild.
func buildASL(fw *framework, janusDir, lake string, progress io.Writer) (*aslBuild, error) {
	pkg, err := loadASL(fw)
	if err != nil {
		return nil, err
	}
	model, err := unpackModel(pkg.Files["vendor/ArmASL.tar.gz"])
	if err != nil {
		return nil, aslDiag("Cannot unpack the vendored ASL model: "+err.Error(), "Restore JanusASL/vendor/ArmASL.tar.gz.")
	}
	dir := aslCacheDir(fw, pkg, janusDir)
	if err := os.MkdirAll(filepath.Dir(dir), 0o755); err != nil {
		return nil, aslDiag("Cannot create the JanusASL cache: "+err.Error(), "Set JANUS_CACHE_DIR to a writable directory.")
	}
	lk, err := lockEntry(dir, dir+".lock")
	if err != nil {
		return nil, aslDiag("Cannot lock the JanusASL cache: "+err.Error(), "")
	}
	defer lk.unlock()
	gcPin(dir)
	// In use from here until release (taken under the build lock, so the collector, which needs
	// both, cannot remove the build in between).
	use, err := lockFileMode(dir+".use", true, true)
	if err != nil {
		return nil, aslDiag("Cannot lock the JanusASL cache: "+err.Error(), "")
	}
	ok := false
	defer func() {
		if !ok {
			use.unlock()
		}
	}()
	touchUse(dir, dir+".lock", dir+".use")
	files := map[string][]byte{}
	for p, b := range pkg.Files {
		files[p] = b
	}
	for p, b := range model {
		files[p] = b
	}
	if err := syncTree(dir, files, func(top string) bool { return top == ".lake" }); err != nil {
		return nil, aslDiag("Cannot write the JanusASL package to the cache: "+err.Error(), "Set JANUS_CACHE_DIR to a writable directory.")
	}
	if _, err := os.Stat(filepath.Join(dir, ".lake", "build")); err != nil {
		// A new framework or JanusASL version: start from the most recently used other build.
		// Lake reuses every module whose inputs are unchanged (by content hash), so the ArmASL
		// model, which depends on neither, is not rebuilt.
		if sib := newestASLSibling(dir); sib != "" {
			if progress != nil {
				fmt.Fprintf(progress, "Seeding the JanusASL build %s from %s.\n", displayPath(dir), displayPath(sib))
			}
			if err := copyTree(filepath.Join(sib, ".lake"), filepath.Join(dir, ".lake.seed")); err == nil {
				_ = os.Remove(filepath.Join(dir, ".lake.seed", "package-overrides.json"))
				_ = os.RemoveAll(filepath.Join(dir, ".lake"))
				_ = os.Rename(filepath.Join(dir, ".lake.seed"), filepath.Join(dir, ".lake"))
			} else {
				_ = os.RemoveAll(filepath.Join(dir, ".lake.seed"))
			}
		}
	}
	// The lakefile requires janus from ".."; point it at this verification's trusted framework.
	override, _ := json.Marshal(map[string]any{"schemaVersion": "1.2.0", "packages": []map[string]any{{
		"type": "path", "scope": "", "name": "janus", "manifestFile": "lake-manifest.json", "inherited": false,
		"dir": janusDir, "configFile": "lakefile.toml"}}})
	if err := os.MkdirAll(filepath.Join(dir, ".lake"), 0o755); err != nil {
		return nil, aslDiag(err.Error(), "")
	}
	if err := os.WriteFile(filepath.Join(dir, ".lake", "package-overrides.json"), override, 0o644); err != nil {
		return nil, aslDiag(err.Error(), "")
	}
	if _, err := os.Stat(filepath.Join(dir, ".lake", "build", "lib", "lean", "ArmASL.olean")); err != nil && progress != nil {
		fmt.Fprintf(progress, "Building JanusASL (Arm's ASL in Lean, model %s) in %s; this happens once and takes about an hour (lean-sail is fetched from GitHub).\n",
			pkg.ModelSha256[:12], displayPath(dir))
	}
	lr := &leanRunner{lake: lake, root: dir}
	if out, err := lr.run("build", "--no-ansi", "ArmASL", "JanusASL"); err != nil {
		return nil, &diag{Invalid: true, Msg: "Building the JanusASL package failed: " + err.Error() + "\n" + summarizeLeanErrors(out, 2000),
			Stage: "ASL build", Next: "Run lake build ArmASL JanusASL in " + dir + " and fix the reported errors.", Details: lastLines(out, 60)}
	}
	touchUse(dir, dir+".lock", dir+".use")
	b := &aslBuild{pkg: pkg, Dir: dir, use: use, Libs: []string{
		filepath.Join(dir, ".lake", "build", "lib", "lean"),
		filepath.Join(dir, ".lake", "packages", "Sail", ".lake", "build", "lib", "lean"),
	}}
	for i, l := range b.Libs {
		who := "the JanusASL build"
		if i == 1 {
			who = "the lean-sail build"
		}
		p, err := newPinnedLib(who, l, nil)
		if err != nil || len(p.want) == 0 {
			return nil, aslDiag(fmt.Sprintf("Cannot read the JanusASL build %s: %v", displayPath(l), err), "")
		}
		b.pins = append(b.pins, p)
	}
	ok = true
	return b, nil
}

// buildASLFor builds the JanusASL package against a trusted framework build: root, the one this
// verification already holds (the checkout for a directory framework, else the cached base), or,
// with root "" (consumer packages and verify-batch, whose workspaces take their own framework
// copies), the cached framework base, held while Lake builds against it.
func buildASLFor(fw *framework, root, lake string, progress io.Writer) (*aslBuild, error) {
	if root != "" {
		return buildASL(fw, root, lake, progress)
	}
	lease, err := fw.frameworkBase(lake, progress)
	if err != nil {
		return nil, err
	}
	defer lease.release()
	return buildASL(fw, lease.dir, lake, progress)
}

// newestASLSibling is the most recently used other JanusASL build in the cache that has a
// build and is not being built right now.
func newestASLSibling(self string) string {
	parent := filepath.Dir(self)
	entries, err := os.ReadDir(parent)
	if err != nil {
		return ""
	}
	best, bestTime := "", time.Time{}
	for _, e := range entries {
		d := filepath.Join(parent, e.Name())
		if !e.IsDir() || d == self {
			continue
		}
		if _, err := os.Stat(filepath.Join(d, ".lake", "build", "lib", "lean", "ArmASL.olean")); err != nil {
			continue
		}
		if fi, err := os.Stat(d); err == nil && fi.ModTime().After(bestTime) {
			best, bestTime = d, fi.ModTime()
		}
	}
	if best == "" {
		return ""
	}
	if lk, err := lockFile(best+".lock", false); err == nil {
		lk.unlock()
		return best
	}
	return ""
}

// aslFrameworkJSON is `janus framework`'s JanusASL record.
type aslFrameworkJSON struct {
	aslModelInfo
	// CacheDir is where janus verify --asl builds the package (for --proof-root and verify-batch
	// groups, ConsumerCacheDir: they build against the cached framework base).
	CacheDir         string `json:"cacheDir"`
	ConsumerCacheDir string `json:"consumerCacheDir"`
	Built            bool   `json:"built"`
}

func aslFrameworkInfo(fw *framework) *aslFrameworkJSON {
	pkg, err := loadASL(fw)
	if err != nil {
		return nil
	}
	base := filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])
	janusDir := base
	if fw.Source == "directory" {
		janusDir = fw.Dir
	}
	a := &aslFrameworkJSON{aslModelInfo: pkg.info(""), CacheDir: aslCacheDir(fw, pkg, janusDir), ConsumerCacheDir: aslCacheDir(fw, pkg, base)}
	_, err = os.Stat(filepath.Join(a.CacheDir, ".lake", "build", "lib", "lean", "JanusASL", "Verify.olean"))
	a.Built = err == nil
	return a
}

// aslAssumptionText are the hypotheses an ASL corollary can carry, in plain words; the record
// lists those whose predicate the statement names, then the caveats that always apply.
var aslAssumptionText = []struct{ name, text string }{
	{"JanusASL.Proofs.Rel", "Rel js s: the ASL (Sail) state s holds the Janus state's X0-X30, SP (as SP_EL0), PC and NZCV, at EL0 with PSTATE.SP = 0 and PSTATE.nRW = 0. Nothing else of the ASL state (system registers, features, memory) is constrained by Rel."},
	{"JanusASL.Proofs.LinuxEL0Config", "LinuxEL0Config s: the ASL state's configuration is the Linux EL0 one janus_init builds: the FeatureImpl vector (features 1-3, 18, 19, 87, 88, 95, 96 and 258 off), SCR_EL3, SCR, HCR_EL2, HCRX_EL2, TCR_EL1, MDCR_EL3, MDCR_EL2, the BRBE/SPE/GCS control registers as janus_init sets them, no SPE sample in flight, not in a guarded page, PSTATE.EL = 0, nRW = 0, SP = 0. It is preserved by every proved step; janus-asl-check evaluates it on its base state and on every corpus case."},
	{"JanusASL.Proofs.UserMapped", "UserMapped m s: Janus' memory regions are identity-mapped Normal write-back user memory under the ASL's own page-table translation (writable where Janus says so), independent of GPR/SP/data changes, and none of it lies in the model's GIC/UART windows; checked by evaluation in janus-asl-check, not proved."},
	{"JanusASL.Proofs.MemRel", "MemRel m s: the ASL memory holds Janus' bytes on every byte of Janus' memory regions."},
}

var aslCaveats = []string{
	"The ASL is the Sail translation of Arm's arm-v9.4-a ASL (sail-arm), sliced to the Janus subset and translated to Lean by Sail's Lean backend (docs/ASL.md, Trust story); the guarantee is about that generated Lean model.",
	"aslRun fetches each instruction word with the program's own fetch (the extracted code), not through the ASL's translated instruction fetch; one janus_step per instruction (decode and execute), with no interrupts and no debug.",
	"Only runs that return to the caller are transferred; faults and out-of-fuel outcomes of Janus are not (there Janus is conservative and the ASL may continue).",
}

func aslAssumptions(statement string) []string {
	var out []string
	for _, a := range aslAssumptionText {
		if regexp.MustCompile(`\b` + regexp.QuoteMeta(a.name) + `\b`).MatchString(statement) {
			out = append(out, a.text)
		}
	}
	return append(out, aslCaveats...)
}

// aslEnv is what the ASL stage needs from the main verification it follows.
type aslEnv struct {
	sb          *sandbox
	tc          *toolchain
	build       *aslBuild
	runBase     string            // parent of the stage's private directories
	trustedDirs []string          // Extracted/JanusTrusted's home first, then the framework library
	searchDirs  []string          // the main verification's LEAN_PATH dirs (toolchain excluded), in order
	protected   []string          // read-only to every sandboxed step
	pinned      pinSet            // the main verification's pins (re-checked)
	framework   *pinnedLib        // the framework pins (closure check)
	homes       map[string]string // the main verification's module homes
	theorem     string            // the verified theorem
	proofModule string
	depRoots    []string
	replayCache bool
	replayFresh bool
	mapPaths    func(string) string
	// auditExe is the compiled auditor (janus-audit) of the framework build and auditExeSha the
	// SHA-256 its build stamp records; with auditExe "" the trusted Audit.lean script runs instead.
	auditExe, auditExeSha string
}

// aslFail records an ASL stage failure.
func aslFail(r *aslReport, err error) *aslReport {
	r.Status = "invalid"
	f := toFailureJSON(err)
	if len(f.Details) > 8000 {
		f.Details = lastLines(f.Details, 80)
	}
	r.Failure = &f
	return r
}

// runASLStage derives, audits and replays the ASL corollary of e.theorem. It never fails the
// main verification: the outcome is the returned record.
func runASLStage(e *aslEnv) *aslReport {
	r := &aslReport{Of: e.theorem, Model: e.build.pkg.info(e.build.Dir), Assumptions: []string{},
		Derivation: fmt.Sprintf("%s := JanusAudit.aslCorollary %s %s: Ensures.toASL (JanusASL.Proofs) applied to %s, its program facts discharged by JanusASL.Verify.covered_* from %s : JanusASL.Classify.covered Extracted.program = true (decide +kernel)",
			aslCorollaryName, e.theorem, aslWordsName, e.theorem, aslWordsName)}
	pinned := append(append(pinSet{}, e.pinned...), e.build.pins...)
	if err := pinned.check("the JanusASL build"); err != nil {
		return aslFail(r, err)
	}
	// No directory of the main verification may provide a module under a JanusASL root: the
	// trusted build is their only home.
	for _, d := range e.searchDirs {
		for _, root := range aslReservedRoots {
			for _, p := range []string{filepath.Join(d, root), filepath.Join(d, root+".olean")} {
				if _, err := os.Stat(p); err == nil {
					return aslFail(r, &diag{Invalid: true, Stage: "ASL module identity",
						Msg:  fmt.Sprintf("%s is on the search path of the verification; it could shadow the trusted JanusASL modules (%s).", displayPath(p), strings.Join(aslReservedRoots, ", ")),
						Next: "Remove the module: JanusASL, ArmASL and Sail come only from the trusted JanusASL build, JanusASLWords and JanusASLCorollary only from janus."})
				}
			}
		}
	}
	mkdir := func(pattern string) (string, error) {
		d, err := os.MkdirTemp(e.runBase, pattern)
		if err == nil {
			_ = os.Chmod(d, 0o700)
		}
		return d, err
	}

	// 1. Coverage, trusted: Extracted and JanusASL.Classify only.
	wordsDir, err := mkdir("asl-words-")
	if err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL coverage"})
	}
	defer os.RemoveAll(wordsDir)
	marker := "janus-asl-" + newNonce() + ": "
	src := fmt.Sprintf("import Extracted\nimport JanusASL.Classify\n#eval JanusASL.Classify.report %s Extracted.program\n"+
		"theorem %s : JanusASL.Classify.covered Extracted.program = true := by decide +kernel\n", leanString(marker), aslWordsName)
	if err := os.WriteFile(filepath.Join(wordsDir, aslWordsModule+".lean"), []byte(src), 0o644); err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL coverage"})
	}
	wordsPath := e.tc.leanPathEnv(append(append([]string{wordsDir}, e.trustedDirs...), e.build.Libs...)...)
	out, cerr := runLean(&sandbox{mode: "none"}, e.tc, wordsDir, nil, wordsPath, e.tc.lean, "--root="+wordsDir,
		filepath.Join(wordsDir, aslWordsModule+".lean"), "-o", filepath.Join(wordsDir, aslWordsModule+".olean"))
	cov := parseCoverage(out, marker)
	r.Coverage = cov
	if cov == nil || len(cov.Uncovered) > 0 || cerr != nil {
		msg := "The ASL coverage check did not run.\n" + summarizeLeanErrors(out, 2000)
		if cov != nil && len(cov.Uncovered) > 0 {
			msg = fmt.Sprintf("%d of the program's %d words (or its addresses) are outside the subset proved equivalent to Arm's ASL:\n  %s",
				len(cov.Uncovered), cov.Words, strings.Join(cov.Uncovered, "\n  "))
		} else if cov != nil && cerr != nil {
			msg = "The kernel did not confirm the ASL coverage of Extracted.program.\n" + summarizeLeanErrors(out, 2000)
		}
		return aslFail(r, &diag{Invalid: true, Msg: msg, Stage: "ASL coverage", Details: out,
			Next: "The ASL corollary needs every instruction in a class with a JanusASL equivalence theorem (docs/ASL.md lists them); the main verification is unaffected."})
	}
	wordsPins, err := newPinnedLib("the trusted JanusASLWords build", wordsDir, nil)
	if err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL coverage"})
	}
	pinned = append(pinned, wordsPins)

	// 2. The corollary, sandboxed: it imports the proof.
	corDir, err := mkdir("asl-cor-")
	if err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL corollary"})
	}
	defer os.RemoveAll(corDir)
	src = fmt.Sprintf("import %s\nimport %s\nimport JanusASL.Verify\njanus_asl_corollary %s of %s using %s\n",
		e.proofModule, aslWordsModule, aslCorollaryName, e.theorem, aslWordsName)
	if err := os.WriteFile(filepath.Join(corDir, aslCorollaryModule+".lean"), []byte(src), 0o644); err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL corollary"})
	}
	dirs := append(append(append(append([]string{}, e.searchDirs...), e.build.Libs...), wordsDir), corDir)
	leanPath := e.tc.leanPathEnv(dirs...)
	protected := append(append(append([]string{}, e.protected...), e.build.Libs...), wordsDir)
	mapPaths := func(s string) string {
		return strings.ReplaceAll(e.mapPaths(s), filepath.Join(corDir, aslCorollaryModule+".lean"), "<"+aslCorollaryModule+".lean, generated by janus>")
	}
	if out, err := runLeanProtected(e.sb, e.tc, corDir, nil, protected, leanPath, e.tc.lean, "--root="+corDir,
		filepath.Join(corDir, aslCorollaryModule+".lean"), "-o", filepath.Join(corDir, aslCorollaryModule+".olean")); err != nil {
		out = mapPaths(out)
		return aslFail(r, &diag{Invalid: true, Stage: "ASL corollary", Details: out,
			Msg:  "Lean rejected the ASL corollary of " + e.theorem + ".\n" + summarizeLeanErrors(out, 2000),
			Next: "--asl transfers a theorem `∀ …, Janus.GoABI.Ensures Extracted.program …` (arm64); the proof must not declare JanusASL, ArmASL, Sail, JanusASLWords or JanusASLCorollary names."})
	}
	if err := pinned.check("the ASL corollary compile"); err != nil {
		return aslFail(r, err)
	}
	corPins, err := newPinnedLib("the ASL corollary build", corDir, nil)
	if err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL corollary"})
	}
	if _, ok := corPins.want[aslCorollaryModule+".olean"]; !ok {
		return aslFail(r, &diag{Invalid: true, Msg: "The ASL corollary compile produced no " + aslCorollaryModule + ".olean.", Stage: "ASL corollary"})
	}
	pinned = append(pinned, corPins)

	// 3. Audit by the trusted auditor (no proof code runs).
	auditDir, err := mkdir("asl-audit-")
	if err != nil {
		return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL audit"})
	}
	defer os.RemoveAll(auditDir)
	amarker := "janus-audit-" + newNonce() + ": "
	var roots []string
	for _, d := range e.depRoots {
		roots = append(roots, leanString(d))
	}
	readOnly := append(append([]string{}, protected...), corDir)
	var aout string
	if e.auditExe != "" {
		if got := regularFileSha(e.auditExe); got != e.auditExeSha {
			return aslFail(r, &diag{Invalid: true, Stage: "framework integrity",
				Msg: fmt.Sprintf("the auditor executable %s changed after it was built (recorded SHA-256 %s, now %s).", displayPath(e.auditExe), short(e.auditExeSha), short(got))})
		}
		aout, _ = runLeanProtected(e.sb, e.tc, auditDir, nil, readOnly, leanPath, append([]string{e.auditExe, "--asl",
			e.theorem, e.proofModule, aslCorollaryName, aslCorollaryModule, amarker, "JanusTrusted", aslWordsName}, e.depRoots...)...)
	} else {
		asrc := fmt.Sprintf("import Janus.Tools.Audit\n#eval JanusAudit.runASL %s %s %s %s %s %s %s #[%s]\n",
			leanString(e.theorem), leanString(e.proofModule), leanString(aslCorollaryName), leanString(aslCorollaryModule),
			leanString(amarker), leanString("JanusTrusted"), leanString(aslWordsName), strings.Join(roots, ", "))
		if err := os.WriteFile(filepath.Join(auditDir, "Audit.lean"), []byte(asrc), 0o644); err != nil {
			return aslFail(r, &diag{Invalid: true, Msg: err.Error(), Stage: "ASL audit"})
		}
		aout, _ = runLeanProtected(e.sb, e.tc, auditDir, nil, readOnly, leanPath, e.tc.lean, "--root="+auditDir, filepath.Join(auditDir, "Audit.lean"))
	}
	if err := pinned.check("the ASL audit"); err != nil {
		return aslFail(r, err)
	}
	ar, err := parseAuditRecord(mapPaths(aout), amarker)
	if err != nil {
		if d, ok := err.(*diag); ok {
			d.Msg = "ASL corollary: " + d.Msg
			if d.Stage == "theorem audit" || strings.Contains(d.Msg, "ASL") {
				d.Stage = "ASL audit"
			}
		}
		return aslFail(r, err)
	}

	// 4. Kernel replay of the corollary's closure, ArmASL, Sail and JanusASL included.
	homes := map[string]string{aslWordsModule: wordsDir, aslCorollaryModule: corDir}
	for k, v := range e.homes {
		homes[k] = v
	}
	resolved, err := closureCheck(ar.Modules, append(append([]string{}, dirs...), e.tc.libDir), e.tc.libDir, e.framework, homes)
	if err != nil {
		return aslFail(r, err)
	}
	for m, f := range resolved {
		if !containsStr(aslRoots, moduleRoot(m)) {
			continue
		}
		ok := false
		for _, p := range e.build.pins {
			if rel, rerr := filepath.Rel(p.dir, f); rerr == nil && !strings.HasPrefix(rel, "..") {
				_, ok = p.want[filepath.ToSlash(rel)]
			}
		}
		if !ok {
			return aslFail(r, &diag{Invalid: true, Stage: "ASL module identity",
				Msg:  fmt.Sprintf("the corollary's environment imports %s from %s, which is not a module of the trusted JanusASL build.", m, displayPath(f)),
				Next: "JanusASL, ArmASL and Sail modules come only from the trusted JanusASL build."})
		}
	}
	kr := kernelReplay{Tool: "leanchecker", Modules: []string{}}
	if !e.tc.hasChecker {
		kr.Status, kr.Note = "unavailable", "leanchecker not found in the Lean toolchain"
	} else {
		plan, err := planReplay(resolved, importGraph(ar.Imports), e.tc.cacheID(), e.replayCache)
		if err != nil {
			return aslFail(r, err)
		}
		run := func(argv ...string) (string, error) {
			return runLeanProtected(e.sb, e.tc, auditDir, nil, readOnly, leanPath, argv...)
		}
		if out, err := plan.replay(e.tc.leanchecker, run, plan.modules); err != nil {
			return aslFail(r, replayDiag(mapPaths(out)))
		}
		fresh := ""
		if e.replayFresh {
			if out, err := plan.replayFresh(e.tc.leanchecker, run, aslCorollaryModule); err != nil {
				return aslFail(r, replayDiag(mapPaths(out)))
			}
			fresh = aslCorollaryModule
		}
		kr = plan.report(plan.modules, fresh)
	}
	if err := pinned.check("the ASL kernel replay"); err != nil {
		return aslFail(r, err)
	}
	r.Status = "verified"
	r.Theorem, r.Module = ar.Name, ar.Module
	r.Statement, r.StatementExplicit = ar.Statement, ar.StatementExplicit
	r.Definitions, r.Axioms = ar.Definitions, ar.Axioms
	r.DependencyDefinitions, r.Notes = ar.ExternalDefs, ar.Notes
	r.KernelReplay = &kr
	r.Assumptions = aslAssumptions(ar.Statement)
	return r
}

var coverageRE = regexp.MustCompile(`^(uncovered|class|summary) (.*)$`)

// parseCoverage reads JanusASLWords' marker lines (nil if it printed no summary).
func parseCoverage(out, marker string) *aslCoverage {
	c := &aslCoverage{Classes: map[string]int{}, Uncovered: []string{}}
	done := false
	for _, line := range strings.Split(out, "\n") {
		i := strings.Index(line, marker)
		if i < 0 {
			continue
		}
		m := coverageRE.FindStringSubmatch(strings.TrimRight(line[i+len(marker):], "\r"))
		if m == nil {
			continue
		}
		switch m[1] {
		case "uncovered":
			c.Uncovered = append(c.Uncovered, m[2])
		case "class":
			if name, n, ok := strings.Cut(m[2], " "); ok {
				c.Classes[name], _ = strconv.Atoi(n)
			}
		case "summary":
			if f := strings.Fields(m[2]); len(f) == 2 {
				c.Words, _ = strconv.Atoi(f[0])
				done = true
			}
		}
	}
	if !done {
		return nil
	}
	return c
}

func containsStr(xs []string, x string) bool {
	for _, y := range xs {
		if y == x {
			return true
		}
	}
	return false
}

// aslDiagOf is the error janus exits with when the ASL stage failed (the report is written).
func aslDiagOf(r *aslReport) error {
	if r == nil || r.Status == "verified" {
		return nil
	}
	d := &diag{Invalid: true, Msg: "ASL corollary: not derived.", Stage: "ASL"}
	if f := r.Failure; f != nil {
		d.Msg = "ASL corollary: " + strings.TrimPrefix(f.Message, "ASL corollary: ")
		d.Stage, d.Next = f.Stage, f.Next
	}
	d.Msg += "\n  (The main verification above is unaffected: its theorem is verified and recorded in verified.json.)"
	return d
}

// printASL prints the ASL part of a report (after printVerified).
func printASL(w io.Writer, r *aslReport) {
	if r == nil {
		return
	}
	if r.Status != "verified" {
		fmt.Fprintf(w, "  ASL corollary: NOT derived (%s); see below and verified.json \"asl\"\n", r.Failure.Stage)
		return
	}
	fmt.Fprintf(w, "ASL corollary: Verified: %s (Arm's ASL, model %s)\n", termSafe(r.Theorem), short(r.Model.ArmASLSha256))
	if c := r.Coverage; c != nil {
		fmt.Fprintf(w, "  Coverage: all %d words in the proved subset (%s)\n", c.Words, classSummary(c.Classes))
	}
	fmt.Fprintf(w, "  Axioms: %s\n", strings.Join(r.Axioms, ", "))
	if kr := r.KernelReplay; kr != nil {
		if kr.Status == "passed" {
			fmt.Fprintf(w, "  Kernel replay: %s passed (%s)\n", kr.Tool, replaySummary(*kr))
		} else {
			fmt.Fprintf(w, "  Kernel replay: skipped (%s)\n", kr.Note)
		}
	}
	fmt.Fprintln(w, "  Statement:")
	fmt.Fprintf(w, "    %s\n", strings.ReplaceAll(termSafe(r.Statement), "\n", "\n    "))
	fmt.Fprintln(w, "  Assumptions (see janus explain):")
	for _, a := range r.Assumptions {
		fmt.Fprintf(w, "    - %s\n", a)
	}
}

func classSummary(m map[string]int) string {
	var ks []string
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	var parts []string
	for _, k := range ks {
		parts = append(parts, fmt.Sprintf("%s %d", k, m[k]))
	}
	return strings.Join(parts, ", ")
}

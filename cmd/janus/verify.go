package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"
	"unicode"
)

const defaultTheorem = "Proof.correctness"

var allowedAxioms = []string{"propext", "Quot.sound", "Classical.choice"}

// A dotted Lean name of plain ASCII identifier components. Deliberately strict: the name is
// spliced into a generated Lean file, and ASCII-only rules out lookalike/Unicode names (E2).
var theoremNameRE = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_][A-Za-z0-9_'!?]*)*$`)

type kernelReplay struct {
	Tool    string   `json:"tool"`
	Status  string   `json:"status"`  // "passed" or "unavailable"
	Modules []string `json:"modules"` // every non-core module of the theorem's import closure
	// Cached are the modules whose passing replay was reused from the replay cache (keyed by the
	// SHA-256 of the module and, recursively, of its imports); the rest were replayed in this run.
	Cached []string `json:"cached,omitempty"`
	// Fresh is the module replayed with `leanchecker --fresh` (--replay-fresh): its whole
	// environment, Lean core included, re-checked from an empty environment.
	Fresh string `json:"fresh,omitempty"`
	Note  string `json:"note,omitempty"`
}

type verifiedReport struct {
	Schema    int    `json:"schema"`
	Theorem   string `json:"theorem"`
	Kind      string `json:"kind"`
	Module    string `json:"module"`
	Statement string `json:"statement"`
	// StatementExplicit is the same statement printed with pp.explicit (every implicit and
	// instance argument shown), for human inspection of what the notation stands for.
	StatementExplicit string         `json:"statementExplicit"`
	Axioms            []string       `json:"axioms"`
	AllowedAxioms     []string       `json:"allowedAxioms"`
	KernelReplay      kernelReplay   `json:"kernelReplay"`
	Proof             string         `json:"proof"`
	ProofSha256       string         `json:"proofSha256"`
	Extracted         string         `json:"extracted"`
	ExtractedSha256   string         `json:"extractedSha256"`
	IdentitySha256    string         `json:"identitySha256"`
	Binary            string         `json:"binary"`
	BinarySha256      string         `json:"binarySha256"`
	Symbol            string         `json:"symbol"`
	Address           string         `json:"address"`
	EntryABI          string         `json:"entryABI,omitempty"`    // identity.json entryABI (abi0.go)
	EntrySource       string         `json:"entrySource,omitempty"` // identity.json entrySource
	GoVersion         string         `json:"goVersion"`
	MainModule        string         `json:"mainModule"`
	LeanVersion       string         `json:"leanVersion"`
	JanusRoot         string         `json:"janusRoot"`
	JanusCommit       string         `json:"janusCommit,omitempty"`
	ExtractorVersion  string         `json:"extractorVersion"`
	Timestamp         string         `json:"timestamp"`
	Framework         *frameworkInfo `json:"framework,omitempty"`
	Consumer          *consumerInfo  `json:"consumer,omitempty"`
	Sandbox           sandboxInfo    `json:"sandbox"`
	MemoryGuard       *memGuardInfo  `json:"memoryGuard,omitempty"`
	Definitions       []string       `json:"definitions,omitempty"`
	// DependencyConsts are the constants from declared extra dependencies that the statement
	// (or a proof-local def it uses) mentions: "<name> (<kind>, <module>)".
	DependencyConsts []string `json:"dependencyConstants,omitempty"`
	// Contracts are the extraction's runtime contracts ("name @ address", from identity.json):
	// functions that were not extracted, whose behaviour the theorem can only use through a
	// contract hypothesis in its statement.
	Contracts []string `json:"contracts,omitempty"`
	// Kernel are the extraction's `.syscall` stubs ("name @ address"): the SVC/SYSCALL
	// instructions, environment reads and vDSO clock functions whose effect only the kernel
	// semantics of Janus/Contracts/Syscall*.lean gives (WP-C). Traps are its `.trap` stubs.
	Kernel []string `json:"kernel,omitempty"`
	Traps  []string `json:"traps,omitempty"`
	// ASL is the ASL corollary (--asl): the theorem transferred to Arm's ASL, or why it could not
	// be. Its failure never changes the verified theorem above.
	ASL *aslReport `json:"asl,omitempty"`
	// DependencyDefinitions are the dependency defs the statement reaches, with their bodies
	// (round 7 J1): a dependency def's name and docstring need not say what it means.
	DependencyDefinitions []string `json:"dependencyDefinitions,omitempty"`
	// Notes flag operations of the statement (and of the disclosed definitions) whose standard
	// Lean meaning often reads unexpectedly (round 7 K1). They are not errors.
	Notes []string `json:"notes,omitempty"`
	// Cached: this report is the recorded result of an earlier verification with exactly the
	// same inputs (resultcache.go), made at CachedFrom.
	Cached     bool   `json:"cached,omitempty"`
	CachedFrom string `json:"cachedFrom,omitempty"`
}

type auditResult struct {
	Name              string     `json:"name"`
	Kind              string     `json:"kind"`
	Module            string     `json:"module"`
	Axioms            []string   `json:"axioms"`
	Statement         string     `json:"statement"`
	StatementExplicit string     `json:"statementExplicit"`   // the statement printed with pp.explicit
	Definitions       []string   `json:"definitions"`         // proof-local defs the statement uses, with bodies
	Modules           []string   `json:"modules"`             // every module in the audited environment
	External          []string   `json:"external"`            // dependency constants the statement uses
	ExternalDefs      []string   `json:"externalDefinitions"` // dependency defs, with bodies (round 7 J1)
	Notes             []string   `json:"notes"`               // surprising standard operations (round 7 K1)
	Imports           [][]string `json:"imports"`             // [module, direct imports…] for every non-core module
}

// findJanusRoot locates the Lean project: --janus-root, else $JANUS_ROOT (a Janus checkout,
// built in place), else the framework embedded in this binary, materialized and built once in
// the local cache (see frameworkBase). The build includes targets and stays in use (shared
// lock) until release: nothing else writes to it meanwhile.
func findJanusRoot(flag string, targets ...string) (string, func(), error) {
	fw, err := loadFramework(flag)
	if err != nil {
		return "", func() {}, err
	}
	lake, err := findLake()
	if err != nil {
		return "", func() {}, err
	}
	var lease *frameworkLease
	if fw.Source == "directory" {
		lease, err = fw.acquire(fw.Dir, lake, targets, os.Stderr)
	} else {
		lease, err = fw.frameworkBase(lake, os.Stderr, targets...)
	}
	if err != nil {
		return "", func() {}, err
	}
	return lease.dir, lease.release, nil
}

func findLake() (string, error) {
	if p, err := exec.LookPath("lake"); err == nil {
		return p, nil
	}
	if home, err := os.UserHomeDir(); err == nil {
		p := filepath.Join(home, ".elan", "bin", "lake")
		if _, err := os.Stat(p); err == nil {
			return p, nil
		}
	}
	return "", &diag{Invalid: true, Msg: "lake is not installed or not on PATH.", Stage: "toolchain",
		Next: "Install Lean with elan (https://github.com/leanprover/elan) and rerun."}
}

type leanRunner struct {
	lake, root, buildDir string
	stderr               io.Writer
	// heldFW is the framework lock file this process holds EXCLUSIVELY while the runner's lake runs (the framework build):
	// the child learns it in JANUS_FRAMEWORK_LOCK_HELD_X, so a lock-taking `lake` wrapper (scripts/lib/lanelake/lake) does
	// not wait for a lock its own parent holds. Empty: nothing is claimed.
	heldFW string
}

// run executes `lake <args>` in the Janus root with the build directory on LEAN_PATH
// (lake env appends Janus's own paths, so Janus modules always win).
func (r *leanRunner) run(args ...string) (string, error) {
	cmd := exec.Command(r.lake, args...)
	cmd.Dir = r.root
	env := []string{}
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "LEAN_PATH=") {
			env = append(env, e)
		}
	}
	if r.buildDir != "" {
		env = append(env, "LEAN_PATH="+r.buildDir)
	}
	if len(args) > 0 && args[0] == "build" {
		env = lakeBuildEnv(env)
	}
	env = withoutEnv(env, "JANUS_FRAMEWORK_LOCK_HELD_X") // an inherited claim is never ours
	if r.heldFW != "" {
		env = append(env, "JANUS_FRAMEWORK_LOCK_HELD_X="+r.heldFW)
	}
	cmd.Env = env
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	err := guardRun(cmd)
	return out.String(), err
}

func (r *leanRunner) compile(module string) (string, error) {
	src := filepath.Join(r.buildDir, module+".lean")
	return r.run("env", "lean", "--root="+r.buildDir, "-o", filepath.Join(r.buildDir, module+".olean"), src)
}

var leanMsgRE = regexp.MustCompile(`^(.+?):(\d+):(\d+): (error|warning|info)`)

// leanErrors returns the error message blocks of Lean output.
func leanErrors(out string) []string {
	var errs []string
	var cur []string
	flush := func() {
		if cur != nil {
			errs = append(errs, strings.Join(cur, "\n"))
			cur = nil
		}
	}
	for _, line := range strings.Split(out, "\n") {
		if m := leanMsgRE.FindStringSubmatch(line); m != nil {
			flush()
			if m[4] == "error" {
				cur = []string{line}
			}
			continue
		}
		if cur != nil {
			cur = append(cur, line)
		}
	}
	flush()
	for i := range errs {
		errs[i] = strings.TrimRight(errs[i], "\n ")
	}
	return errs
}

func summarizeLeanErrors(out string, limit int) string {
	errs := leanErrors(out)
	if len(errs) == 0 {
		return ""
	}
	var sb strings.Builder
	fmt.Fprintf(&sb, "Lean errors (%d):", len(errs))
	for _, e := range errs {
		if len(e) > limit {
			e = e[:limit] + " ..."
		}
		sb.WriteString("\n  " + strings.ReplaceAll(e, "\n", "\n    "))
	}
	return sb.String()
}

func cmdVerify(args []string, stdout, stderr io.Writer) error {
	args, flags := takeBoolFlags(args, "json", "fresh", "fresh-framework", "replay-fresh", "unsafe-no-sandbox", "allow-path-deps", "asl")
	pos, opts, err := parseArgs(args, "proof", "theorem", "janus-root", "binary", "proof-root", "results")
	if err != nil {
		return jsonFailure(stdout, flags["json"], usageErr("%v", err))
	}
	if len(pos) != 1 {
		return jsonFailure(stdout, flags["json"], usageErr("verify takes exactly one artifact directory"))
	}
	if flags["fresh"] {
		opts["fresh"] = "true"
	}
	if flags["unsafe-no-sandbox"] {
		opts["unsafe-no-sandbox"] = "true"
	}
	if flags["fresh-framework"] {
		opts["fresh-framework"] = "true"
	}
	if flags["replay-fresh"] {
		opts["replay-fresh"] = "true"
	}
	if flags["asl"] {
		opts["asl"] = "true"
	}
	if flags["allow-path-deps"] {
		if opts["proof-root"] == "" {
			return jsonFailure(stdout, flags["json"], usageErr("--allow-path-deps applies only with --proof-root"))
		}
		opts["allow-path-deps"] = "true"
	}
	outdir := pos[0]
	if strings.Contains(opts["theorem"], "\n") || strings.Contains(opts["theorem"], "::") || opts["results"] != "" {
		return cmdVerifyMany(outdir, opts, flags, stdout, stderr)
	}
	r, err := verifyAndReport(outdir, opts, stderr)
	if err != nil {
		return jsonFailure(stdout, flags["json"], err)
	}
	if flags["json"] {
		b, _ := json.MarshalIndent(r, "", "  ")
		fmt.Fprintf(stdout, "%s\n", b)
	} else {
		printVerified(stdout, outdir, r)
		printASL(stdout, r.ASL)
	}
	if !strings.Contains(r.Statement, "Extracted.") {
		fmt.Fprintln(stderr, "Warning: the statement does not mention any Extracted definition; it says nothing about the extracted code.")
	}
	if w := abiMismatch(r.Statement, statementABI(r.Symbol, r.EntryABI)); w != "" {
		fmt.Fprintln(stderr, w)
	}
	// The ASL stage failed: the report (with the verified theorem) is written; exit 1.
	return aslDiagOf(r.ASL)
}

// verifyAndReport withdraws <outdir>/verified.json, verifies (a single proof file, or a
// module of a consumer package with --proof-root) and writes the new report on success.
func verifyAndReport(outdir string, opts map[string]string, stderr io.Writer) (*verifiedReport, error) {
	reportPath := filepath.Join(outdir, "verified.json")
	// Every attempt starts by withdrawing the previous report; only success writes a new one.
	if err := os.Remove(reportPath); err != nil && !errors.Is(err, fs.ErrNotExist) {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot remove stale %s: %v", displayPath(reportPath), err), Stage: "writing report"}
	}
	// The guard's detection (a systemd-run probe, ~0.2 s, when no delegated cgroup is available)
	// runs in the background; the first job that needs it waits for it (J1).
	if err := memGuardEnvErr(); err != nil {
		return nil, err
	}
	go currentGuard()
	var r *verifiedReport
	var err error
	mark := memMark()
	if opts["proof-root"] != "" {
		logMemGuard(stderr)
		r, err = verifyConsumer(outdir, opts, stderr)
	} else {
		r, err = verify(outdir, opts, stderr)
	}
	r, err = memOutcome(mark, r, err)
	if err != nil {
		_ = os.Remove(reportPath)
		return nil, err
	}
	if err := writeReport(reportPath, r); err != nil {
		return nil, err
	}
	return r, nil
}

func writeReport(reportPath string, r *verifiedReport) error {
	b, _ := json.MarshalIndent(r, "", "  ")
	if err := os.WriteFile(reportPath, append(b, '\n'), 0o644); err != nil {
		_ = os.Remove(reportPath)
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot write %s: %v", displayPath(reportPath), err), Stage: "writing report"}
	}
	return nil
}

func printVerified(stdout io.Writer, outdir string, r *verifiedReport) {
	printVerifiedAt(stdout, outdir, filepath.Join(outdir, "verified.json"), r)
}

func printVerifiedAt(stdout io.Writer, outdir, reportPath string, r *verifiedReport) {
	fmt.Fprintf(stdout, "Verified: %s\n", termSafe(r.Theorem))
	fmt.Fprintf(stdout, "  Module: %s (%s)\n", r.MainModule, r.GoVersion)
	if desc := describeEntry(r.EntryABI, r.EntrySource); desc != "" {
		fmt.Fprintf(stdout, "  Entry: %s at %s (%s)\n", r.Symbol, r.Address, desc)
	} else {
		fmt.Fprintf(stdout, "  Entry: %s at %s\n", r.Symbol, r.Address)
	}
	fmt.Fprintf(stdout, "  Binary: %s (SHA-256 %s)\n", displayPath(resolveBinary(outdir, r.Binary)), r.BinarySha256)
	fmt.Fprintf(stdout, "  Proof: %s\n", displayPath(resolveBinary(outdir, r.Proof)))
	if c := r.Consumer; c != nil {
		fmt.Fprintf(stdout, "  Consumer: %s (%s, module %s, %d source file(s), janus %s)\n", displayPath(c.Root), c.Lakefile, c.Module,
			len(c.Files), c.Dependency.describe())
		for _, d := range c.Dependencies {
			fmt.Fprintf(stdout, "  Dependency: %s %s\n", d.Name, d.describe())
		}
		if len(r.DependencyConsts) > 0 {
			fmt.Fprintf(stdout, "  Dependency constants in the statement: %s\n", strings.Join(r.DependencyConsts, ", "))
		}
		if len(c.Rebuilt) == 0 {
			fmt.Fprintln(stdout, "  Build: every module reused from the support cache")
		} else {
			fmt.Fprintf(stdout, "  Build: rebuilt %s\n", moduleList(c.Rebuilt))
		}
	}
	if f := r.Framework; f != nil {
		fmt.Fprintf(stdout, "  Framework: %s (SHA-256 %s, %d files, %s)\n", f.Source, f.Sha256, f.Files, f.Toolchain)
	}
	switch r.Sandbox.Mode {
	case "none":
		fmt.Fprintln(stdout, "  Sandbox: NONE (--unsafe-no-sandbox: the proof ran unconfined)")
	case "bwrap":
		fmt.Fprintln(stdout, "  Sandbox: bubblewrap (no network, read-only filesystem, private build dir)")
	default:
		fmt.Fprintf(stdout, "  Sandbox: %s (no network, read-only filesystem, private build dir)\n", r.Sandbox.Mode)
	}
	if r.Cached {
		fmt.Fprintf(stdout, "  Cached: the recorded result of an identical verification at %s (same janus, framework build, toolchain, sandbox, artifact and proof; --fresh re-runs it)\n", r.CachedFrom)
	}
	ax := strings.Join(r.Axioms, ", ")
	if ax == "" {
		ax = "(none)"
	}
	fmt.Fprintf(stdout, "  Axioms: %s\n", ax)
	if r.KernelReplay.Status == "passed" {
		fmt.Fprintf(stdout, "  Kernel replay: %s passed (%s)\n", r.KernelReplay.Tool, replaySummary(r.KernelReplay))
	} else {
		fmt.Fprintf(stdout, "  Kernel replay: skipped (%s)\n", r.KernelReplay.Note)
	}
	fmt.Fprintf(stdout, "  Lean: %s\n", r.LeanVersion)
	if len(r.Contracts) > 0 {
		fmt.Fprintf(stdout, "  Runtime contracts assumed: %s (not extracted; see the contract hypotheses of the statement)\n",
			termSafe(strings.Join(r.Contracts, ", ")))
	}
	if len(r.Kernel) > 0 {
		fmt.Fprintf(stdout, "  Kernel interface: %s (.syscall stubs: their effect is the kernel contract of Janus.Kernel, under ReturnsK/EnsuresK only)\n",
			termSafe(strings.Join(r.Kernel, ", ")))
	}
	if len(r.Traps) > 0 {
		fmt.Fprintf(stdout, "  Trap sites: %s (.trap stubs: a run reaching one ends in a trap, Kernel.Traps)\n",
			termSafe(strings.Join(r.Traps, ", ")))
	}
	fmt.Fprintf(stdout, "  Report: %s\n", displayPath(reportPath))
	fmt.Fprintln(stdout, "  Statement:")
	fmt.Fprintf(stdout, "    %s\n", strings.ReplaceAll(termSafe(r.Statement), "\n", "\n    "))
	printDefinitions(stdout, r.Definitions)
	printDependencyDefinitions(stdout, r.DependencyDefinitions)
	printNotes(stdout, r.Notes)
}

// printDependencyDefinitions shows the dependency definitions the statement names, with their
// bodies (round 7 J1).
func printDependencyDefinitions(w io.Writer, defs []string) {
	if len(defs) == 0 {
		return
	}
	fmt.Fprintln(w, "  Dependency definitions used by the statement (pinned source; part of its meaning):")
	for _, d := range defs {
		fmt.Fprintf(w, "    %s\n", strings.ReplaceAll(termSafe(d), "\n", "\n      "))
	}
}

// printNotes shows the round-7 K1 notes: standard Lean meanings that often surprise readers.
func printNotes(w io.Writer, notes []string) {
	if len(notes) == 0 {
		return
	}
	fmt.Fprintln(w, "  Notes (standard Lean meaning that may read unexpectedly; not errors):")
	for _, n := range notes {
		fmt.Fprintf(w, "    - %s\n", strings.ReplaceAll(termSafe(n), "\n", "\n      "))
	}
}

// printDefinitions shows the proof-local definitions the statement names (round 4, D2): the
// statement's meaning depends on them, so they are part of what is reported, not only of
// verified.json.
func printDefinitions(w io.Writer, defs []string) {
	if len(defs) == 0 {
		return
	}
	fmt.Fprintln(w, "  Proof-local definitions used by the statement (part of its meaning):")
	for _, d := range defs {
		fmt.Fprintf(w, "    %s\n", strings.ReplaceAll(termSafe(d), "\n", "\n      "))
	}
}

// termSafe neutralizes control characters (ANSI escapes, carriage returns, …) other than
// newline and tab in report text before it reaches a terminal (round 4, D3): Lean names written
// with «…» may contain them, and they could make the terminal show something other than the
// report.
func termSafe(s string) string {
	var b strings.Builder
	for _, r := range s {
		// Round 7 (H1): every format character (Unicode Cf: all bidi embeddings, overrides,
		// isolates and marks, zero-width spaces and joiners, …) is escaped, not only the
		// overrides and isolates.
		if r == '\n' || r == '\t' || (r >= 0x20 && r != 0x7f && !(r >= 0x80 && r < 0xa0)) &&
			!unicode.Is(unicode.Cf, r) {
			b.WriteRune(r)
			continue
		}
		fmt.Fprintf(&b, "\\u{%x}", r)
	}
	return b.String()
}

// moduleList joins module names, abbreviating long lists (a Mathlib closure has thousands).
func moduleList(mods []string) string {
	if len(mods) <= 12 {
		return strings.Join(mods, ", ")
	}
	return fmt.Sprintf("%s, … and %d more; %d modules", strings.Join(mods[:10], ", "), len(mods)-10, len(mods))
}

// thmOutcome is the outcome of one theorem of a verification: its report, or why it failed.
type thmOutcome struct {
	Theorem string
	Report  *verifiedReport
	Err     error
}

// verify verifies one theorem (opts["theorem"], default Proof.correctness) of a proof file.
func verify(outdir string, opts map[string]string, stderr io.Writer) (*verifiedReport, error) {
	thm := opts["theorem"]
	if thm == "" {
		thm = defaultTheorem
	}
	o := verifyMany(outdir, opts, []string{thm}, stderr)[0]
	return o.Report, o.Err
}

// verifyMany verifies several theorems of ONE proof file in one run: the extraction check, the
// toolchain/sandbox/framework steps, the trusted compile and the proof compile happen once; every
// theorem then gets its own audit (axiom check included), its own result-cache entry and the
// kernel replay of its import closure (shared only by theorems whose closures are identical, as
// the replay is of modules, not of theorems). A theorem's outcome never depends on the others':
// a failing theorem fails alone, while a failure of a shared step (the proof does not compile, a
// pin changed, the kernel rejects a module) fails every theorem that step covers.
func verifyMany(outdir string, opts map[string]string, thms []string, stderr io.Writer) []thmOutcome {
	outs := make([]thmOutcome, len(thms))
	seen := map[string]bool{}
	for i, t := range thms {
		outs[i].Theorem = t
		switch {
		case !theoremNameRE.MatchString(t):
			outs[i].Err = &diag{Invalid: true, Msg: fmt.Sprintf("%q is not a plain dotted Lean name.", t), Stage: "proof selection",
				Next: "Pass --theorem Namespace.name."}
		case seen[t]:
			outs[i].Err = &diag{Invalid: true, Msg: fmt.Sprintf("Theorem %s is listed more than once.", t), Stage: "proof selection",
				Next: "List each theorem once."}
		}
		seen[t] = true
	}
	if err := verifyShared(outdir, opts, outs, stderr); err != nil {
		for i := range outs {
			if outs[i].Report == nil && outs[i].Err == nil {
				outs[i].Err = err
			}
		}
	}
	return outs
}

// verifyShared is verifyMany's body. It fills outs (entries that already have an Err are skipped)
// and returns the error of a shared step, which applies to every entry still without outcome.
func verifyShared(outdir string, opts map[string]string, outs []thmOutcome, stderr io.Writer) error {
	var todo []int
	for i := range outs {
		if outs[i].Err == nil {
			todo = append(todo, i)
		}
	}
	if len(todo) == 0 {
		return nil
	}
	proofPath := opts["proof"]
	if proofPath == "" {
		proofPath = filepath.Join(outdir, "Proof.lean")
	}
	tm := newStageTimer(stderr)
	defer tm.total()

	// 1. Extraction integrity.
	cr, err := check(outdir, opts["binary"])
	if err != nil {
		return err
	}
	tm.mark("extraction check")
	proofSrc, err := os.ReadFile(proofPath)
	if err != nil {
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read proof %s: %v", displayPath(proofPath), err),
			Stage: "proof selection", Next: "Pass --proof path/to/Proof.lean (default: <outdir>/Proof.lean)."}
	}

	// 2. Toolchain, sandbox and the trusted Janus library build. The independent steps run at
	// once (J1): the memory-guard probe, the sandbox self-test, the toolchain query and the
	// framework readiness check (which hashes the framework build and the auditor).
	go currentGuard()
	fw, err := loadFramework(opts["janus-root"])
	if err != nil {
		return err
	}
	lake, err := findLake()
	if err != nil {
		return err
	}
	type sbResult struct {
		sb  *sandbox
		err error
	}
	sbCh := make(chan sbResult, 1)
	go func() {
		sb, err := detectSandbox(opts["unsafe-no-sandbox"] != "")
		sbCh <- sbResult{sb, err}
	}()
	// The toolchain is looked up speculatively in the root the framework will be leased from
	// (the lease only confirms that root; --fresh builds elsewhere and looks again).
	type tcResult struct {
		tc   *toolchain
		err  error
		root string
	}
	tcCh := make(chan tcResult, 1)
	if specRoot := fw.speculativeRoot(opts["fresh"] != ""); specRoot != "" {
		go func() {
			tc, err := findToolchain(lake, specRoot)
			if err == nil {
				tc.cacheID() // the toolchain identity (a stat walk of its library), off the critical path
			}
			tcCh <- tcResult{tc, err, specRoot}
		}()
	} else {
		tcCh <- tcResult{}
	}
	root, rdy, cleanup, err := fw.libraryRootInfo(lake, opts["fresh"] != "", stderr)
	if err != nil {
		return err
	}
	defer cleanup()
	sbr := <-sbCh
	if sbr.err != nil {
		return sbr.err
	}
	sb := sbr.sb
	logMemGuard(stderr)
	tm.mark("sandbox self-test, framework build check")
	// The compiled auditor (janus-audit) of this framework build, and the SHA-256 its build
	// recorded (a --fresh build was made by this process just now).
	auditExe := auditExePath(root)
	var auditExeSha string
	if rdy != nil {
		auditExeSha = rdy.exeSha
	} else {
		auditExeSha = fw.stampedAuditExe(root)
		if opts["fresh"] != "" && fw.Source != "directory" {
			auditExeSha = regularFileSha(auditExe)
		}
	}
	if auditExeSha == "" {
		return &diag{Invalid: true, Stage: "Janus library build",
			Msg: "The framework build in " + displayPath(root) + " records no auditor executable."}
	}
	tr := <-tcCh
	var tc *toolchain
	if tr.tc != nil && tr.root == root {
		tc = tr.tc
	} else if tc, err = findToolchain(lake, root); err != nil {
		return err
	}
	// --asl: the trusted JanusASL build, before the framework is pinned (its Lake build may check
	// the framework's traces).
	var asl *aslBuild
	if opts["asl"] != "" {
		aslRoot := root
		if fw.Source != "directory" && opts["fresh"] != "" {
			aslRoot = "" // not the temporary --fresh build: the cached base (byte-identical)
		}
		if asl, err = buildASLFor(fw, aslRoot, lake, stderr); err != nil {
			return err
		}
		defer asl.release()
	}
	tm.mark("toolchain lookup")
	janusLibDir := filepath.Join(root, ".lake", "build", "lib", "lean")
	// Pin the trusted framework build: every Janus.* module-data file, hashed now and
	// re-verified after every untrusted step, the audit and the replay (R1). The readiness
	// check measured exactly these hashes under the lease; they are not taken a second time.
	var fwPins *pinnedLib
	if rdy != nil && asl == nil {
		fwPins = rdy.pins
	} else {
		fwPins, err = frameworkPins(janusLibDir, fw.Files)
		if err != nil || len(fwPins.want) == 0 {
			return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read the framework build %s: %v", displayPath(janusLibDir), err), Stage: "Janus library build"}
		}
	}
	if len(fwPins.want) == 0 {
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read the framework build %s", displayPath(janusLibDir)), Stage: "Janus library build"}
	}
	pinned := pinSet{fwPins}
	tm.mark("framework pins")

	// The recorded result of an identical earlier verification (resultcache.go), if any.
	idBytes0, _ := os.ReadFile(filepath.Join(outdir, "identity.json"))
	cacheIn := resultInputs{fw: fw, root: root, fwPins: fwPins, auditExeSha: auditExeSha, tc: tc, sb: sb,
		outdir: outdir, proof: proofPath, opts: opts, extracted: cr.Lean, identity: idBytes0,
		binPath: cr.BinPath, binarySha: cr.Identity.BinarySha256, proofSrc: proofSrc}
	// One result-cache key per theorem: each binds its own theorem name (and every other input),
	// so an entry recorded for one theorem can never answer for another.
	resultKeys := make([]string, len(outs))
	if resultCacheOK(sb, opts) {
		// Created before any sandboxed step, so the sandbox's tmpfs always covers it.
		keyOK := false
		if _, err := resultHMACKey(); err == nil {
			keyOK = true
		} else if d, ok := err.(*diag); ok {
			return d // round 8 C1: an unsafe cache is an error, not a silent miss
		}
		prevs := make([]*verifiedReport, len(outs))
		anyHit := false
		for _, i := range todo {
			if !keyOK {
				break
			}
			in := cacheIn
			in.thm = outs[i].Theorem
			resultKeys[i] = in.key()
			if prevs[i] = lookupResult(resultKeys[i]); prevs[i] != nil {
				anyHit = true
			}
		}
		if anyHit {
			// The inputs must still be the ones the keys were computed from.
			cr2, err := check(outdir, opts["binary"])
			proofNow, perr := os.ReadFile(proofPath)
			idNow, _ := os.ReadFile(filepath.Join(outdir, "identity.json"))
			if err == nil && perr == nil && bytes.Equal(cr2.Lean, cr.Lean) && bytes.Equal(proofNow, proofSrc) && bytes.Equal(idNow, idBytes0) {
				var rest []int
				for _, i := range todo {
					if prevs[i] != nil {
						outs[i].Report = cachedReport(prevs[i], fw, root)
					} else {
						rest = append(rest, i)
					}
				}
				todo = rest
				tm.mark("result cache hit")
				if len(todo) == 0 {
					return nil
				}
			}
		}
		tm.mark("result cache miss")
	}

	// The framework replay verdict (replaymark.go), looked up now, before any untrusted step
	// runs: the framework build these pins describe passed `leanchecker Janus` under this
	// toolchain. Without one, the framework is replayed alongside the steps below (speed.go),
	// once per framework build: concurrent verifications wait for one replay under a lock.
	// The verdict is read without a sandbox too (the decision is made before the unconfined proof
	// runs, and the pins it covers are re-checked after every step), but written only by a
	// sandboxed run; --fresh neither reads nor writes it.
	fwKey := frameworkVerdictKey(tc.cacheID(), fwPins)
	// The verdict store: the replay cache of the cache root, or with --fresh and a gate-private
	// store (JANUS_VERDICT_CACHE, verdictstore.go) that store, so that a gate's --fresh rows
	// replay one framework build once. Recording needs a sandbox either way.
	vstore := defaultVerdictStore()
	fwRead := opts["fresh"] == ""
	fwWrite := replayCacheOK(sb, opts)
	if opts["fresh"] != "" {
		ext, ok, err := externalVerdictStore(opts)
		if err != nil {
			return err
		}
		if ok {
			vstore, fwRead, fwWrite = ext, true, sb.mode != "none"
		}
	}
	fwHave, fwLease := false, (*fileLock)(nil)
	if fwRead {
		fwHave, fwLease = vstore.lookup(fwKey)
	}
	var earlyFw *fwReplay
	if tc.hasChecker {
		rb, err := janusRunBase()
		fwRunDir := ""
		if err == nil && !fwHave {
			fwRunDir, err = os.MkdirTemp(rb, "replay-")
			if err == nil {
				defer os.RemoveAll(fwRunDir)
			}
		}
		if err == nil {
			fwPath := tc.leanPathEnv(janusLibDir)
			earlyFw = startFrameworkReplayIn(vstore, tc.leanchecker, func(argv ...string) (string, error) {
				return runLeanProtected(sb, tc, fwRunDir, nil, []string{janusLibDir}, fwPath, argv...)
			}, fwKey, fwPins, fwHave, fwLease, fwRead, fwWrite)
			defer earlyFw.release()
		}
	}
	if earlyFw == nil {
		fwLease.unlock()
	}
	tm.mark("framework replay verdict")

	// 3. Trusted directory: our Extracted and an independently renamed JanusTrusted copy,
	// compiled by us (no proof code), kept read-only for the untrusted steps.
	runBase, err := janusRunBase()
	if err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	trustedDir, err := os.MkdirTemp(runBase, "trusted-")
	if err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	defer os.RemoveAll(trustedDir)
	if err := os.WriteFile(filepath.Join(trustedDir, "Extracted.lean"), cr.Lean, 0o644); err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	if err := os.WriteFile(filepath.Join(trustedDir, "JanusTrusted.lean"), janusTrustedSource(cr.Lean), 0o644); err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	trustedPath := tc.leanPathEnv(trustedDir, janusLibDir)
	compileTrusted := func(mod string) (string, error) {
		return runLean(&sandbox{mode: "none"}, tc, trustedDir, nil, trustedPath,
			tc.lean, "--root="+trustedDir, filepath.Join(trustedDir, mod+".lean"), "-o", filepath.Join(trustedDir, mod+".olean"))
	}
	tm.mark("trusted dir setup")
	// The two trusted compiles are independent and run at once; an identical earlier compile
	// (same toolchain, framework build and sources) is reused from the trusted cache.
	cacheOK := replayCacheOK(sb, opts)
	tkey := trustedCacheKey(tc, fwPins, cr.Lean, janusTrustedSource(cr.Lean))
	var trustedPins *pinnedLib
	trustedHit := false
	if cacheOK {
		if want, ok := loadTrustedCache(tkey, trustedDir); ok {
			trustedHit = true
			trustedPins = &pinnedLib{who: "the trusted Extracted/JanusTrusted build", dir: trustedDir, want: want}
		}
	}
	if !trustedHit {
		outs, errs := compileBoth(compileTrusted, "Extracted", "JanusTrusted")
		if out, err := outs[0], errs[0]; err != nil {
			return &diag{Invalid: true, Msg: "Lean rejected the extracted program " + displayPath(cr.Extracted) + ".\n" + summarizeLeanErrors(out, 2000),
				Stage: "extraction elaboration", Next: "Check that the Janus library matches this extractor version.", Details: out}
		}
		if out, err := outs[1], errs[1]; err != nil {
			return &diag{Invalid: true, Msg: "Lean rejected the trusted copy of the extracted program.\n" + summarizeLeanErrors(out, 2000),
				Stage: "extraction elaboration", Details: out}
		}
	}
	if trustedHit {
		tm.mark("trusted compile (cached)")
	} else {
		tm.mark("trusted compile")
		if trustedPins, err = newPinnedLib("the trusted Extracted/JanusTrusted build", trustedDir, nil); err != nil {
			return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
		}
		if cacheOK {
			storeTrustedCache(tkey, trustedDir, trustedPins.want)
		}
	}
	pinned = append(pinned, trustedPins)
	// A Lean process ran on the framework build only if the trusted compile was not cached; then
	// the pins are checked after it. With a cached compile no process has run since the framework
	// pins were taken, and the trusted pins are the hashes the cache entry was verified against
	// (the check after the proof compile compares the files on disk with them).
	if !trustedHit {
		if err := pinned.check("the trusted compile"); err != nil {
			return err
		}
	}
	tm.mark("trusted pins")

	// 4. Work directory: the proof and the audit script, the only writable place for the
	// sandboxed, untrusted lean processes.
	workDir, err := os.MkdirTemp(runBase, "work-")
	if err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	defer os.RemoveAll(workDir)
	_ = os.Chmod(workDir, 0o700)
	if err := os.WriteFile(filepath.Join(workDir, "Proof.lean"), proofSrc, 0o644); err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	proofPathEnv := tc.leanPathEnv(trustedDir, janusLibDir, workDir)
	searchDirs := []string{trustedDir, janusLibDir, workDir, tc.libDir}
	if err := noForeignModule(map[string]string{
		"Extracted": trustedDir, "JanusTrusted": trustedDir, "Proof": workDir,
	}, searchDirs); err != nil {
		return err
	}
	mapPaths := func(s string) string {
		s = strings.ReplaceAll(s, filepath.Join(workDir, "Proof.lean"), displayPath(proofPath))
		return strings.ReplaceAll(s, filepath.Join(trustedDir, "Extracted.lean"), displayPath(cr.Extracted))
	}
	// The framework and trusted builds stay read-only to every sandboxed step, even if they sit
	// below a writable directory.
	protected := []string{trustedDir, janusLibDir}
	sandboxed := func(argv ...string) (string, error) {
		return runLeanProtected(sb, tc, workDir, nil, protected, proofPathEnv, argv...)
	}

	// The audit's scratch directory, and the prestarted auditors (auditserve.go): they build the
	// clean environment from the trusted builds while the proof compiles.
	auditDir, err := os.MkdirTemp(runBase, "audit-")
	if err != nil {
		return &diag{Invalid: true, Msg: err.Error(), Stage: "theorem audit"}
	}
	defer os.RemoveAll(auditDir)
	var serve *auditServe
	if auditServeEnabled(sb) {
		serve = startAuditServe(sb, tc, auditDir, append(append([]string{}, protected...), workDir), auditExe, "JanusTrusted",
			tc.leanPathEnv(trustedDir, janusLibDir), proofPathEnv, thmNames(outs, todo))
		defer serve.stop()
	}

	tm.mark("work dir setup")
	// Compile the proof, sandboxed. It imports the trusted Extracted; its output is Proof.olean.
	if out, err := sandboxed(tc.lean, "--root="+workDir, filepath.Join(workDir, "Proof.lean"), "-o", filepath.Join(workDir, "Proof.olean")); err != nil {
		out = mapPaths(out)
		msg := "Lean rejected the proof " + displayPath(proofPath) + "."
		if s := summarizeLeanErrors(out, 2000); s != "" {
			msg += "\n" + s
		}
		return &diag{Invalid: true, Msg: msg, Stage: "proof checking",
			Next: "Fix the proof. It must import Extracted (and Janus) and prove " + strings.Join(thmNames(outs, todo), ", ") + ".", Details: out}
	}
	tm.mark("proof compile")
	// The auditor executable is hashed while the pins are checked: both read only files that no
	// untrusted process is running on any more. The result is compared right before the audit.
	exeCh := make(chan string, 1)
	go func() { exeCh <- regularFileSha(auditExe) }()
	if err := pinned.check("the proof compile"); err != nil {
		<-exeCh
		return err
	}
	// The proof's outputs (Proof.olean and anything else the compile left in the work dir) are
	// pinned from here on: the audit and the replay must see the same bytes.
	proofPins, err := newPinnedLib("the proof build", workDir, nil)
	if err != nil {
		<-exeCh
		return &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	pinned = append(pinned, proofPins)
	if _, ok := proofPins.want["Proof.olean"]; !ok {
		<-exeCh
		return &diag{Invalid: true, Msg: "The proof compile produced no Proof.olean.", Stage: "proof build integrity"}
	}

	// 5. Theorem, axiom and statement audit by the trusted janus-audit (no proof code runs).
	tm.mark("pins after proof")
	replayRun := func(argv ...string) (string, error) {
		return runLeanProtected(sb, tc, auditDir, nil, append(protected, workDir), proofPathEnv, argv...)
	}
	// The kernel replay of the three modules of this verification runs alongside the audit
	// (it reads only pinned files; see speed.go). Its result is used below only for modules of
	// the audited closure.
	var early *earlyReplay
	if tc.hasChecker {
		markers := map[string]string{
			"Extracted":    earlyReplayMarker(tc.cacheID(), "Extracted", fwPins, trustedPins),
			"JanusTrusted": earlyReplayMarker(tc.cacheID(), "JanusTrusted", fwPins, trustedPins),
			"Proof":        earlyReplayMarker(tc.cacheID(), "Proof", fwPins, trustedPins, proofPins),
		}
		early = startEarlyReplay(tc.leanchecker, replayRun, []string{"Extracted", "JanusTrusted", "Proof"}, markers, cacheOK)
		defer early.wait()
	}
	// The auditor executable must be the one its trusted build recorded; nothing untrusted runs
	// between this check and its start (the proof compile has ended).
	exeChanged := func() error {
		if got := <-exeCh; got != auditExeSha {
			return &diag{Invalid: true, Stage: "framework integrity",
				Msg:  fmt.Sprintf("the auditor executable %s changed after it was built (recorded SHA-256 %s, now %s).", displayPath(auditExe), short(auditExeSha), short(got)),
				Next: "Something other than janus wrote to the framework build; janus rebuilds it on the next run."}
		}
		return nil
	}
	// A prestarted auditor was started from the file the readiness check hashed, before any
	// untrusted step ran, and a running executable cannot be written; the file is hashed once
	// more, in parallel with the audit, and must still be the recorded one before the result is
	// used. An auditor started now is checked before it starts.
	if serve == nil {
		if err := exeChanged(); err != nil {
			return err
		}
	}
	// Each theorem is audited by the trusted janus-audit (no proof code runs), concurrently: the
	// auditor is a separate process per theorem, with its own nonce marker, on the same pinned
	// build. It runs JanusAudit.runImpl with the arguments the trusted Audit.lean script would
	// pass to JanusAudit.run (auditScript, used by the consumer path).
	markers := make([]string, len(outs))
	auditOuts := make([]string, len(outs))
	slot := map[int]int{} // theorem index -> its prestarted auditor
	for k, i := range todo {
		slot[i] = k
	}
	var awg sync.WaitGroup
	asem := make(chan struct{}, 4)
	for _, i := range todo {
		markers[i] = "janus-audit-" + newNonce() + ": "
		awg.Add(1)
		go func(i int) {
			defer awg.Done()
			if serve != nil { // its own bound on running auditors (auditServeMax)
				auditOuts[i], _ = serve.request(slot[i], markers[i], proofPathEnv)
				return
			}
			asem <- struct{}{}
			defer func() { <-asem }()
			auditOuts[i], _ = runLeanProtected(sb, tc, auditDir, nil, append(protected, workDir), proofPathEnv,
				auditExe, outs[i].Theorem, "Proof", markers[i], "JanusTrusted")
		}(i)
	}
	awg.Wait()
	tm.mark("audit")
	if serve != nil {
		if err := exeChanged(); err != nil {
			return err
		}
	}
	// The audit and the kernel replays of this verification's modules (and of the framework, when
	// it has no verdict yet) have all ended: one pin check covers them (J1; it used to be one after
	// the audit and one after the replay, each re-hashing the framework build).
	early.wait()
	earlyFw.wait()
	tm.mark("early replay wait")
	if err := pinned.check("the audit"); err != nil {
		return err
	}
	tm.mark("pins after audit")
	ars := make([]*auditResult, len(outs))
	var audited []int
	byName := map[string]int{}
	for _, i := range todo {
		ar, err := parseAuditRecord(mapPaths(auditOuts[i]), markers[i])
		if err != nil {
			outs[i].Err = err
			continue
		}
		// Two requested names that resolve to one declaration would be one theorem reported twice.
		if j, dup := byName[ar.Name]; dup {
			outs[i].Err = &diag{Invalid: true, Msg: fmt.Sprintf("%s and %s are the same theorem (%s).", outs[j].Theorem, outs[i].Theorem, ar.Name),
				Stage: "proof selection", Next: "List each theorem once."}
			continue
		}
		byName[ar.Name] = i
		ars[i] = ar
		audited = append(audited, i)
	}
	if len(audited) == 0 {
		return nil
	}

	// 6. Independent kernel replay (leanchecker), sandboxed, of every non-core module of each
	// theorem's import closure; the closure's modules must come from their trusted homes. The
	// replay is of modules: theorems with the same closure (all of one proof file) share one.
	homes := map[string]string{"Extracted": trustedDir, "JanusTrusted": trustedDir, "Proof": workDir}
	type replayOutcome struct {
		kr  kernelReplay
		err error
	}
	replays := map[string]replayOutcome{}
	pinnedHashes := pinned.absHashes()
	lateReplay := false
	krs := make([]kernelReplay, len(outs))
	var replayed []int
	for _, i := range audited {
		ar := ars[i]
		set := append([]string{}, ar.Modules...)
		sort.Strings(set)
		setKey := strings.Join(set, "\n")
		ro, done := replays[setKey]
		if !done {
			ro = func() replayOutcome {
				resolved, err := closureCheck(ar.Modules, searchDirs, tc.libDir, fwPins, homes)
				if err != nil {
					return replayOutcome{err: err}
				}
				kr := kernelReplay{Tool: "leanchecker", Modules: []string{}}
				if !tc.hasChecker {
					kr.Status = "unavailable"
					kr.Note = "leanchecker not found in the Lean toolchain"
					return replayOutcome{kr: kr}
				}
				plan, err := planReplayPinned(resolved, importGraph(ar.Imports), tc.cacheID(), replayCacheOK(sb, opts), pinnedHashes)
				if err != nil {
					return replayOutcome{err: err}
				}
				early.apply(plan)
				earlyFw.apply(plan, fwPins)
				// Modules still to be replayed (not cached, not covered by the early replays) are
				// replayed now, after the pin check above: the pins are checked again after them.
				if len(plan.pending(plan.modules)) > 0 {
					lateReplay = true
				}
				if out, err := plan.replay(tc.leanchecker, replayRun, plan.modules); err != nil {
					return replayOutcome{err: replayDiag(mapPaths(out))}
				}
				fresh := ""
				if opts["replay-fresh"] != "" {
					if out, err := plan.replayFresh(tc.leanchecker, replayRun, "Proof"); err != nil {
						return replayOutcome{err: replayDiag(mapPaths(out))}
					}
					fresh = "Proof"
				}
				return replayOutcome{kr: plan.report(plan.modules, fresh)}
			}()
			replays[setKey] = ro
		}
		if ro.err != nil {
			outs[i].Err = ro.err
			continue
		}
		krs[i] = ro.kr
		replayed = append(replayed, i)
	}
	tm.mark("kernel replay")
	// --replay-fresh replays the proof module once more, in a process of its own.
	if lateReplay || opts["replay-fresh"] != "" {
		if err := pinned.check("the kernel replay"); err != nil {
			return err
		}
		tm.mark("pins after replay")
	}

	// 7. Inputs must still be the ones that were checked.
	cr2, err := check(outdir, opts["binary"])
	if err != nil {
		d := err.(*diag)
		d.Msg = "Artifacts changed during verification: " + d.Msg
		return d
	}
	proofNow, err := os.ReadFile(proofPath)
	if err != nil || !bytes.Equal(proofNow, proofSrc) || !bytes.Equal(cr2.Lean, cr.Lean) {
		return &diag{Invalid: true, Msg: "The proof or Extracted.lean changed during verification.", Stage: "stale input",
			Next: "Rerun janus verify."}
	}

	// 8. --asl: the ASL corollary of each theorem (its outcome is recorded; it never fails the
	// theorem).
	aslReps := make([]*aslReport, len(outs))
	if asl != nil {
		for _, i := range replayed {
			aslReps[i] = runASLStage(&aslEnv{sb: sb, tc: tc, build: asl, runBase: runBase,
				trustedDirs: []string{trustedDir, janusLibDir}, searchDirs: []string{trustedDir, janusLibDir, workDir},
				protected: append(append([]string{}, protected...), workDir), pinned: pinned, framework: fwPins,
				homes:   homes,
				theorem: ars[i].Name, proofModule: "Proof", replayCache: replayCacheOK(sb, opts), replayFresh: opts["replay-fresh"] != "",
				mapPaths: mapPaths, auditExe: auditExe, auditExeSha: auditExeSha})
		}
	}

	tm.mark("final input check")
	idBytes, _ := os.ReadFile(filepath.Join(outdir, "identity.json"))
	fi := fw.info()
	commit := fi.Revision
	if fi.Modified {
		commit += "+dirty"
	}
	for _, i := range replayed {
		ar := ars[i]
		report := &verifiedReport{
			ASL:               aslReps[i],
			Schema:            1,
			Theorem:           ar.Name,
			Kind:              ar.Kind,
			Module:            ar.Module,
			Statement:         ar.Statement,
			StatementExplicit: ar.StatementExplicit,
			Axioms:            ar.Axioms,
			AllowedAxioms:     allowedAxioms,
			KernelReplay:      krs[i],
			Proof:             binaryRef(outdir, proofPath),
			ProofSha256:       sha256Hex(proofSrc),
			Extracted:         "Extracted.lean",
			ExtractedSha256:   sha256Hex(cr.Lean),
			IdentitySha256:    sha256Hex(idBytes),
			Binary:            binaryRef(outdir, cr.BinPath),
			BinarySha256:      cr.Identity.BinarySha256,
			Symbol:            cr.Identity.Symbol,
			Address:           cr.Identity.Address,
			EntryABI:          cr.Identity.EntryABI,
			EntrySource:       cr.Identity.EntrySource,
			GoVersion:         cr.Identity.GoVersion,
			MainModule:        cr.Identity.MainModule,
			LeanVersion:       tc.version,
			JanusRoot:         root,
			JanusCommit:       commit,
			ExtractorVersion:  extractorVersion,
			Timestamp:         time.Now().UTC().Format(time.RFC3339),
			Framework:         fi,
			Sandbox:           sb.info(),
			Definitions:       ar.Definitions,
			Contracts:         cr.Identity.contractList(),
			Notes:             ar.Notes,
		}
		report.Kernel, report.Traps = cr.Identity.kernelLists()
		if resultKeys[i] != "" && bytes.Equal(idBytes, idBytes0) {
			storeResult(resultKeys[i], report)
		}
		outs[i].Report = report
	}
	return nil
}

// thmNames lists the theorem names of outs[idx].
func thmNames(outs []thmOutcome, idx []int) []string {
	var n []string
	for _, i := range idx {
		n = append(n, outs[i].Theorem)
	}
	return n
}

// parseAuditJSON parses the auditor's record and enforces the axiom allow-list. The auditor
// has already enforced the theorem kind and module, the Extracted identity, the trusted-only
// constant rule and that the statement mentions Extracted; this is the one remaining policy
// check (which axioms are permitted) plus marshalling.
func parseAuditJSON(line, full string) (*auditResult, error) {
	ar := &auditResult{}
	if jerr := json.Unmarshal([]byte(line), ar); jerr != nil {
		return nil, &diag{Invalid: true, Msg: "Cannot parse the audit result: " + jerr.Error(), Stage: "theorem audit", Details: full}
	}
	if ar.Kind != "theorem" {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s is a %s, not a theorem.", ar.Name, ar.Kind), Stage: "theorem audit",
			Next: "Select a theorem."}
	}
	allowed := map[string]bool{}
	for _, a := range allowedAxioms {
		allowed[a] = true
	}
	var bad []string
	for _, a := range ar.Axioms {
		if !allowed[a] {
			bad = append(bad, a)
		}
	}
	sort.Strings(ar.Axioms)
	if len(bad) > 0 {
		next := "Remove the dependency. Only " + strings.Join(allowedAxioms, ", ") + " are permitted."
		for _, a := range bad {
			switch a {
			case "sorryAx":
				next = "The proof (or a lemma it uses) contains sorry or an elaboration error; complete it."
			case "Lean.ofReduceBool", "Lean.trustCompiler":
				next = "native_decide and other compiler-trusting tactics are not permitted; use decide or a kernel proof."
			}
		}
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s depends on disallowed axioms: %s.", ar.Name, strings.Join(bad, ", ")),
			Stage: "axiom audit", Next: next}
	}
	if ar.Axioms == nil {
		ar.Axioms = []string{}
	}
	if ar.Definitions == nil {
		ar.Definitions = []string{}
	}
	return ar, nil
}

// classifyAuditError maps the auditor's own ERROR message to a stage and Next hint.
func classifyAuditError(msg, full string) error {
	d := &diag{Invalid: true, Msg: "The audit rejected the proof: " + msg, Stage: "theorem audit", Details: full}
	switch {
	case strings.Contains(msg, "does not define"):
		d.Msg = msg
		d.Next = "Name the theorem with --theorem Namespace.name (default " + defaultTheorem + ")."
	case strings.Contains(msg, "not the checked one"):
		d.Stage = "extraction identity"
		d.Next = "Extracted was shadowed or planted; the imported program is not the one checked from the binary. Rerun in a clean checkout."
	case strings.Contains(msg, "shadows the Extracted namespace"):
		d.Stage = "statement identity"
		d.Next = "Do not declare names under an Extracted namespace in the proof."
	case strings.Contains(msg, "does not mention Extracted"):
		d.Stage = "statement identity"
		d.Next = "State the theorem about Extracted.program or Extracted.entry."
	case strings.Contains(msg, "declared in dependency module"):
		d.Stage = "statement identity"
		d.Next = "A statement may use a dependency's plain defs, theorems and structures, not its instances, classes, opaques or axioms; name the operation (e.g. UInt256.add a b, not a + b)."
	case strings.Contains(msg, "disguised instance") || strings.Contains(msg, "is not a plain def"):
		d.Stage = "statement identity"
		d.Next = "Remove proof-local instances/class values from the statement; use the model's own operations."
	case strings.Contains(msg, "inline instance"):
		d.Stage = "statement identity"
		d.Next = "Instance arguments in the statement must be registered instances: write the operation with its canonical instance (x * y), or name the function (BitVec.add x y). See docs/AUDIT-ROUND2.md CRITICAL-1."
	case strings.Contains(msg, "binds the instance"):
		d.Stage = "statement identity"
		d.Next = "Do not bind instances inside the statement (∃/∀/fun with an [inst : C] binder): state the operation with its canonical instance, or name the function. See docs/AUDIT-ROUND5.md E5."
	case strings.Contains(msg, "out-of-range numeral"):
		d.Stage = "statement identity"
		d.Next = "Write numerals in range for their type (0 rather than 18446744073709551616 at BitVec 64): an out-of-range literal wraps and does not mean what it reads. See docs/AUDIT-ROUND6.md F2."
	case strings.Contains(msg, "lookalike letters"):
		d.Stage = "statement identity"
		d.Next = "Rename the definition with ASCII letters, digits, _ ' ! ? (and subscripts): a lookalike letter makes it print like a trusted constant. See docs/AUDIT-ROUND6.md F1."
	case strings.Contains(msg, "does not round-trip"):
		d.Stage = "statement identity"
		d.Next = "The printed statement must elaborate back to the checked one. Add type ascriptions where the printed text is ambiguous (numerals, coercions, implicit arguments), and do not hide instances or notation."
	case strings.Contains(msg, "which is not Lean/Std core"):
		d.Stage = "statement identity"
		d.Next = "The statement may mention only core, Janus, Extracted and plain proof-local definitions."
	}
	return d
}

// Several theorems in one run (janus verify --theorem A --theorem B ...).
//
// Output layout. Every theorem that passes gets its own report, byte-for-byte what a run of that
// theorem alone writes: <outdir>/verified/<Theorem.Name>.json. When the first theorem of the
// list passes, its report is also written to <outdir>/verified.json, so the readers of the
// single-theorem layout (janus explain <outdir>, scripts) keep working; no other theorem is ever
// recorded there. Every attempt starts by withdrawing verified.json and the verified/ directory's
// reports, and a failed theorem leaves no report of its own, so a file exists exactly for the
// theorems that passed this run. A one-theorem run uses only verified.json, as before.
// With --proof-root a theorem may be written PROOF.lean::Theorem.Name to name its module.

const verifiedDir = "verified"

// parseTheoremSpecs turns the --theorem values into specs, rejecting duplicates and, for
// anything but a --proof-root package, module-qualified entries.
func parseTheoremSpecs(opts map[string]string) ([]thmSpec, error) {
	vals := optsList(opts, "theorem")
	if len(vals) == 0 {
		vals = []string{defaultTheorem}
	}
	var specs []thmSpec
	names := map[string]bool{}
	for _, v := range vals {
		sp := thmSpec{Theorem: v}
		if p, t, ok := strings.Cut(v, "::"); ok {
			if opts["proof-root"] == "" {
				return nil, usageErr("--theorem %s: PROOF.lean::NAME needs --proof-root (a single proof file takes --proof)", v)
			}
			sp = thmSpec{Proof: p, Theorem: t}
		}
		if sp.Theorem == "" {
			sp.Theorem = defaultTheorem
		}
		if names[sp.Theorem] {
			return nil, usageErr("theorem %s is listed more than once (each theorem's report is verified/%s.json)", sp.Theorem, sp.Theorem)
		}
		names[sp.Theorem] = true
		specs = append(specs, sp)
	}
	return specs, nil
}

type multiJSON struct {
	Schema  int             `json:"schema"`
	Results []multiJSONItem `json:"results"`
}

type multiJSONItem struct {
	Theorem string          `json:"theorem"`
	Status  string          `json:"status"` // "verified" or "failed"
	Report  *verifiedReport `json:"report,omitempty"`
	Failure *failureJSON    `json:"failure,omitempty"`
}

func cmdVerifyMany(outdir string, opts map[string]string, flags map[string]bool, stdout, stderr io.Writer) error {
	specs, err := parseTheoremSpecs(opts)
	if err != nil {
		return jsonFailure(stdout, flags["json"], err)
	}
	outs, err := verifyAndReportMany(outdir, opts, specs, stderr)
	if err != nil {
		return jsonFailure(stdout, flags["json"], err)
	}
	failed := 0
	var aslErr error
	mj := multiJSON{Schema: 1}
	for _, o := range outs {
		it := multiJSONItem{Theorem: o.Theorem, Status: "verified", Report: o.Report}
		if o.Err != nil {
			f := toFailureJSON(o.Err)
			it.Status, it.Failure = "failed", &f
			failed++
		} else if aslErr == nil {
			aslErr = aslDiagOf(o.Report.ASL)
		}
		mj.Results = append(mj.Results, it)
	}
	// --results FILE: the per-theorem outcomes, written by this process (a proof cannot write
	// it: the sandbox is read-only outside the work directory). scripts/lib/theorems.sh reads
	// each theorem's status from it.
	if opts["results"] != "" {
		b, _ := json.MarshalIndent(mj, "", "  ")
		if err := os.WriteFile(opts["results"], append(b, '\n'), 0o644); err != nil {
			return jsonFailure(stdout, flags["json"], &diag{Msg: fmt.Sprintf("Cannot write %s: %v", opts["results"], err), Stage: "writing report"})
		}
	}
	if flags["json"] {
		b, _ := json.MarshalIndent(mj, "", "  ")
		fmt.Fprintf(stdout, "%s\n", b)
	} else {
		// One block per theorem, each introduced by a "=== NAME: verified|FAILED ===" line (in this
		// order, on standard output) so a log can be split per theorem.
		for i, o := range outs {
			if o.Err != nil {
				fmt.Fprintf(stdout, "=== %s: FAILED ===\n", termSafe(o.Theorem))
				printDiag(stdout, o.Err)
				continue
			}
			fmt.Fprintf(stdout, "=== %s: verified ===\n", termSafe(o.Theorem))
			rp := filepath.Join(outdir, verifiedDir, o.Theorem+".json")
			if len(outs) == 1 {
				rp = filepath.Join(outdir, "verified.json")
			}
			printVerifiedAt(stdout, outdir, rp, o.Report)
			printASL(stdout, o.Report.ASL)
			if i == 0 && len(outs) > 1 {
				fmt.Fprintf(stdout, "  Report (also): %s\n", displayPath(filepath.Join(outdir, "verified.json")))
			}
			if !strings.Contains(o.Report.Statement, "Extracted.") {
				fmt.Fprintln(stderr, "Warning: the statement of "+termSafe(o.Theorem)+" does not mention any Extracted definition; it says nothing about the extracted code.")
			}
			if w := abiMismatch(o.Report.Statement, statementABI(o.Report.Symbol, o.Report.EntryABI)); w != "" {
				fmt.Fprintln(stderr, w)
			}
			if aslErr == nil {
				aslErr = aslDiagOf(o.Report.ASL)
			}
		}
	}
	if failed > 0 {
		return &diag{Invalid: true, Msg: fmt.Sprintf("%d of %d theorem(s) failed.", failed, len(outs)), Stage: "verify",
			Next: "See the FAIL blocks above (each theorem is checked on its own; the others are unaffected)."}
	}
	return aslErr
}

// withdrawReports removes the reports of an earlier run: verified.json and the *.json reports of
// verified/ (the directory itself too, when that leaves it empty).
func withdrawReports(outdir string) error {
	rm := func(p string) error {
		if err := os.Remove(p); err != nil && !errors.Is(err, fs.ErrNotExist) {
			return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot remove stale %s: %v", displayPath(p), err), Stage: "writing report"}
		}
		return nil
	}
	if err := rm(filepath.Join(outdir, "verified.json")); err != nil {
		return err
	}
	dir := filepath.Join(outdir, verifiedDir)
	ents, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	for _, e := range ents {
		if !e.IsDir() && strings.HasSuffix(e.Name(), ".json") {
			if err := rm(filepath.Join(dir, e.Name())); err != nil {
				return err
			}
		}
	}
	_ = os.Remove(dir)
	return nil
}

// verifyAndReportMany is verifyAndReport for several theorems; see the layout above. The error
// is non-nil only when the run could not start; each theorem's own failure is in its outcome.
func verifyAndReportMany(outdir string, opts map[string]string, specs []thmSpec, stderr io.Writer) ([]thmOutcome, error) {
	if err := withdrawReports(outdir); err != nil {
		return nil, err
	}
	if err := memGuardConfigErr(); err != nil {
		return nil, err
	}
	logMemGuard(stderr)
	mark := memMark()
	var outs []thmOutcome
	if opts["proof-root"] != "" {
		outs = verifyConsumerMany(outdir, opts, specs, stderr)
	} else {
		thms := make([]string, len(specs))
		for i, sp := range specs {
			thms[i] = sp.Theorem
		}
		outs = verifyMany(outdir, opts, thms, stderr)
	}
	for i := range outs {
		outs[i].Report, outs[i].Err = memOutcome(mark, outs[i].Report, outs[i].Err)
		if outs[i].Err != nil {
			outs[i].Report = nil
		}
	}
	for i := range outs {
		o := &outs[i]
		if o.Report == nil {
			continue
		}
		var werr error
		if len(outs) == 1 {
			werr = writeReport(filepath.Join(outdir, "verified.json"), o.Report)
		} else {
			if werr = os.MkdirAll(filepath.Join(outdir, verifiedDir), 0o755); werr == nil {
				werr = writeReport(filepath.Join(outdir, verifiedDir, o.Theorem+".json"), o.Report)
			}
			if werr == nil && i == 0 {
				werr = writeReport(filepath.Join(outdir, "verified.json"), o.Report)
			}
		}
		if werr != nil {
			o.Report, o.Err = nil, werr
		}
	}
	return outs, nil
}

// withoutEnv drops every NAME=... entry of env.
func withoutEnv(env []string, name string) []string {
	out := env[:0:0]
	for _, e := range env {
		if !strings.HasPrefix(e, name+"=") {
			out = append(out, e)
		}
	}
	return out
}

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
	"time"
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
	Definitions       []string       `json:"definitions,omitempty"`
	// DependencyConsts are the constants from declared extra dependencies that the statement
	// (or a proof-local def it uses) mentions: "<name> (<kind>, <module>)".
	DependencyConsts []string `json:"dependencyConstants,omitempty"`
	// ASL is the ASL corollary (--asl): the theorem transferred to Arm's ASL, or why it could not
	// be. Its failure never changes the verified theorem above.
	ASL *aslReport `json:"asl,omitempty"`
}

type auditResult struct {
	Name              string     `json:"name"`
	Kind              string     `json:"kind"`
	Module            string     `json:"module"`
	Axioms            []string   `json:"axioms"`
	Statement         string     `json:"statement"`
	StatementExplicit string     `json:"statementExplicit"` // the statement printed with pp.explicit
	Definitions       []string   `json:"definitions"`       // proof-local defs the statement uses, with bodies
	Modules           []string   `json:"modules"`           // every module in the audited environment
	External          []string   `json:"external"`          // dependency constants the statement uses
	Imports           [][]string `json:"imports"`           // [module, direct imports…] for every non-core module
}

// findJanusRoot locates the Lean project: --janus-root, else $JANUS_ROOT (a Janus checkout,
// built in place), else the framework embedded in this binary, materialized and built once in
// the local cache (see frameworkBase).
func findJanusRoot(flag string) (string, error) {
	fw, err := loadFramework(flag)
	if err != nil {
		return "", err
	}
	if fw.Source == "directory" {
		return fw.Dir, nil
	}
	lake, err := findLake()
	if err != nil {
		return "", err
	}
	return fw.frameworkBase(lake, os.Stderr)
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
	cmd.Env = env
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	err := cmd.Run()
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
	args, flags := takeBoolFlags(args, "json", "fresh", "replay-fresh", "unsafe-no-sandbox", "allow-path-deps", "asl")
	pos, opts, err := parseArgs(args, "proof", "theorem", "janus-root", "binary", "proof-root")
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
	var r *verifiedReport
	var err error
	if opts["proof-root"] != "" {
		r, err = verifyConsumer(outdir, opts, stderr)
	} else {
		r, err = verify(outdir, opts, stderr)
	}
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
	fmt.Fprintf(stdout, "Verified: %s\n", termSafe(r.Theorem))
	fmt.Fprintf(stdout, "  Module: %s (%s)\n", r.MainModule, r.GoVersion)
	fmt.Fprintf(stdout, "  Entry: %s at %s\n", r.Symbol, r.Address)
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
	fmt.Fprintf(stdout, "  Report: %s\n", displayPath(filepath.Join(outdir, "verified.json")))
	fmt.Fprintln(stdout, "  Statement:")
	fmt.Fprintf(stdout, "    %s\n", strings.ReplaceAll(termSafe(r.Statement), "\n", "\n    "))
	printDefinitions(stdout, r.Definitions)
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
		if r == '\n' || r == '\t' || (r >= 0x20 && r != 0x7f && !(r >= 0x80 && r < 0xa0)) &&
			r != 0x202e && r != 0x202d && r != 0x2066 && r != 0x2067 && r != 0x2068 && r != 0x2069 {
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

func verify(outdir string, opts map[string]string, stderr io.Writer) (*verifiedReport, error) {
	thm := opts["theorem"]
	if thm == "" {
		thm = defaultTheorem
	}
	if !theoremNameRE.MatchString(thm) {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%q is not a plain dotted Lean name.", thm), Stage: "proof selection",
			Next: "Pass --theorem Namespace.name."}
	}
	proofPath := opts["proof"]
	if proofPath == "" {
		proofPath = filepath.Join(outdir, "Proof.lean")
	}

	// 1. Extraction integrity.
	cr, err := check(outdir, opts["binary"])
	if err != nil {
		return nil, err
	}
	proofSrc, err := os.ReadFile(proofPath)
	if err != nil {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read proof %s: %v", displayPath(proofPath), err),
			Stage: "proof selection", Next: "Pass --proof path/to/Proof.lean (default: <outdir>/Proof.lean)."}
	}

	// 2. Toolchain, sandbox and the trusted Janus library build.
	fw, err := loadFramework(opts["janus-root"])
	if err != nil {
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
	root, cleanup, err := fw.libraryRoot(lake, opts["fresh"] != "", stderr)
	if err != nil {
		return nil, err
	}
	defer cleanup()
	tc, err := findToolchain(lake, root)
	if err != nil {
		return nil, err
	}
	// --asl: the trusted JanusASL build, before the framework is pinned (its Lake build may check
	// the framework's traces).
	var asl *aslBuild
	if opts["asl"] != "" {
		if asl, err = buildASLFor(fw, root, lake, stderr); err != nil {
			return nil, err
		}
	}
	janusLibDir := filepath.Join(root, ".lake", "build", "lib", "lean")
	// Pin the trusted framework build: every Janus.* module-data file, hashed now and
	// re-verified after every untrusted step, the audit and the replay (R1).
	fwPins, err := frameworkPins(janusLibDir, fw.Files)
	if err != nil || len(fwPins.want) == 0 {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read the framework build %s: %v", displayPath(janusLibDir), err), Stage: "Janus library build"}
	}
	pinned := pinSet{fwPins}

	// 3. Trusted directory: our Extracted and an independently renamed JanusTrusted copy,
	// compiled by us (no proof code), kept read-only for the untrusted steps.
	runBase, err := janusRunBase()
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	trustedDir, err := os.MkdirTemp(runBase, "trusted-")
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	defer os.RemoveAll(trustedDir)
	if err := os.WriteFile(filepath.Join(trustedDir, "Extracted.lean"), cr.Lean, 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	if err := os.WriteFile(filepath.Join(trustedDir, "JanusTrusted.lean"), janusTrustedSource(cr.Lean), 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	trustedPath := tc.leanPathEnv(trustedDir, janusLibDir)
	compileTrusted := func(mod string) (string, error) {
		return runLean(&sandbox{mode: "none"}, tc, trustedDir, nil, trustedPath,
			tc.lean, "--root="+trustedDir, filepath.Join(trustedDir, mod+".lean"), "-o", filepath.Join(trustedDir, mod+".olean"))
	}
	if out, err := compileTrusted("Extracted"); err != nil {
		return nil, &diag{Invalid: true, Msg: "Lean rejected the extracted program " + displayPath(cr.Extracted) + ".\n" + summarizeLeanErrors(out, 2000),
			Stage: "extraction elaboration", Next: "Check that the Janus library matches this extractor version.", Details: out}
	}
	if out, err := compileTrusted("JanusTrusted"); err != nil {
		return nil, &diag{Invalid: true, Msg: "Lean rejected the trusted copy of the extracted program.\n" + summarizeLeanErrors(out, 2000),
			Stage: "extraction elaboration", Details: out}
	}
	trustedPins, err := newPinnedLib("the trusted Extracted/JanusTrusted build", trustedDir, nil)
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	pinned = append(pinned, trustedPins)
	if err := pinned.check("the trusted compile"); err != nil {
		return nil, err
	}

	// 4. Work directory: the proof and the audit script, the only writable place for the
	// sandboxed, untrusted lean processes.
	workDir, err := os.MkdirTemp(runBase, "work-")
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	defer os.RemoveAll(workDir)
	_ = os.Chmod(workDir, 0o700)
	if err := os.WriteFile(filepath.Join(workDir, "Proof.lean"), proofSrc, 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	proofPathEnv := tc.leanPathEnv(trustedDir, janusLibDir, workDir)
	searchDirs := []string{trustedDir, janusLibDir, workDir, tc.libDir}
	if err := noForeignModule(map[string]string{
		"Extracted": trustedDir, "JanusTrusted": trustedDir, "Proof": workDir,
	}, searchDirs); err != nil {
		return nil, err
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

	// Compile the proof, sandboxed. It imports the trusted Extracted; its output is Proof.olean.
	if out, err := sandboxed(tc.lean, "--root="+workDir, filepath.Join(workDir, "Proof.lean"), "-o", filepath.Join(workDir, "Proof.olean")); err != nil {
		out = mapPaths(out)
		msg := "Lean rejected the proof " + displayPath(proofPath) + "."
		if s := summarizeLeanErrors(out, 2000); s != "" {
			msg += "\n" + s
		}
		return nil, &diag{Invalid: true, Msg: msg, Stage: "proof checking",
			Next: "Fix the proof. It must import Extracted (and Janus) and prove " + thm + ".", Details: out}
	}
	if err := pinned.check("the proof compile"); err != nil {
		return nil, err
	}
	// The proof's outputs (Proof.olean and anything else the compile left in the work dir) are
	// pinned from here on: the audit and the replay must see the same bytes.
	proofPins, err := newPinnedLib("the proof build", workDir, nil)
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	pinned = append(pinned, proofPins)
	if _, ok := proofPins.want["Proof.olean"]; !ok {
		return nil, &diag{Invalid: true, Msg: "The proof compile produced no Proof.olean.", Stage: "proof build integrity"}
	}

	// 5. Theorem, axiom and statement audit by the trusted janus-audit (no proof code runs).
	marker := "janus-audit-" + newNonce() + ": "
	auditDir, err := os.MkdirTemp(runBase, "audit-")
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "theorem audit"}
	}
	defer os.RemoveAll(auditDir)
	if err := os.WriteFile(filepath.Join(auditDir, "Audit.lean"), []byte(auditScript(thm, "Proof", marker)), 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "theorem audit"}
	}
	auditOut, _ := runLeanProtected(sb, tc, auditDir, nil, append(protected, workDir), proofPathEnv,
		tc.lean, "--root="+auditDir, filepath.Join(auditDir, "Audit.lean"))
	if err := pinned.check("the audit"); err != nil {
		return nil, err
	}
	ar, err := parseAuditRecord(mapPaths(auditOut), marker)
	if err != nil {
		return nil, err
	}

	// 6. Independent kernel replay (leanchecker), sandboxed, of every non-core module of the
	// theorem's import closure; the closure's modules must come from their trusted homes.
	resolved, err := closureCheck(ar.Modules, searchDirs, tc.libDir, fwPins,
		map[string]string{"Extracted": trustedDir, "JanusTrusted": trustedDir, "Proof": workDir})
	if err != nil {
		return nil, err
	}
	kr := kernelReplay{Tool: "leanchecker", Modules: []string{}}
	if !tc.hasChecker {
		kr.Status = "unavailable"
		kr.Note = "leanchecker not found in the Lean toolchain"
	} else {
		plan, err := planReplay(resolved, importGraph(ar.Imports), tc.version, replayCacheOK(sb, opts))
		if err != nil {
			return nil, err
		}
		replayRun := func(argv ...string) (string, error) {
			return runLeanProtected(sb, tc, auditDir, nil, append(protected, workDir), proofPathEnv, argv...)
		}
		if out, err := plan.replay(tc.leanchecker, replayRun, plan.modules); err != nil {
			return nil, replayDiag(mapPaths(out))
		}
		fresh := ""
		if opts["replay-fresh"] != "" {
			if out, err := plan.replayFresh(tc.leanchecker, replayRun, "Proof"); err != nil {
				return nil, replayDiag(mapPaths(out))
			}
			fresh = "Proof"
		}
		kr = plan.report(plan.modules, fresh)
	}
	if err := pinned.check("the kernel replay"); err != nil {
		return nil, err
	}

	// 7. Inputs must still be the ones that were checked.
	cr2, err := check(outdir, opts["binary"])
	if err != nil {
		d := err.(*diag)
		d.Msg = "Artifacts changed during verification: " + d.Msg
		return nil, d
	}
	proofNow, err := os.ReadFile(proofPath)
	if err != nil || !bytes.Equal(proofNow, proofSrc) || !bytes.Equal(cr2.Lean, cr.Lean) {
		return nil, &diag{Invalid: true, Msg: "The proof or Extracted.lean changed during verification.", Stage: "stale input",
			Next: "Rerun janus verify."}
	}

	// 8. --asl: the ASL corollary (its outcome is recorded; it never fails the theorem above).
	var aslRep *aslReport
	if asl != nil {
		aslRep = runASLStage(&aslEnv{sb: sb, tc: tc, build: asl, runBase: runBase,
			trustedDirs: []string{trustedDir, janusLibDir}, searchDirs: []string{trustedDir, janusLibDir, workDir},
			protected: append(append([]string{}, protected...), workDir), pinned: pinned, framework: fwPins,
			homes:   map[string]string{"Extracted": trustedDir, "JanusTrusted": trustedDir, "Proof": workDir},
			theorem: ar.Name, proofModule: "Proof", replayCache: replayCacheOK(sb, opts), replayFresh: opts["replay-fresh"] != "",
			mapPaths: mapPaths})
	}

	idBytes, _ := os.ReadFile(filepath.Join(outdir, "identity.json"))
	fi := fw.info()
	commit := fi.Revision
	if fi.Modified {
		commit += "+dirty"
	}
	return &verifiedReport{
		ASL:               aslRep,
		Schema:            1,
		Theorem:           ar.Name,
		Kind:              ar.Kind,
		Module:            ar.Module,
		Statement:         ar.Statement,
		StatementExplicit: ar.StatementExplicit,
		Axioms:            ar.Axioms,
		AllowedAxioms:     allowedAxioms,
		KernelReplay:      kr,
		Proof:             binaryRef(outdir, proofPath),
		ProofSha256:       sha256Hex(proofSrc),
		Extracted:         "Extracted.lean",
		ExtractedSha256:   sha256Hex(cr.Lean),
		IdentitySha256:    sha256Hex(idBytes),
		Binary:            binaryRef(outdir, cr.BinPath),
		BinarySha256:      cr.Identity.BinarySha256,
		Symbol:            cr.Identity.Symbol,
		Address:           cr.Identity.Address,
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
	}, nil
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
	case strings.Contains(msg, "does not round-trip"):
		d.Stage = "statement identity"
		d.Next = "The printed statement must elaborate back to the checked one. Add type ascriptions where the printed text is ambiguous (numerals, coercions, implicit arguments), and do not hide instances or notation."
	case strings.Contains(msg, "which is not Lean/Std core"):
		d.Stage = "statement identity"
		d.Next = "The statement may mention only core, Janus, Extracted and plain proof-local definitions."
	}
	return d
}

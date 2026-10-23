package main

import (
	"bytes"
	"crypto/rand"
	"encoding/hex"
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

// A dotted Lean name of plain identifier components. Deliberately strict: the name is
// spliced into a generated Lean file.
var theoremNameRE = regexp.MustCompile(`^[\p{L}_][\p{L}\p{N}_'!?]*(\.[\p{L}_][\p{L}\p{N}_'!?]*)*$`)

type kernelReplay struct {
	Tool    string   `json:"tool"`
	Status  string   `json:"status"` // "passed" or "unavailable"
	Modules []string `json:"modules"`
	Note    string   `json:"note,omitempty"`
}

type verifiedReport struct {
	Schema           int          `json:"schema"`
	Theorem          string       `json:"theorem"`
	Kind             string       `json:"kind"`
	Module           string       `json:"module"`
	Statement        string       `json:"statement"`
	Axioms           []string     `json:"axioms"`
	AllowedAxioms    []string     `json:"allowedAxioms"`
	KernelReplay     kernelReplay `json:"kernelReplay"`
	Proof            string       `json:"proof"`
	ProofSha256      string       `json:"proofSha256"`
	Extracted        string       `json:"extracted"`
	ExtractedSha256  string       `json:"extractedSha256"`
	IdentitySha256   string       `json:"identitySha256"`
	Binary           string       `json:"binary"`
	BinarySha256     string       `json:"binarySha256"`
	Symbol           string       `json:"symbol"`
	Address          string       `json:"address"`
	GoVersion        string       `json:"goVersion"`
	MainModule       string       `json:"mainModule"`
	LeanVersion      string       `json:"leanVersion"`
	JanusRoot        string       `json:"janusRoot"`
	JanusCommit      string       `json:"janusCommit,omitempty"`
	ExtractorVersion string       `json:"extractorVersion"`
	Timestamp        string       `json:"timestamp"`
}

type auditResult struct {
	Name      string   `json:"name"`
	Kind      string   `json:"kind"`
	Module    string   `json:"module"`
	Axioms    []string `json:"axioms"`
	Statement string   `json:"statement"`
}

// findJanusRoot locates the Lean project: --janus-root, $JANUS_ROOT, then the repository
// containing the executable, then the one containing the working directory.
func findJanusRoot(flag string) (string, error) {
	isRoot := func(dir string) bool {
		b, err := os.ReadFile(filepath.Join(dir, "lakefile.toml"))
		return err == nil && regexp.MustCompile(`(?m)^name\s*=\s*"janus"\s*$`).Match(b)
	}
	explicit := flag
	if explicit == "" {
		explicit = os.Getenv("JANUS_ROOT")
	}
	if explicit != "" {
		abs, err := filepath.Abs(explicit)
		if err == nil && isRoot(abs) {
			return abs, nil
		}
		return "", &diag{Invalid: true, Msg: fmt.Sprintf("%s is not the Janus Lean project (no lakefile.toml with name = \"janus\").", explicit),
			Stage: "toolchain", Next: "Pass --janus-root pointing at the Janus repository (or set JANUS_ROOT)."}
	}
	var starts []string
	if exe, err := os.Executable(); err == nil {
		if r, err := filepath.EvalSymlinks(exe); err == nil {
			exe = r
		}
		starts = append(starts, filepath.Dir(exe))
	}
	if wd, err := os.Getwd(); err == nil {
		starts = append(starts, wd)
	}
	for _, d := range starts {
		for {
			if isRoot(d) {
				return d, nil
			}
			parent := filepath.Dir(d)
			if parent == d {
				break
			}
			d = parent
		}
	}
	return "", &diag{Invalid: true, Msg: "Cannot find the Janus Lean project.", Stage: "toolchain",
		Next: "Pass --janus-root pointing at the Janus repository (or set JANUS_ROOT)."}
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
	pos, opts, err := parseArgs(args, "proof", "theorem", "janus-root", "binary")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 1 {
		return usageErr("verify takes exactly one artifact directory")
	}
	outdir := pos[0]
	reportPath := filepath.Join(outdir, "verified.json")
	// Every attempt starts by withdrawing the previous report; only success writes a new one.
	if err := os.Remove(reportPath); err != nil && !errors.Is(err, fs.ErrNotExist) {
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot remove stale %s: %v", displayPath(reportPath), err), Stage: "writing report"}
	}
	r, err := verify(outdir, opts, stderr)
	if err != nil {
		_ = os.Remove(reportPath)
		return err
	}
	b, _ := json.MarshalIndent(r, "", "  ")
	if err := os.WriteFile(reportPath, append(b, '\n'), 0o644); err != nil {
		_ = os.Remove(reportPath)
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot write %s: %v", displayPath(reportPath), err), Stage: "writing report"}
	}
	fmt.Fprintf(stdout, "Verified: %s\n", r.Theorem)
	fmt.Fprintf(stdout, "  Module: %s (%s)\n", r.MainModule, r.GoVersion)
	fmt.Fprintf(stdout, "  Entry: %s at %s\n", r.Symbol, r.Address)
	fmt.Fprintf(stdout, "  Binary: %s (SHA-256 %s)\n", displayPath(resolveBinary(outdir, r.Binary)), r.BinarySha256)
	fmt.Fprintf(stdout, "  Proof: %s\n", displayPath(resolveBinary(outdir, r.Proof)))
	ax := strings.Join(r.Axioms, ", ")
	if ax == "" {
		ax = "(none)"
	}
	fmt.Fprintf(stdout, "  Axioms: %s\n", ax)
	if r.KernelReplay.Status == "passed" {
		fmt.Fprintf(stdout, "  Kernel replay: %s passed (%s)\n", r.KernelReplay.Tool, strings.Join(r.KernelReplay.Modules, ", "))
	} else {
		fmt.Fprintf(stdout, "  Kernel replay: skipped (%s)\n", r.KernelReplay.Note)
	}
	fmt.Fprintf(stdout, "  Lean: %s\n", r.LeanVersion)
	fmt.Fprintf(stdout, "  Report: %s\n", displayPath(reportPath))
	fmt.Fprintln(stdout, "  Statement:")
	fmt.Fprintf(stdout, "    %s\n", strings.ReplaceAll(r.Statement, "\n", "\n    "))
	if !strings.Contains(r.Statement, "Extracted.") {
		fmt.Fprintln(stderr, "Warning: the statement does not mention any Extracted definition; it says nothing about the extracted code.")
	}
	return nil
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

	// 2. Toolchain and Janus library.
	root, err := findJanusRoot(opts["janus-root"])
	if err != nil {
		return nil, err
	}
	lake, err := findLake()
	if err != nil {
		return nil, err
	}
	absOut, _ := filepath.Abs(outdir)
	buildDir := filepath.Join(absOut, ".janus-build")
	lr := &leanRunner{lake: lake, root: root, stderr: stderr}
	if out, err := lr.run("build", "Janus"); err != nil {
		return nil, &diag{Invalid: true, Msg: "Building the Janus Lean library failed: " + err.Error(), Stage: "Janus library build",
			Next: "Run lake build in " + root + " and fix the reported errors.", Details: out}
	}
	leanVersion, err := lr.run("env", "lean", "--version")
	if err != nil {
		return nil, &diag{Invalid: true, Msg: "lean --version failed: " + err.Error(), Stage: "toolchain", Details: leanVersion}
	}
	leanVersion = strings.TrimSpace(leanVersion)

	// 3. Scratch build directory with exactly the checked bytes.
	if err := os.RemoveAll(buildDir); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	if err := os.MkdirAll(buildDir, 0o755); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	lr.buildDir = buildDir
	if err := os.WriteFile(filepath.Join(buildDir, "Extracted.lean"), cr.Lean, 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	if err := os.WriteFile(filepath.Join(buildDir, "Proof.lean"), proofSrc, 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "proof build"}
	}
	mapPaths := func(s string) string {
		s = strings.ReplaceAll(s, filepath.Join(buildDir, "Proof.lean"), displayPath(proofPath))
		return strings.ReplaceAll(s, filepath.Join(buildDir, "Extracted.lean"), displayPath(cr.Extracted))
	}

	if out, err := lr.compile("Extracted"); err != nil {
		out = mapPaths(out)
		return nil, &diag{Invalid: true, Msg: "Lean rejected the extracted program " + displayPath(cr.Extracted) + ".\n" + summarizeLeanErrors(out, 2000),
			Stage: "extraction elaboration", Next: "Check that the Janus library (" + root + ") matches this extractor version.", Details: out}
	}
	extractedOlean, err := os.ReadFile(filepath.Join(buildDir, "Extracted.olean"))
	if err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "extraction elaboration"}
	}

	// 4. The proof.
	if out, err := lr.compile("Proof"); err != nil {
		out = mapPaths(out)
		msg := "Lean rejected the proof " + displayPath(proofPath) + "."
		if s := summarizeLeanErrors(out, 2000); s != "" {
			msg += "\n" + s
		}
		return nil, &diag{Invalid: true, Msg: msg, Stage: "proof checking",
			Next: "Fix the proof. It must import Extracted (and Janus) and prove " + thm + ".", Details: out}
	}
	if again, err := os.ReadFile(filepath.Join(buildDir, "Extracted.olean")); err != nil || !bytes.Equal(again, extractedOlean) {
		return nil, &diag{Invalid: true, Msg: "Extracted.olean changed while the proof was being checked.", Stage: "proof build integrity",
			Next: "The proof must not write files. Remove any IO from it and rerun."}
	}

	// 5. Theorem and axiom audit, in a fresh file importing both modules.
	nonceBytes := make([]byte, 8)
	_, _ = rand.Read(nonceBytes)
	marker := "janus-audit-" + hex.EncodeToString(nonceBytes) + ": "
	audit := fmt.Sprintf(`import Lean
import Extracted
import Proof

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let n := %s.toName
  let env ← getEnv
  let some ci := env.find? n | throwError "janus-audit: unknown constant {n}"
  let kind := match ci with
    | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | _ => "other"
  let axs ← liftCoreM (collectAxioms n)
  let mod := match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]?).getD .anonymous
    | none => .anonymous
  let sig ← liftTermElabM do return toString (← PrettyPrinter.ppSignature n).fmt
  let j := Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
    ("module", toJson mod.toString), ("axioms", toJson (axs.map (·.toString))),
    ("statement", toJson sig)]
  logInfo m!"%s{j.compress}"

#print axioms %s
#check @%s
`, leanString(thm), marker, thm, thm)
	auditPath := filepath.Join(buildDir, "Audit.lean")
	if err := os.WriteFile(auditPath, []byte(audit), 0o644); err != nil {
		return nil, &diag{Invalid: true, Msg: err.Error(), Stage: "theorem audit"}
	}
	out, err := lr.run("env", "lean", "--root="+buildDir, auditPath)
	out = mapPaths(out)
	var ar *auditResult
	for _, line := range strings.Split(out, "\n") {
		if i := strings.Index(line, marker); i >= 0 {
			if ar != nil {
				return nil, &diag{Invalid: true, Msg: "The audit printed more than one result.", Stage: "theorem audit", Details: out}
			}
			ar = &auditResult{}
			if jerr := json.Unmarshal([]byte(line[i+len(marker):]), ar); jerr != nil {
				return nil, &diag{Invalid: true, Msg: "Cannot parse the audit result: " + jerr.Error(), Stage: "theorem audit", Details: out}
			}
		}
	}
	if err != nil || ar == nil {
		msg := fmt.Sprintf("The theorem audit for %s failed.", thm)
		if strings.Contains(out, "unknown constant") || strings.Contains(out, "unknown identifier") {
			msg = fmt.Sprintf("The proof does not define %s.", thm)
		}
		return nil, &diag{Invalid: true, Msg: msg, Stage: "theorem audit",
			Next: "Name the theorem with --theorem Namespace.name (default " + defaultTheorem + ").", Details: out}
	}
	if ar.Kind != "theorem" {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s is a %s, not a theorem.", thm, ar.Kind), Stage: "theorem audit",
			Next: "Select a theorem declared in the proof file."}
	}
	if ar.Module != "Proof" {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s is declared in module %s, not in the proof file.", thm, ar.Module),
			Stage: "theorem audit", Next: "Select a theorem declared in the proof file."}
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
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s depends on disallowed axioms: %s.", thm, strings.Join(bad, ", ")),
			Stage: "axiom audit", Next: next}
	}

	// 6. Independent kernel replay of the imported environment (leanchecker ships with Lean).
	kr := kernelReplay{Tool: "leanchecker", Modules: []string{"Janus", "Extracted", "Proof"}}
	prefix, perr := lr.run("env", "lean", "--print-prefix")
	checker := filepath.Join(strings.TrimSpace(prefix), "bin", "leanchecker")
	if _, serr := os.Stat(checker); perr != nil || serr != nil {
		kr.Status = "unavailable"
		kr.Note = "leanchecker not found in the Lean toolchain"
		kr.Modules = []string{}
	} else {
		out, err := lr.run(append([]string{"env", checker}, kr.Modules...)...)
		if err != nil {
			return nil, &diag{Invalid: true, Msg: "Kernel replay rejected the environment:\n  " + strings.ReplaceAll(strings.TrimSpace(mapPaths(out)), "\n", "\n  "),
				Stage: "kernel replay", Next: "The proof manipulates the environment (e.g. debug.skipKernelTC or addDecl without checking); remove that."}
		}
		kr.Status = "passed"
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

	idBytes, _ := os.ReadFile(filepath.Join(outdir, "identity.json"))
	commit := ""
	if c, err := exec.Command("git", "-C", root, "rev-parse", "HEAD").Output(); err == nil {
		commit = strings.TrimSpace(string(c))
		if st, err := exec.Command("git", "-C", root, "status", "--porcelain", "--", "Janus", "Janus.lean").Output(); err == nil && len(bytes.TrimSpace(st)) > 0 {
			commit += "+dirty"
		}
	}
	if ar.Axioms == nil {
		ar.Axioms = []string{}
	}
	return &verifiedReport{
		Schema:           1,
		Theorem:          ar.Name,
		Kind:             ar.Kind,
		Module:           ar.Module,
		Statement:        ar.Statement,
		Axioms:           ar.Axioms,
		AllowedAxioms:    allowedAxioms,
		KernelReplay:     kr,
		Proof:            binaryRef(outdir, proofPath),
		ProofSha256:      sha256Hex(proofSrc),
		Extracted:        "Extracted.lean",
		ExtractedSha256:  sha256Hex(cr.Lean),
		IdentitySha256:   sha256Hex(idBytes),
		Binary:           binaryRef(outdir, cr.BinPath),
		BinarySha256:     cr.Identity.BinarySha256,
		Symbol:           cr.Identity.Symbol,
		Address:          cr.Identity.Address,
		GoVersion:        cr.Identity.GoVersion,
		MainModule:       cr.Identity.MainModule,
		LeanVersion:      leanVersion,
		JanusRoot:        root,
		JanusCommit:      commit,
		ExtractorVersion: extractorVersion,
		Timestamp:        time.Now().UTC().Format(time.RFC3339),
	}, nil
}

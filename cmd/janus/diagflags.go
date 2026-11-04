package main

// Opt-in diagnostics for the edit-a-failing-proof loop: --full-errors and --keep-workspace.
//
// Neither flag changes what a verification checks, what it trusts, or what the result cache
// records or answers from:
//
//   - --full-errors only changes how a FAILURE is presented. After the verification has already
//     failed, the failing Lean compile is run once more in the same sandbox with Lean's pretty
//     printer limits raised (pp.deepTerms, pp.proofs, pp.maxSteps), its output is shown, and the
//     complete output is written to <outdir>/diag/. The rerun's result is display only: it can
//     never turn a failure into a pass (its exit status is ignored, nothing it produces is
//     loaded, hashed or cached), and a passing verification never runs it.
//   - --keep-workspace leaves a directory in which `lake env lean F.lean` works against the
//     built Extracted module. It is output only: no verification step reads it, no cache key
//     includes it or the flag, and it is never evidence for anything. With the flag the result
//     cache is not READ (a cache hit builds no workspace); a pass is recorded exactly as without
//     the flag.
//
// The flags are carried in the options map, but the cache keys (resultcache.go) hash named
// fields, never the whole map; TestDiagFlagsDoNotEnterCacheKeys pins that.

import (
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"strings"
)

// diagFlags are the two opt-in flags.
type diagFlags struct {
	FullErrors    bool
	KeepWorkspace bool
}

func diagFlagsOf(opts map[string]string) diagFlags {
	return diagFlags{FullErrors: opts["full-errors"] != "", KeepWorkspace: opts["keep-workspace"] != ""}
}

// diagFlagNames are the boolean flags of verify and verify-batch.
var diagFlagNames = []string{"full-errors", "keep-workspace"}

// fullLeanOpts are the Lean options of the display-only rerun: no elision of deep terms or
// proof terms (printed as `⋯` by default) and no step budget for the pretty printer.
var fullLeanOpts = []string{"-Dpp.deepTerms=true", "-Dpp.proofs=true", "-Dpp.maxSteps=1000000000"}

// errLimit is the per-error length limit of summarizeLeanErrors.
func (d diagFlags) errLimit() int {
	if d.FullErrors {
		return math.MaxInt
	}
	return 2000
}

// diagDirName is the directory of an artifact directory that receives full Lean output.
const diagDirName = "diag"

// diagLogName is the file name of the full Lean output of one proof file (a slash path).
func diagLogName(proofRel string) string {
	n := strings.NewReplacer("/", ".", "\\", ".", ":", ".").Replace(strings.TrimPrefix(filepath.ToSlash(proofRel), "./"))
	return strings.Trim(n, ".") + ".lean-output.log"
}

// writeFullOutput writes the complete Lean output to <outdir>/diag/<name> and returns its path
// (empty when it cannot be written; this is a convenience, never an error).
func writeFullOutput(outdir, proofRel, output string) string {
	dir := filepath.Join(outdir, diagDirName)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return ""
	}
	p := filepath.Join(dir, diagLogName(proofRel))
	if err := os.WriteFile(p, []byte(output), 0o644); err != nil {
		return ""
	}
	return p
}

// withFullOutput decorates a proof-checking failure with the path of the full output.
func withFullOutput(d *diag, path string) *diag {
	if path == "" {
		return d
	}
	note := "The complete, untruncated Lean output is in " + displayPath(path) + "."
	if d.Next == "" {
		d.Next = note
	} else {
		d.Next += " " + note
	}
	return d
}

// keptMarker is the file that identifies a directory janus created for --keep-workspace; a
// directory without it is never replaced.
const keptMarker = ".janus-kept-workspace"

// keepSingleFileWorkspace builds, under <outdir>/workspace, a Lake package against the framework
// build at fwRoot that holds the trusted Extracted module (source and olean), a copy of the proof
// and a lakefile, so that `lake env lean Proof.lean` (or any scratch file) works in it. The
// directory is recreated by each run. It returns the directory.
func keepSingleFileWorkspace(outdir, fwRoot, trustedDir, proofPath string, proofSrc []byte) (string, error) {
	dir, err := filepath.Abs(filepath.Join(outdir, "workspace"))
	if err != nil {
		return "", err
	}
	if _, err := os.Lstat(dir); err == nil {
		if _, merr := os.Lstat(filepath.Join(dir, keptMarker)); merr != nil {
			return "", fmt.Errorf("%s exists and was not created by janus --keep-workspace", displayPath(dir))
		}
		if err := os.RemoveAll(dir); err != nil {
			return "", err
		}
	}
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	if err := os.MkdirAll(lib, 0o755); err != nil {
		return "", err
	}
	for _, f := range []string{"Extracted.olean", "Extracted.ilean"} {
		if b, err := os.ReadFile(filepath.Join(trustedDir, f)); err == nil {
			if err := os.WriteFile(filepath.Join(lib, f), b, 0o644); err != nil {
				return "", err
			}
		}
	}
	if _, err := os.Stat(filepath.Join(lib, "Extracted.olean")); err != nil {
		return "", fmt.Errorf("no compiled Extracted module to keep")
	}
	src, err := os.ReadFile(filepath.Join(trustedDir, "Extracted.lean"))
	if err != nil {
		return "", err
	}
	tc, _ := os.ReadFile(filepath.Join(fwRoot, "lean-toolchain"))
	files := map[string][]byte{
		"Extracted.lean": src,
		"Proof.lean":     proofSrc,
		"lean-toolchain": tc,
		"lakefile.toml": []byte("name = \"kept\"\ndefaultTargets = [\"Extracted\"]\n\n[[require]]\nname = \"janus\"\npath = " +
			leanString(fwRoot) + "\n\n[[lean_lib]]\nname = \"Extracted\"\n"),
		keptMarker: []byte("Created by janus verify --keep-workspace. Diagnostic output only: janus never reads this directory back.\n"),
	}
	if len(tc) == 0 {
		delete(files, "lean-toolchain")
	}
	for n, b := range files {
		if err := os.WriteFile(filepath.Join(dir, n), b, 0o644); err != nil {
			return "", err
		}
	}
	return dir, nil
}

// reportKept tells the user where the kept workspace is and how to use it.
func reportKept(w io.Writer, dir, how string) {
	fmt.Fprintf(w, "Kept workspace: %s\n  Use: %s\n  (diagnostics only: janus never reads it back, and `janus cache gc` may remove an unused one)\n", dir, how)
}

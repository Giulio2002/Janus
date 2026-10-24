package main

// Shared machinery for compiling and auditing a proof against a checked Extracted program,
// used by the single-file verify path and (through the audit-script helpers) the consumer
// path. Everything that loads untrusted Lean runs under a sandbox with a private, ordered
// LEAN_PATH; the trusted janus-audit logic runs without executing the proof's initializers,
// and every compiled olean is hash-bound and re-checked. See docs/AUDIT.md F1/F2.

import (
	"bytes"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// toolchain locates the Lean binaries and library of the framework's toolchain. It is found
// once, unsandboxed, without loading any proof code.
type toolchain struct {
	lean, leanchecker, sysroot, libDir string
	version                            string
	hasChecker                         bool
}

func findToolchain(lake, root string) (*toolchain, error) {
	lr := &leanRunner{lake: lake, root: root}
	// The two queries are independent; run them at once.
	var version string
	var verErr error
	done := make(chan struct{})
	go func() {
		defer close(done)
		version, verErr = lr.run("env", "lean", "--version")
	}()
	prefix, err := lr.run("env", "lean", "--print-prefix")
	<-done
	if err != nil {
		return nil, &diag{Invalid: true, Msg: "lean --print-prefix failed: " + err.Error(), Stage: "toolchain", Details: prefix}
	}
	pfx := strings.TrimSpace(prefix)
	if err := verErr; err != nil {
		return nil, &diag{Invalid: true, Msg: "lean --version failed: " + err.Error(), Stage: "toolchain", Details: version}
	}
	tc := &toolchain{
		lean:        filepath.Join(pfx, "bin", "lean"),
		leanchecker: filepath.Join(pfx, "bin", "leanchecker"),
		sysroot:     pfx,
		libDir:      filepath.Join(pfx, "lib", "lean"),
		version:     strings.TrimSpace(version),
	}
	if _, err := os.Stat(tc.leanchecker); err == nil {
		tc.hasChecker = true
	}
	return tc, nil
}

// janusTrustedSource renames the module namespace of a generated Extracted.lean so an
// independently elaborated copy can coexist with the imported Extracted and be compared to it.
func janusTrustedSource(extractedLean []byte) []byte {
	s := string(extractedLean)
	s = strings.Replace(s, "namespace Extracted\n", "namespace JanusTrusted\n", 1)
	s = strings.Replace(s, "end Extracted\n", "end JanusTrusted\n", 1)
	return []byte(s)
}

func newNonce() string {
	b := make([]byte, 12)
	_, _ = rand.Read(b)
	return hex.EncodeToString(b)
}

// auditScript is the trusted Audit.lean run under the full lean frontend. It imports only the
// trusted Janus.Tools.Audit module (never the proof) and calls the auditor, which loads the
// proof's compiled module as data without running its initializers.
// depRoots are the module roots of declared extra dependencies (consumer packages only).
func auditScript(thm, proofModule, marker string, depRoots ...string) string {
	var roots []string
	for _, r := range depRoots {
		roots = append(roots, leanString(r))
	}
	return fmt.Sprintf("import Janus.Tools.Audit\n#eval JanusAudit.run %s %s %s %s #[%s]\n",
		leanString(thm), leanString(proofModule), leanString(marker), leanString("JanusTrusted"), strings.Join(roots, ", "))
}

// leanPathEnv builds a LEAN_PATH with dirs in order (first wins), plus the toolchain lib.
func (tc *toolchain) leanPathEnv(dirs ...string) string {
	return strings.Join(append(dirs, tc.libDir), string(os.PathListSeparator))
}

// baseEnv is the environment for a sandboxed lean process: the parent env with LEAN_PATH and
// the audit's sysroot set, and LEAN_SRC_PATH cleared.
func (tc *toolchain) jobEnv(leanPath string) []string {
	binDir := filepath.Join(tc.sysroot, "bin")
	var env []string
	havePath := false
	for _, e := range os.Environ() {
		switch {
		case strings.HasPrefix(e, "LEAN_PATH="), strings.HasPrefix(e, "LEAN_SRC_PATH="), strings.HasPrefix(e, "JANUS_LEAN_SYSROOT="):
			continue
		case strings.HasPrefix(e, "PATH="):
			// Put the toolchain's own bin first, so `lean` resolves to the real binary and not
			// the elan shim (which needs a configured default toolchain and network).
			env = append(env, "PATH="+binDir+string(os.PathListSeparator)+strings.TrimPrefix(e, "PATH="))
			havePath = true
		default:
			env = append(env, e)
		}
	}
	if !havePath {
		env = append(env, "PATH="+binDir)
	}
	return append(env, "LEAN_PATH="+leanPath, "JANUS_LEAN_SYSROOT="+tc.sysroot)
}

// noForeignModule fails if any directory on the LEAN_PATH other than its home dir contains an
// olean for one of the reserved module names — the defence against a shadowing Extracted/Proof
// (C1), complementing the first-wins ordering and the sandbox's read-only mounts.
func noForeignModule(paths map[string]string, dirs []string) error {
	for mod, home := range paths {
		rel := filepath.FromSlash(strings.ReplaceAll(mod, ".", "/")) + ".olean"
		for _, d := range dirs {
			if d == home {
				continue
			}
			if _, err := os.Stat(filepath.Join(d, rel)); err == nil {
				return &diag{Invalid: true, Stage: "module identity",
					Msg:  fmt.Sprintf("a second %s.olean is on the search path (%s), which could shadow the checked one.", mod, displayPath(filepath.Join(d, rel))),
					Next: "Remove the stray module; janus supplies Extracted and the proof from private directories."}
			}
		}
	}
	return nil
}

// runLean runs a lean/leanchecker command under the sandbox, returning combined output.
func runLean(sb *sandbox, tc *toolchain, workDir string, roWritableExtra []string, leanPath string, argv ...string) (string, error) {
	return runLeanProtected(sb, tc, workDir, roWritableExtra, nil, leanPath, argv...)
}

// runLeanProtected is runLean with protected directories kept read-only even inside the
// writable ones (see sandbox.commandOverlay).
func runLeanProtected(sb *sandbox, tc *toolchain, workDir string, roWritableExtra, protected []string, leanPath string, argv ...string) (string, error) {
	// Expose the LEAN_PATH directories read-only: bubblewrap's private /tmp would otherwise
	// hide a --janus-root (or any search directory) that lives under /tmp.
	var ro []string
	for _, d := range filepath.SplitList(leanPath) {
		if d != "" {
			ro = append(ro, d)
		}
	}
	cmd := sb.commandOverlay(workDir, roWritableExtra, ro, protected, argv, tc.jobEnv(leanPath))
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	err := cmd.Run()
	return out.String(), err
}

var auditRecordRE = regexp.MustCompile(`(?s)\bERROR (.*)$`)

// parseAuditRecord reads the marker-tagged line the auditor prints and returns the record, or
// a diagnostic for an audit error. It never trusts output that lacks the marker.
func parseAuditRecord(out, marker string) (*auditResult, error) {
	idx := strings.Index(out, marker)
	if idx < 0 {
		return nil, &diag{Invalid: true, Msg: "The audit produced no result.", Stage: "theorem audit", Details: out}
	}
	rest := out[idx+len(marker):]
	if nl := strings.IndexByte(rest, '\n'); nl >= 0 {
		rest = rest[:nl]
	}
	rest = strings.TrimRight(rest, "\r")
	if strings.HasPrefix(rest, "ERROR ") {
		msg := strings.TrimPrefix(rest, "ERROR ")
		return nil, classifyAuditError(msg, out)
	}
	return parseAuditJSON(rest, out)
}

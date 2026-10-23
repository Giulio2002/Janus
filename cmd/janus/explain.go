package main

// janus explain: a human-readable account of a verified.json.

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
)

func cmdExplain(args []string, stdout, stderr io.Writer) error {
	pos, _, err := parseArgs(args)
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 1 {
		return usageErr("explain takes exactly one verified.json (or the artifact directory holding it)")
	}
	reportPath := pos[0]
	if fi, err := os.Stat(reportPath); err == nil && fi.IsDir() {
		reportPath = filepath.Join(reportPath, "verified.json")
	}
	raw, err := os.ReadFile(reportPath)
	if err != nil {
		return &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read %s: %v", displayPath(reportPath), err), Stage: "report",
			Next: "Pass the verified.json written by janus verify (it exists only after a successful verification)."}
	}
	var r verifiedReport
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&r); err != nil || r.Schema != 1 || r.Theorem == "" {
		if err == nil {
			err = fmt.Errorf("schema %d, theorem %q", r.Schema, r.Theorem)
		}
		return &diag{Invalid: true, Msg: fmt.Sprintf("%s is not a janus verification report: %v", displayPath(reportPath), err), Stage: "report"}
	}
	outdir := filepath.Dir(reportPath)
	explain(stdout, outdir, reportPath, &r)
	return nil
}

func explain(w io.Writer, outdir, reportPath string, r *verifiedReport) {
	p := func(format string, a ...any) { fmt.Fprintf(w, format+"\n", a...) }
	p("Verification report %s", displayPath(reportPath))
	p("")
	p("What was proved")
	p("  The Lean kernel accepted %s %s, declared in module %s:", r.Kind, r.Theorem, r.Module)
	p("")
	p("    %s", strings.ReplaceAll(r.Statement, "\n", "\n    "))
	p("")
	p("  The guarantee is exactly this statement, with its hypotheses and quantifiers. Its")
	p("  Extracted.* names denote the machine code copied from the binary below; nothing else")
	p("  about the program is claimed.")
	if !strings.Contains(r.Statement, "Extracted.") {
		p("  Warning: the statement mentions no Extracted definition, so it says nothing about the code.")
	}
	p("")

	p("About which code")
	id := readIdentityFile(filepath.Join(outdir, "identity.json"))
	arch := ""
	if id != nil && sha256Hex(id.raw) == r.IdentitySha256 {
		arch = fmt.Sprintf(" for %s/%s", id.GOOS, id.GOARCH)
	}
	p("  Function: %s, entry address %s", r.Symbol, r.Address)
	p("  Program: Go module %s, built with %s%s", r.MainModule, r.GoVersion, arch)
	p("  Binary: %s", displayPath(resolveBinary(outdir, r.Binary)))
	if id != nil && sha256Hex(id.raw) == r.IdentitySha256 {
		var names []string
		for _, f := range id.Functions {
			names = append(names, f.Name+" @ "+f.Address)
		}
		p("  Extracted code: %d function(s): %s", len(id.Functions), strings.Join(names, ", "))
		if len(id.Stubs) > 0 {
			var stubs []string
			for _, s := range id.Stubs {
				stubs = append(stubs, s.Name+" ("+s.Kind+")")
			}
			p("  Runtime stubs (named outcomes, not executed): %s", strings.Join(stubs, ", "))
		}
		dataBytes := 0
		for _, d := range id.Data {
			dataBytes += d.Size
		}
		p("  Read-only data copied: %d object(s), %d byte(s); writable data referenced but not copied: %d", len(id.Data), dataBytes, len(id.SkippedData))
	}
	p("")

	p("How it was checked")
	ax := "none"
	if len(r.Axioms) > 0 {
		ax = strings.Join(r.Axioms, ", ")
	}
	p("  Axioms used: %s (allowed: %s)", ax, strings.Join(r.AllowedAxioms, ", "))
	if r.KernelReplay.Status == "passed" {
		p("  Kernel replay: %s re-checked %s", r.KernelReplay.Tool, strings.Join(r.KernelReplay.Modules, ", "))
	} else {
		p("  Kernel replay: not performed (%s)", r.KernelReplay.Note)
	}
	p("  Lean: %s", r.LeanVersion)
	if f := r.Framework; f != nil {
		rev := f.Revision
		if rev == "" {
			rev = "unknown revision"
		}
		if f.Modified {
			rev += ", modified"
		}
		p("  Janus framework: %s, %d files, SHA-256 %s (%s)", f.Source, f.Files, f.Sha256, rev)
	}
	p("  Extractor: janus %s", r.ExtractorVersion)
	if c := r.Consumer; c != nil {
		p("  Consumer package: %s (%s), module %s, %d source file(s), snapshot SHA-256 %s", displayPath(c.Root), c.Lakefile, c.Module, len(c.Files), c.SnapshotSha256)
		p("  janus dependency: %s", c.Dependency.describe())
	}
	p("  Verified at: %s", r.Timestamp)
	p("")

	p("Hashes (SHA-256), and whether the files on disk still match")
	row := func(what, path, want string) {
		state := "missing"
		if b, err := os.ReadFile(path); err == nil {
			state = "matches"
			if sha256Hex(b) != want {
				state = "CHANGED"
			}
		}
		p("  %-15s %s  %-7s  %s", what, want, state, displayPath(path))
	}
	row("binary", resolveBinary(outdir, r.Binary), r.BinarySha256)
	row("Extracted.lean", filepath.Join(outdir, r.Extracted), r.ExtractedSha256)
	row("identity.json", filepath.Join(outdir, "identity.json"), r.IdentitySha256)
	row("proof", resolveBinary(outdir, r.Proof), r.ProofSha256)
	p("")
	p("To re-establish the result, rerun janus verify; janus check %s re-checks the extraction alone.", displayPath(outdir))
}

type identityWithRaw struct {
	Identity
	raw []byte
}

func readIdentityFile(path string) *identityWithRaw {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil
	}
	var id identityWithRaw
	if json.Unmarshal(b, &id.Identity) != nil {
		return nil
	}
	id.raw = b
	return &id
}

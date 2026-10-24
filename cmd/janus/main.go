// Command janus extracts arm64 machine code of Go functions from an ELF binary into Lean,
// checks extraction artifacts against the binary, and verifies Lean proofs about them.
//
//	janus list <binary> [--filter SUBSTR]
//	janus extract <binary> <symbol> <outdir> [--max-functions N] [--contract SYM]... [--targets SYM,...]
//	janus check <outdir> [--binary PATH]
//	janus verify <outdir> [--proof FILE] [--theorem NAME] [--janus-root DIR] [--binary PATH]
//	janus blockers <binary> <symbol>... [--max-functions N] [--janus-root DIR] [--json FILE]
//
// Exit code 0 on success, 1 on failure; diagnostics go to standard error.
package main

import (
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
)

// diag is a user-facing failure with the stage that failed and what to do next.
type diag struct {
	Invalid bool // printed as "Invalid:" (artifact/proof rejected) rather than "Error:"
	Msg     string
	Stage   string
	Next    string
	Details string
}

func (d *diag) Error() string { return d.Msg }

func printDiag(w io.Writer, err error) {
	d, ok := err.(*diag)
	if !ok {
		fmt.Fprintf(w, "Error: %v\n", err)
		return
	}
	prefix := "Error"
	if d.Invalid {
		prefix = "Invalid"
	}
	fmt.Fprintf(w, "%s: %s\n", prefix, d.Msg)
	if d.Stage != "" {
		fmt.Fprintf(w, "  Stage: %s\n", d.Stage)
	}
	if d.Next != "" {
		fmt.Fprintf(w, "  Next: %s\n", d.Next)
	}
	if d.Details != "" {
		fmt.Fprintf(w, "Details:\n%s\n", strings.TrimRight(d.Details, "\n"))
	}
}

// displayPath shows paths under the working directory relative to it.
func displayPath(p string) string {
	abs, err := filepath.Abs(p)
	if err != nil {
		return p
	}
	wd, err := os.Getwd()
	if err != nil {
		return abs
	}
	if rel, err := filepath.Rel(wd, abs); err == nil && !strings.HasPrefix(rel, "..") {
		return rel
	}
	return abs
}

const usage = `Usage:
  janus list <binary> [--filter SUBSTR]
  janus extract <binary> <symbol> <outdir> [--max-functions N] [--contract SYM]... [--targets SYM,...]
  janus check <outdir> [--binary PATH]
  janus verify <outdir> [--proof FILE] [--theorem NAME] [--janus-root DIR] [--binary PATH]
  janus blockers <binary> <symbol>... [--max-functions N] [--contract SYM]... [--janus-root DIR] [--json FILE]
  janus version
` + extraUsage + `
See docs/CLI.md.
`

// parseArgs splits args into positionals and --flag value / --flag=value options.
// repeatableFlags may be given more than once; their values are joined with "\n" (split them
// with optsList).
var repeatableFlags = map[string]bool{"contract": true, "targets": true}

// optsList returns the values of a repeatable option.
func optsList(opts map[string]string, name string) []string {
	v, ok := opts[name]
	if !ok {
		return nil
	}
	return strings.Split(v, "\n")
}

func parseArgs(args []string, valueFlags ...string) ([]string, map[string]string, error) {
	known := map[string]bool{}
	for _, f := range valueFlags {
		known[f] = true
	}
	var pos []string
	opts := map[string]string{}
	for i := 0; i < len(args); i++ {
		a := args[i]
		if a == "--" {
			pos = append(pos, args[i+1:]...)
			break
		}
		if !strings.HasPrefix(a, "--") {
			pos = append(pos, a)
			continue
		}
		name, val, hasVal := strings.Cut(strings.TrimPrefix(a, "--"), "=")
		if !known[name] {
			return nil, nil, fmt.Errorf("unknown option --%s", name)
		}
		if !hasVal {
			if i+1 >= len(args) {
				return nil, nil, fmt.Errorf("option --%s needs a value", name)
			}
			i++
			val = args[i]
		}
		if prev, ok := opts[name]; ok && repeatableFlags[name] {
			if strings.Contains(val, "\n") {
				return nil, nil, fmt.Errorf("option --%s value contains a newline", name)
			}
			val = prev + "\n" + val
		}
		opts[name] = val
	}
	return pos, opts, nil
}

func main() { os.Exit(run(os.Args[1:], os.Stdout, os.Stderr)) }

func run(args []string, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprint(stderr, usage)
		return 1
	}
	if code, ok := runExtra(args, stdout, stderr); ok {
		return code
	}
	var err error
	switch args[0] {
	case "list":
		err = cmdList(args[1:], stdout)
	case "extract":
		err = cmdExtract(args[1:], stdout, stderr)
	case "check":
		err = cmdCheck(args[1:], stdout)
	case "verify":
		err = cmdVerify(args[1:], stdout, stderr)
	case "blockers":
		err = cmdBlockers(args[1:], stdout, stderr)
	case "version", "--version":
		fmt.Fprintf(stdout, "janus %s\n", extractorVersion)
	case "help", "-h", "--help":
		fmt.Fprint(stdout, usage)
	default:
		fmt.Fprintf(stderr, "Error: unknown command %q\n%s", args[0], usage)
		return 1
	}
	if err != nil {
		printDiag(stderr, err)
		return 1
	}
	return 0
}

func usageErr(format string, a ...any) error {
	return &diag{Msg: fmt.Sprintf(format, a...), Stage: "command line", Next: "Run janus help for the command syntax."}
}

func cmdList(args []string, stdout io.Writer) error {
	pos, opts, err := parseArgs(args, "filter")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 1 {
		return usageErr("list takes exactly one binary")
	}
	b, err := loadBinary(pos[0])
	if err != nil {
		return err
	}
	fmt.Fprintf(stdout, "# %s: %s, %s, %s/%s, functions from %s\n", displayPath(b.Path), b.MainModule, b.GoVersion, b.GOOS, b.GOARCH, b.SymbolSource)
	fmt.Fprintf(stdout, "%-18s %8s  %s\n", "ADDRESS", "SIZE", "NAME")
	for _, f := range b.Funcs {
		if opts["filter"] != "" && !strings.Contains(f.Name, opts["filter"]) {
			continue
		}
		fmt.Fprintf(stdout, "0x%016x %8d  %s\n", f.Addr, f.Size, f.Name)
	}
	return nil
}

func cmdExtract(args []string, stdout, stderr io.Writer) error {
	pos, opts, err := parseArgs(args, "max-functions", "contract", "targets")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 3 {
		return usageErr("extract takes <binary> <symbol> <outdir>")
	}
	maxF := defaultMaxFunctions
	if v, ok := opts["max-functions"]; ok {
		if maxF, err = strconv.Atoi(v); err != nil || maxF < 1 {
			return usageErr("--max-functions needs a positive integer, got %q", v)
		}
	}
	binPath, sym, outdir := pos[0], pos[1], pos[2]
	b, err := loadBinary(binPath)
	if err != nil {
		return err
	}
	var targets []string
	for _, v := range optsList(opts, "targets") {
		targets = append(targets, parseTargets(v)...)
	}
	x, err := extractWith(b, sym, maxF, optsList(opts, "contract"), targets...)
	if err != nil {
		return err
	}
	id := makeIdentity(x, binaryRef(outdir, binPath), maxF)
	if err := writeArtifacts(outdir, x, id); err != nil {
		return &diag{Msg: fmt.Sprintf("Cannot write artifacts to %s: %v", displayPath(outdir), err), Stage: "writing artifacts"}
	}
	words := 0
	for _, s := range x.Segments {
		words += len(s.Words) + len(s.Bytes)
	}
	unit := "word(s)"
	if x.Bin.GOARCH == "amd64" {
		unit = "code byte(s)"
	}
	dataBytes := 0
	for _, d := range x.Data {
		dataBytes += len(d.Bytes)
	}
	fmt.Fprintf(stdout, "Extracted %s: %d function(s), %d %s, %d stub(s), %d data object(s) (%d bytes) into %s\n",
		x.Entry.Name, len(x.Segments), words, unit, len(x.Stubs), len(x.Data), dataBytes, displayPath(filepath.Join(outdir, "Extracted.lean")))
	for _, s := range x.Segments {
		if x.Bin.GOARCH == "amd64" {
			fmt.Fprintf(stdout, "  code  0x%x %4d bytes  %s\n", s.Base, len(s.Bytes), s.Name)
			continue
		}
		fmt.Fprintf(stdout, "  code  0x%x %4d words  %s\n", s.Base, len(s.Words), s.Name)
	}
	for _, s := range x.Stubs {
		fmt.Fprintf(stdout, "  stub  0x%x %-10s %s\n", s.Addr, s.Kind, s.Name)
	}
	for _, c := range x.Contracts {
		fmt.Fprintf(stdout, "  contract 0x%x  %s (not extracted; calls need a contract hypothesis)\n", c.Addr, c.Name)
	}
	for _, d := range x.Data {
		fmt.Fprintf(stdout, "  data  0x%x %4d bytes  %s (%s)\n", d.Base, len(d.Bytes), d.Name, d.Section)
	}
	for _, t := range x.Dynamic {
		how := map[string]string{"targets": "named by --targets", "itab": "method of " + t.From,
			"funcval": "function of " + t.From, "code-address": "address computed at " + t.From}[t.Via]
		fmt.Fprintf(stdout, "  dynamic target 0x%x  %s (%s)\n", t.Addr, t.Name, how)
	}
	for _, o := range x.Omitted {
		fmt.Fprintf(stdout, "  omitted call at 0x%x to %s: %s; not extracted (the model faults with noCode there)\n", o.From, o.Name, o.Reason)
	}
	for _, pat := range x.ContractPatterns {
		hit := false
		cm, _ := newContractMatcher([]string{pat})
		for _, c := range x.Contracts {
			hit = hit || cm.match(c.Name)
		}
		if !hit {
			fmt.Fprintf(stderr, "Note: --contract %q matches no function the extraction calls directly.\n", pat)
		}
	}
	printSkipped(stderr, x.Skipped)
	for _, u := range x.Unresolved {
		fmt.Fprintf(stderr, "Warning: branch at 0x%x targets 0x%x, which is in no known function; it is not extracted (Lean faults with noCode there).\n", u.From, u.Target)
	}
	return nil
}

// printSkipped warns about data references whose bytes are not copied, one line per target.
func printSkipped(w io.Writer, skipped []SkippedData) {
	seen := map[uint64]bool{}
	for _, s := range skipped {
		if seen[s.Target] {
			continue
		}
		seen[s.Target] = true
		what := fmt.Sprintf("0x%x", s.Target)
		if s.Symbol != "" {
			what += " (" + s.Symbol + ")"
		}
		switch s.Reason {
		case "writable":
			fmt.Fprintf(w, "Warning: code at 0x%x references %s in writable section %s; its content is not fixed by the binary, so it is not copied (accesses fault unless a precondition provides that memory).\n", s.From, what, s.Section)
		case "gopclntab":
			fmt.Fprintf(w, "Warning: code at 0x%x references %s in .gopclntab; runtime metadata is not copied.\n", s.From, what)
		case "code":
			fmt.Fprintf(w, "Note: code at 0x%x computes the code address %s in %s; code is not copied as data (a function entry is copied as code, see the dynamic targets).\n", s.From, what, s.Section)
		default:
			fmt.Fprintf(w, "Warning: code at 0x%x references %s, which is in no allocated section; nothing is copied.\n", s.From, what)
		}
	}
}

func cmdCheck(args []string, stdout io.Writer) error {
	pos, opts, err := parseArgs(args, "binary")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 1 {
		return usageErr("check takes exactly one artifact directory")
	}
	r, err := check(pos[0], opts["binary"])
	if err != nil {
		return err
	}
	id := r.Identity
	fmt.Fprintln(stdout, "Valid: extraction artifacts match the binary and recorded settings.")
	fmt.Fprintf(stdout, "  Binary: %s\n", displayPath(r.BinPath))
	fmt.Fprintf(stdout, "  Module: %s (%s, %s/%s)\n", id.MainModule, id.GoVersion, id.GOOS, id.GOARCH)
	fmt.Fprintf(stdout, "  Entry: %s at %s\n", id.Symbol, id.Address)
	fmt.Fprintf(stdout, "  Functions: %d, stubs: %d, data objects: %d\n", len(id.Functions), len(id.Stubs), len(id.Data))
	if len(id.Contracts) > 0 {
		fmt.Fprintf(stdout, "  Runtime contracts (not extracted): %s\n", strings.Join(id.contractList(), ", "))
	}
	fmt.Fprintf(stdout, "  Code: %s\n", displayPath(r.Extracted))
	fmt.Fprintf(stdout, "  Manifest: %s\n", displayPath(filepath.Join(r.Outdir, "identity.json")))
	fmt.Fprintln(stdout, "  Matched: binary SHA-256, extractor version, Extracted.lean SHA-256, regenerated words and data.")
	return nil
}

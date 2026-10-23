// Command janus extracts arm64 machine code of Go functions from an ELF binary into Lean,
// checks extraction artifacts against the binary, and verifies Lean proofs about them.
//
//	janus list <binary> [--filter SUBSTR]
//	janus extract <binary> <symbol> <outdir> [--max-functions N]
//	janus check <outdir> [--binary PATH]
//	janus verify <outdir> [--proof FILE] [--theorem NAME] [--janus-root DIR] [--binary PATH]
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
  janus extract <binary> <symbol> <outdir> [--max-functions N]
  janus check <outdir> [--binary PATH]
  janus verify <outdir> [--proof FILE] [--theorem NAME] [--janus-root DIR] [--binary PATH]
  janus version

See docs/CLI.md.
`

// parseArgs splits args into positionals and --flag value / --flag=value options.
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
	pos, opts, err := parseArgs(args, "max-functions")
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
	x, err := extract(binPath, sym, maxF)
	if err != nil {
		return err
	}
	id := makeIdentity(x, binaryRef(outdir, binPath), maxF)
	if err := writeArtifacts(outdir, x, id); err != nil {
		return &diag{Msg: fmt.Sprintf("Cannot write artifacts to %s: %v", displayPath(outdir), err), Stage: "writing artifacts"}
	}
	words := 0
	for _, s := range x.Segments {
		words += len(s.Words)
	}
	fmt.Fprintf(stdout, "Extracted %s: %d function(s), %d word(s), %d stub(s) into %s\n",
		x.Entry.Name, len(x.Segments), words, len(x.Stubs), displayPath(filepath.Join(outdir, "Extracted.lean")))
	for _, s := range x.Segments {
		fmt.Fprintf(stdout, "  code  0x%x %4d words  %s\n", s.Base, len(s.Words), s.Name)
	}
	for _, s := range x.Stubs {
		fmt.Fprintf(stdout, "  stub  0x%x %-10s %s\n", s.Addr, s.Kind, s.Name)
	}
	for _, u := range x.Unresolved {
		fmt.Fprintf(stderr, "Warning: branch at 0x%x targets 0x%x, which is in no known function; it is not extracted (Lean faults with noCode there).\n", u.From, u.Target)
	}
	return nil
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
	fmt.Fprintf(stdout, "  Functions: %d, stubs: %d\n", len(id.Functions), len(id.Stubs))
	fmt.Fprintf(stdout, "  Code: %s\n", displayPath(r.Extracted))
	fmt.Fprintf(stdout, "  Manifest: %s\n", displayPath(filepath.Join(r.Outdir, "identity.json")))
	fmt.Fprintln(stdout, "  Matched: binary SHA-256, extractor version, Extracted.lean SHA-256 and regenerated words.")
	return nil
}

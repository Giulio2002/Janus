package main

import (
	"encoding/json"
	"fmt"
	"io"
)

// Commands added on top of the core list/extract/check/verify/blockers set. main.go's run
// dispatches here first (runExtra), so the commands live in their own files.
var extraCommands = map[string]func(args []string, stdout, stderr io.Writer) error{
	"verify-batch": cmdVerifyBatch,
	"init":         cmdInit,
	"explain":      cmdExplain,
	"framework":    cmdFramework,
}

const extraUsage = `  janus verify <outdir> --proof FILE --proof-root PKG [--theorem NAME] [--json] [--fresh] [--asl]
  janus verify-batch <requests.json> [--results FILE] [--json] [--fresh] [--janus-root DIR] [--asl]
  janus init <dir> [--name NAME] [--rev REV | --janus-path DIR] [--no-update]
  janus explain <verified.json | outdir>
  janus framework [--janus-root DIR] [--json]
`

// runExtra runs one of extraCommands; ok is false for any other command.
func runExtra(args []string, stdout, stderr io.Writer) (code int, ok bool) {
	if len(args) == 0 {
		return 0, false
	}
	cmd, ok := extraCommands[args[0]]
	if !ok {
		return 0, false
	}
	if err := cmd(args[1:], stdout, stderr); err != nil {
		printDiag(stderr, err)
		return 1, true
	}
	return 0, true
}

// takeBoolFlags removes the boolean --name flags from args (parseArgs only knows options
// with values) and reports which were present.
func takeBoolFlags(args []string, names ...string) ([]string, map[string]bool) {
	known := map[string]bool{}
	for _, n := range names {
		known[n] = true
	}
	set := map[string]bool{}
	var rest []string
	for i, a := range args {
		if a == "--" {
			rest = append(rest, args[i:]...)
			break
		}
		if len(a) > 2 && a[:2] == "--" && known[a[2:]] {
			set[a[2:]] = true
			continue
		}
		rest = append(rest, a)
	}
	return rest, set
}

// failureJSON is what --json prints on standard output when a command fails.
type failureJSON struct {
	Status  string `json:"status"` // "invalid" or "error"
	Message string `json:"message"`
	Stage   string `json:"stage,omitempty"`
	Next    string `json:"next,omitempty"`
	Details string `json:"details,omitempty"`
}

func toFailureJSON(err error) failureJSON {
	f := failureJSON{Status: "error", Message: err.Error()}
	if d, ok := err.(*diag); ok {
		if d.Invalid {
			f.Status = "invalid"
		}
		f.Stage, f.Next, f.Details = d.Stage, d.Next, d.Details
	}
	return f
}

// jsonFailure prints err as JSON on stdout when enabled, and returns it unchanged (so the
// human-readable diagnostic still goes to standard error).
func jsonFailure(stdout io.Writer, enabled bool, err error) error {
	if enabled && err != nil {
		b, _ := json.MarshalIndent(toFailureJSON(err), "", "  ")
		fmt.Fprintf(stdout, "%s\n", b)
	}
	return err
}

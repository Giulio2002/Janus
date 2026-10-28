package main

// Prestarted auditors (J1, docs/SOUNDNESS.md "Prestarted auditors").
//
// The compiled auditor builds two environments: the audited one (the proof's closure) and a clean
// one that imports only Extracted and Janus, with initializers, so that the statement is printed
// without any notation the proof defines. The clean one does not depend on the proof, and building
// it costs about as much as the proof compile's own import of the same library. So the auditor is
// started in `--serve` mode before the proof compile: it builds the clean environment from the
// pinned framework build and the trusted Extracted (its search path holds only those and the
// toolchain), then waits on its standard input. Once the proof has compiled and every pin has been
// checked, one request line (theorem, proof module, nonce marker, and the final search path with
// the proof's directory added) makes it import the proof's closure and run exactly the audit it
// would have run from a cold start. The nonce marker is sent only then, so nothing that ran earlier
// has seen it.
//
// What this does not change: the auditor is the same pinned executable, in the same sandbox
// (bwrap: no network, read-only filesystem, the proof's directory read-only, its own scratch
// directory); the audit logic and every check in it; the pin checks after the proof compile and
// after the audit; the order in which the proof's bytes are first read (after the compile, after the
// pins). The trusted modules it reads while the proof compiles are read-only to both sandboxes. A
// proof that compiles, fails, or is cancelled ends the prestarted auditors (their standard input
// closes; a cancelled context kills them).

import (
	"context"
	"fmt"
	"os"
	"strings"
	"sync"
)

// auditServeMax bounds how many auditor processes run at once (as for the classic audit).
const auditServeMax = 4

type auditGo struct{ marker, leanPath string }

type auditJob struct {
	thm  string
	goCh chan auditGo // buffered: the request, or closed for "no request"
	done chan struct{}
	out  string
	err  error
}

// auditServe is the set of prestarted auditors of one verification.
type auditServe struct {
	cancel context.CancelFunc
	jobs   []*auditJob
	wg     sync.WaitGroup
}

// auditServeEnabled: only with a sandbox. Unconfined (--unsafe-no-sandbox), nothing runs
// alongside the proof compile and the auditor starts after it, as before.
func auditServeEnabled(sb *sandbox) bool {
	return sb.mode != "none" && os.Getenv("JANUS_AUDIT_PRESTART") != "off"
}

// startAuditServe starts one auditor per theorem in serve mode (at most auditServeMax at a time;
// the others start when one finishes). The auditors run in workDir's sandbox shape of the classic
// audit: scratchDir writable, protected (plus the proof's directory) read-only. servePath is their
// LEAN_PATH until the request, fullPath the one the request installs; fullPath's directories are
// mounted from the start.
func startAuditServe(sb *sandbox, tc *toolchain, scratchDir string, protected []string, auditExe, trusted, servePath, fullPath string, thms []string) *auditServe {
	ctx, cancel := context.WithCancel(context.Background())
	as := &auditServe{cancel: cancel}
	csb := sb.withContext(ctx)
	sem := make(chan struct{}, auditServeMax)
	for _, thm := range thms {
		j := &auditJob{thm: thm, goCh: make(chan auditGo, 1), done: make(chan struct{})}
		as.jobs = append(as.jobs, j)
		as.wg.Add(1)
		go func() {
			defer as.wg.Done()
			defer close(j.done)
			select {
			case sem <- struct{}{}:
				defer func() { <-sem }()
			case <-ctx.Done():
				return
			}
			if ctx.Err() != nil {
				return
			}
			r, w, err := os.Pipe()
			if err != nil {
				j.err = err
				return
			}
			defer r.Close()
			cmd, out := leanCmd(csb, tc, scratchDir, nil, protected, fullPath, servePath, []string{auditExe, "--serve", trusted})
			cmd.Stdin = r
			ran := make(chan error, 1)
			go func() { ran <- guardRun(cmd) }()
			select {
			case g, ok := <-j.goCh:
				if ok {
					// theorem, proof module, marker and search path: single-line, tab-separated
					// (the theorem name is a plain dotted name; the others contain no tab or newline).
					fmt.Fprintf(w, "%s\tProof\t%s\t%s\n", j.thm, g.marker, g.leanPath)
				}
			case <-ctx.Done():
			}
			w.Close() // end of requests: the auditor exits after its answer (or at once if none came)
			j.err = <-ran
			j.out = out.String()
		}()
	}
	return as
}

// request sends the audit request to theorem i's auditor and waits for it to end; it returns the
// auditor's output (which holds the marker-tagged record).
func (as *auditServe) request(i int, marker, leanPath string) (string, error) {
	j := as.jobs[i]
	if strings.ContainsAny(marker+leanPath, "\t\n") {
		return "", fmt.Errorf("audit request contains a separator")
	}
	j.goCh <- auditGo{marker, leanPath}
	<-j.done
	return j.out, j.err
}

// stop cancels the auditors that have not been asked, kills the ones still running and waits for
// all of them.
func (as *auditServe) stop() {
	if as == nil {
		return
	}
	as.cancel()
	as.wg.Wait()
}

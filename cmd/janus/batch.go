package main

// janus verify-batch: many requests against one snapshot of each consumer package, sharing
// the Lean build. See docs/CONSUMERS.md#batch-verification.

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

type batchManifest struct {
	Schema    int            `json:"schema"`
	ProofRoot string         `json:"proofRoot"`
	Requests  []batchRequest `json:"requests"`
}

type batchRequest struct {
	Outdir    string `json:"outdir"`
	Proof     string `json:"proof"`
	Theorem   string `json:"theorem"`
	ProofRoot string `json:"proofRoot"`
	Binary    string `json:"binary"`
}

type batchResult struct {
	Index     int          `json:"index"`
	Outdir    string       `json:"outdir"`
	Proof     string       `json:"proof"`
	Theorem   string       `json:"theorem"`
	ProofRoot string       `json:"proofRoot,omitempty"`
	Status    string       `json:"status"` // "verified" or "failed"
	Module    string       `json:"module,omitempty"`
	Group     int          `json:"group"` // index into groups, -1 when none
	Report    string       `json:"report,omitempty"`
	Failure   *failureJSON `json:"failure"`
	// ASL is the outcome of the ASL stage (--asl): "verified" or "invalid" (then ASLFailure).
	ASL        string       `json:"asl,omitempty"`
	ASLFailure *failureJSON `json:"aslFailure,omitempty"`
}

type batchGroup struct {
	ProofRoot       string   `json:"proofRoot"`
	SnapshotSha256  string   `json:"snapshotSha256"`
	ExtractedSha256 string   `json:"extractedSha256"`
	Workspace       string   `json:"workspace"`
	Requests        []int    `json:"requests"`
	Rebuilt         []string `json:"rebuilt"`
}

type batchResults struct {
	Schema int `json:"schema"`
	Passed int `json:"passed"`
	Failed int `json:"failed"`
	// ASLFailed counts verified requests whose ASL stage failed (--asl).
	ASLFailed int           `json:"aslFailed,omitempty"`
	Snapshots int           `json:"snapshots"`
	Groups    []batchGroup  `json:"groups"`
	Results   []batchResult `json:"results"`
}

func cmdVerifyBatch(args []string, stdout, stderr io.Writer) error {
	args, flags := takeBoolFlags(args, "json", "fresh", "unsafe-no-sandbox", "allow-path-deps", "asl")
	pos, opts, err := parseArgs(args, "results", "janus-root")
	if err != nil {
		return jsonFailure(stdout, flags["json"], usageErr("%v", err))
	}
	if len(pos) != 1 {
		return jsonFailure(stdout, flags["json"], usageErr("verify-batch takes exactly one requests file"))
	}
	res, err := verifyBatch(pos[0], opts["janus-root"], flags["fresh"], flags["unsafe-no-sandbox"], flags["allow-path-deps"], flags["json"], flags["asl"], stdout, stderr)
	if err != nil {
		return jsonFailure(stdout, flags["json"], err)
	}
	b, _ := json.MarshalIndent(res, "", "  ")
	if opts["results"] != "" {
		if err := os.WriteFile(opts["results"], append(b, '\n'), 0o644); err != nil {
			return &diag{Msg: fmt.Sprintf("Cannot write %s: %v", opts["results"], err), Stage: "writing report"}
		}
	}
	if flags["json"] {
		fmt.Fprintf(stdout, "%s\n", b)
	} else {
		fmt.Fprintf(stdout, "Summary: %d request(s): %d verified, %d failed; %d consumer snapshot(s), %d workspace(s).\n",
			len(res.Results), res.Passed, res.Failed, res.Snapshots, len(res.Groups))
	}
	if res.Failed > 0 {
		return &diag{Invalid: true, Msg: fmt.Sprintf("%d of %d request(s) failed.", res.Failed, len(res.Results)), Stage: "verify-batch",
			Next: "See the FAIL lines above (or the failure field of each result) and rerun."}
	}
	if res.ASLFailed > 0 {
		return &diag{Invalid: true, Msg: fmt.Sprintf("%d of %d verified request(s) have no ASL corollary (their theorems are verified).", res.ASLFailed, res.Passed),
			Stage: "ASL", Next: "See the ASL lines above (or the aslFailure field of each result)."}
	}
	return nil
}

func verifyBatch(manifestPath, janusRoot string, fresh, unsafe, allowPathDeps, quiet, asl bool, stdout, stderr io.Writer) (*batchResults, error) {
	if err := memGuardConfigErr(); err != nil {
		return nil, err
	}
	logMemGuard(stderr)
	raw, err := os.ReadFile(manifestPath)
	if err != nil {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot read %s: %v", displayPath(manifestPath), err), Stage: "batch requests",
			Next: "Pass a requests file (see docs/CONSUMERS.md#batch-verification)."}
	}
	var man batchManifest
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&man); err != nil {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("Cannot parse %s: %v", displayPath(manifestPath), err), Stage: "batch requests",
			Next: `Use {"schema": 1, "proofRoot": "...", "requests": [{"outdir": "...", "proof": "...", "theorem": "..."}]}.`}
	}
	if man.Schema != 1 || len(man.Requests) == 0 {
		return nil, &diag{Invalid: true, Msg: fmt.Sprintf("%s must have \"schema\": 1 and at least one request.", displayPath(manifestPath)), Stage: "batch requests"}
	}
	base := filepath.Dir(manifestPath)
	resolve := func(p string) string {
		if p == "" || filepath.IsAbs(p) {
			return p
		}
		return filepath.Join(base, filepath.FromSlash(p))
	}
	out := stdout
	if quiet {
		out = stderr
	}

	res := &batchResults{Schema: 1, Groups: []batchGroup{}}
	reqs := make([]*consumerRequest, len(man.Requests))
	roots := make([]string, len(man.Requests))
	seenOut := map[string]int{}
	for i, br := range man.Requests {
		root := br.ProofRoot
		if root == "" {
			root = man.ProofRoot
		}
		roots[i] = resolve(root)
		reqs[i] = &consumerRequest{Outdir: resolve(br.Outdir), Proof: resolve(br.Proof), Theorem: br.Theorem, Binary: resolve(br.Binary)}
		res.Results = append(res.Results, batchResult{Index: i, Outdir: br.Outdir, Proof: br.Proof, Theorem: br.Theorem, ProofRoot: root, Group: -1})
		if br.Outdir == "" {
			reqs[i].Err = &diag{Invalid: true, Msg: "The request has no outdir.", Stage: "batch requests"}
			continue
		}
		abs, _ := filepath.Abs(reqs[i].Outdir)
		if j, dup := seenOut[abs]; dup {
			reqs[i].Err = &diag{Invalid: true, Msg: fmt.Sprintf("Requests %d and %d write the same output %s.", j, i, br.Outdir), Stage: "batch requests",
				Next: "Give every request its own outdir (each gets an independent verified.json)."}
			continue
		}
		seenOut[abs] = i
		// Every request starts by withdrawing its previous report.
		_ = os.Remove(filepath.Join(reqs[i].Outdir, "verified.json"))
	}

	finish := func(i int) {
		r := reqs[i]
		br := &res.Results[i]
		if r.Err == nil && r.Report != nil {
			if err := writeReport(filepath.Join(r.Outdir, "verified.json"), r.Report); err != nil {
				r.Err = err
			}
		}
		if r.Err != nil {
			f := toFailureJSON(r.Err)
			br.Status, br.Failure = "failed", &f
			res.Failed++
			fmt.Fprintf(out, "FAIL %s %s\n  %s\n  Stage: %s\n", displayPath(r.Outdir), termSafe(theoremOrDefault(br.Theorem)), strings.ReplaceAll(termSafe(f.Message), "\n", "\n  "), f.Stage)
			if f.Next != "" {
				fmt.Fprintf(out, "  Next: %s\n", f.Next)
			}
			return
		}
		br.Status = "verified"
		br.Module = r.Report.Module
		br.Report = filepath.ToSlash(filepath.Join(br.Outdir, "verified.json"))
		res.Passed++
		fmt.Fprintf(out, "PASS %s %s (module %s)\n", displayPath(r.Outdir), termSafe(r.Report.Theorem), termSafe(r.Report.Module))
		if a := r.Report.ASL; a != nil {
			br.ASL = a.Status
			if a.Status == "verified" {
				fmt.Fprintf(out, "  ASL: %s verified\n", termSafe(a.Theorem))
			} else {
				res.ASLFailed++
				br.ASLFailure = a.Failure
				fmt.Fprintf(out, "  ASL: NOT derived: %s\n  Stage: %s\n", strings.ReplaceAll(termSafe(a.Failure.Message), "\n", "\n  "), a.Failure.Stage)
			}
		}
	}

	fw, err := loadFramework(janusRoot)
	if err != nil {
		return nil, err
	}
	lake, err := findLake()
	if err != nil {
		return nil, err
	}
	sb, err := detectSandbox(unsafe)
	if err != nil {
		return nil, err
	}
	fwLease, err := fw.frameworkBase(lake, stderr)
	if err != nil {
		return nil, err
	}
	// Only the toolchain is read here; each workspace (and single-file verification) takes the
	// framework build again for as long as it uses it.
	tc, err := findToolchain(lake, fwLease.dir)
	fwLease.release()
	if err != nil {
		return nil, err
	}
	var aslB *aslBuild
	if asl {
		if aslB, err = buildASLFor(fw, "", lake, stderr); err != nil {
			return nil, err
		}
		defer aslB.release()
	}

	// Requests without a proof root are single-file verifications, one by one.
	byRoot := map[string][]int{}
	var rootOrder []string
	for i, r := range reqs {
		if r.Err != nil {
			continue
		}
		if roots[i] == "" {
			opts := map[string]string{"proof": r.Proof, "theorem": r.Theorem, "binary": r.Binary, "janus-root": janusRoot}
			if fresh {
				opts["fresh"] = "true"
			}
			if unsafe {
				opts["unsafe-no-sandbox"] = "true"
			}
			if asl {
				opts["asl"] = "true"
			}
			mark := memMark()
			r.Report, r.Err = verify(r.Outdir, opts, stderr)
			r.Report, r.Err = memOutcome(mark, r.Report, r.Err)
			continue
		}
		abs, _ := filepath.Abs(roots[i])
		if _, ok := byRoot[abs]; !ok {
			rootOrder = append(rootOrder, abs)
		}
		byRoot[abs] = append(byRoot[abs], i)
	}

	for _, root := range rootOrder {
		idx := byRoot[root]
		var outdirs []string
		for _, i := range idx {
			outdirs = append(outdirs, reqs[i].Outdir)
		}
		// Selection and extraction integrity, per request.
		var live []int
		for _, i := range idx {
			if err := reqs[i].prepare(); err != nil {
				reqs[i].Err = err
				finish(i)
				continue
			}
			live = append(live, i)
		}
		if len(live) == 0 {
			continue
		}
		// One snapshot of the package for all its requests.
		pkg, err := loadConsumer(root, fw, outdirs, loadOpts{AllowPathDeps: allowPathDeps, SB: sb})
		if err != nil {
			for _, i := range live {
				reqs[i].Err = err
				finish(i)
			}
			continue
		}
		res.Snapshots++
		groups := map[string][]int{}
		var order []string
		for _, i := range live {
			r := reqs[i]
			if r.rel, err = pkg.proofRel(r.Proof); err != nil {
				r.Err = err
				finish(i)
				continue
			}
			if !bytes.Equal(pkg.Files[r.rel], r.proofSrc) {
				r.Err = &diag{Invalid: true, Msg: "The proof changed while the package was read.", Stage: "stale input", Next: "Rerun janus verify-batch."}
				finish(i)
				continue
			}
			k := sha256Hex(r.cr.Lean)
			if _, ok := groups[k]; !ok {
				order = append(order, k)
			}
			groups[k] = append(groups[k], i)
		}
		// One workspace per distinct extraction; the first one's build seeds the others.
		for _, k := range order {
			gi := groups[k]
			var greqs []*consumerRequest
			for _, i := range gi {
				greqs = append(greqs, reqs[i])
			}
			mark := memMark()
			ws, err := openWorkspace(fw, pkg, greqs[0].cr.Lean, fresh, lake, sb, tc, stderr)
			if err != nil {
				for _, i := range gi {
					reqs[i].Err = err
					finish(i)
				}
				continue
			}
			ws.asl = aslB
			verifyGroup(fw, pkg, ws, greqs)
			for _, r := range greqs {
				r.Report, r.Err = memOutcomeSkip(mark, ws.memOwn, r.Report, r.Err)
			}
			g := batchGroup{ProofRoot: root, SnapshotSha256: pkg.Sha256, ExtractedSha256: k, Workspace: ws.Dir, Requests: gi, Rebuilt: []string{}}
			if ws.temp {
				g.Workspace = "(temporary, --fresh)"
			}
			for _, r := range greqs {
				if r.Report != nil {
					g.Rebuilt = r.Report.Consumer.Rebuilt
					break
				}
			}
			ws.close()
			res.Groups = append(res.Groups, g)
			for _, i := range gi {
				res.Results[i].Group = len(res.Groups) - 1
				finish(i)
			}
		}
	}
	// Single-file and early failures that have not been printed yet.
	printed := map[int]bool{}
	for _, g := range res.Groups {
		for _, i := range g.Requests {
			printed[i] = true
		}
	}
	for i, br := range res.Results {
		if br.Status == "" && !printed[i] {
			finish(i)
		}
	}
	sort.SliceStable(res.Results, func(a, b int) bool { return res.Results[a].Index < res.Results[b].Index })
	return res, nil
}

func theoremOrDefault(t string) string {
	if t == "" {
		return defaultTheorem
	}
	return t
}

package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"testing"
)

// INCR2: why the incremental gate skipped (almost) nothing across commits, and the tests that keep it from happening
// again without weakening it. See docs/TESTING.md "Incremental gate" (the miss analysis and the rules).

// gateRunEnv is what scripts/gate.sh, scripts/lib/incr.sh and scripts/verify-all-examples.sh export to every item of
// one gate run, with the values of that run: they are run-specific (a timestamped output directory, the stamp of the
// tree, the load-derived sizing). Two gate runs of identical item inputs differ in all of them.
func gateRunEnv(n int) []string {
	return []string{
		fmt.Sprintf("JANUS_GATE_TREE0=stamp-of-run-%d", n),
		fmt.Sprintf("JANUS_LAKEGUARD_PIN=/repo/artifacts/gate/2026103%dT101010Z/.pinned", n),
		fmt.Sprintf("JANUS_LAKEGUARD_ROOT=/worktree-%d", n),
		fmt.Sprintf("JANUS_GATE_AUTO_WHY=load %d.5, 40 GiB free: -j %d", n, 2+n),
		fmt.Sprintf("JANUS_GATE_ROUNDS_LANES=%d", 2+n),
		fmt.Sprintf("JANUS_ROUNDS_LANES=%d", 2+n),
		fmt.Sprintf("JANUS_GATE_AUTO_BUDGET=budget %d GiB", 100+n),
		fmt.Sprintf("JANUS_VERIFY_MEM_BUDGET_GIB=%d", 90+n),
		fmt.Sprintf("JANUS_JOBS=%d", 2+n),
		fmt.Sprintf("JANUS_LANES=%d", 3+n),
		fmt.Sprintf("JANUS_GATE_PG=/repo/artifacts/gate/run%d", n),
		fmt.Sprintf("JANUS_POOL_DIR=/repo/artifacts/gate/run%d/verify", n),
		fmt.Sprintf("JANUS_GATE_T0=17917000%d.5", n),
		fmt.Sprintf("JANUS_MEMGUARD_CGROUP=janus-%d", n),
		"JANUS_GATE_PREBUILT=1", "JANUS_EXAMPLES_PREBUILT=1", "JANUS_INCR_RECORD=1", "JANUS_GATE_INCREMENTAL=1",
		// constants of the gate: they stay in the key
		"LEAN_NUM_THREADS=4", "JANUS_REAL_LAKE=/usr/local/bin/lake",
	}
}

// Two gate runs of the same inputs share a key: a PASS of the first is a skip in the second. This is the regression test of
// the bug of ad264a2 (every incremental gate run missed every item).
func TestIncr2GateRunsShareKeys(t *testing.T) {
	x := newIncrFx(t)
	x.ctx.environ = append(x.ctx.environ, gateRunEnv(1)...)
	x.pass()
	x.wantSkip()
	x.ctx.environ = append(x.ctx.environ[:4:4], gateRunEnv(2)...) // the fixture's own four variables, then run 2's
	x.wantSkip()
}

// Each bookkeeping variable alone, changed, set or unset: still a skip. And the same set of variables under the OLD skip list
// would have been a miss (the mutation check: the test fails if one of them is keyed again).
func TestIncr2EachBookkeepingVariableIsNotKeyed(t *testing.T) {
	for _, kv := range gateRunEnv(1) {
		name := kv[:strings.IndexByte(kv, '=')]
		if name == "LEAN_NUM_THREADS" || name == "JANUS_REAL_LAKE" {
			continue
		}
		t.Run(name, func(t *testing.T) {
			if incrEnvRelevant(name) {
				t.Fatalf("%s is keyed", name)
			}
			x := newIncrFx(t)
			x.ctx.environ = append(x.ctx.environ, kv)
			x.pass()
			x.wantSkip()
			x.ctx.environ[len(x.ctx.environ)-1] = name + "=another value"
			x.wantSkip()
			x.ctx.environ = x.ctx.environ[:len(x.ctx.environ)-1] // unset
			x.wantSkip()
		})
	}
}

// The constants of the gate and every variable that CAN change what is checked stay in the key.
func TestIncr2RelevantVariablesStayKeyed(t *testing.T) {
	for _, kv := range []string{"LEAN_NUM_THREADS=2", "JANUS_REAL_LAKE=/other/lake", "JANUS_ITEM_TIMEOUT=60", "JANUS_MEM_MAX=1G",
		"JANUS_ROOT=/elsewhere", "JANUS_VERIFIER_ID=exe", "JANUS_GATE_TEST_LANE=true", "LEAN_PATH=/x", "JANUS_GATE_TREE01=1"} {
		t.Run(kv, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			x.ctx.environ = append(x.ctx.environ, kv)
			x.wantRun()
		})
	}
}

// Key collision attempts through the skip list: a skipped name must match exactly, a value must not smuggle a second
// variable past it, and a keyed variable's value must not be able to impersonate "nothing".
func TestIncr2SkipListCollisionAttempts(t *testing.T) {
	t.Run("a lookalike name is keyed", func(t *testing.T) {
		for _, n := range []string{"JANUS_GATE_TREE0_", "JANUS_GATE_TREE", "JANUS_GATE_TREE00", "JANUS_VERIFY_MEM_BUDGET", "JANUS_LAKEGUARD_PINS", "JANUS_LAKEGUARD"} {
			x := newIncrFx(t)
			x.pass()
			x.ctx.environ = append(x.ctx.environ, n+"=1")
			x.wantRun()
		}
	})
	t.Run("a skipped variable's value cannot hide a keyed variable", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		// environ entries are split at the first '=': the whole line belongs to the skipped name, and the process sees one variable
		x.ctx.environ = append(x.ctx.environ, "JANUS_GATE_TREE0=x\nJANUS_ITEM_TIMEOUT=1")
		x.wantSkip() // (a real process environment cannot hold a keyed variable inside another's value)
		if got := incrEnvLines(x.ctx.environ); len(got) != 1 || got[0] != "JANUS_ITEM_TIMEOUT=2700" {
			t.Fatalf("the keyed environment is %q", got)
		}
	})
	t.Run("a keyed variable's value that looks like a skipped one is part of its line", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		x.ctx.environ = append(x.ctx.environ, "JANUS_FOO=1\nJANUS_GATE_TREE0=2")
		x.wantRun()
	})
	t.Run("two variables never equal one with a newline", func(t *testing.T) {
		a := newIncrFx(t)
		a.ctx.environ = append(a.ctx.environ, "JANUS_FOO=1", "JANUS_BAR=2")
		b := newIncrFx(t)
		b.fwFiles = a.fwFiles
		b.ctx.environ = append(b.ctx.environ, "JANUS_FOO=1\nJANUS_BAR=2")
		if hashLines(incrEnvLines(a.ctx.environ)) == hashLines(incrEnvLines(b.ctx.environ)) {
			t.Fatal("collision between two variables and one variable with a newline in its value")
		}
	})
}

// A tampered record stays a miss when the run that reads it has other bookkeeping values than the run that wrote it.
func TestIncr2TamperedRecordIsAMissAcrossGateRuns(t *testing.T) {
	x := newIncrFx(t)
	x.ctx.environ = append(x.ctx.environ, gateRunEnv(1)...)
	x.pass()
	x.ctx.environ = append(x.ctx.environ[:4:4], gateRunEnv(2)...)
	x.wantSkip()
	p := incrPath(x.key())
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(p, []byte(strings.Replace(string(b), `"mac":"`, `"mac":"0`, 1)), 0o600); err != nil {
		t.Fatal(err)
	}
	x.wantRun()
}

// A second item next to the first: the fixture's framework and toolchain are shared, its proof and extraction are its own.
func (x *incrFx) addItemQ() *incrSpec {
	wr(x.t, filepath.Join(x.root, "proofs", "Q.lean"), "import Janus\nimport Extracted\n\ntheorem q : True := trivial\n")
	wr(x.t, filepath.Join(x.root, "artq", "Extracted.lean"), "import Janus\nnamespace Extracted\nend Extracted\n")
	sha, _ := (&incrCtx{root: x.root, memo: map[string]string{}}).fileSha("bin/ex")
	wr(x.t, filepath.Join(x.root, "artq", "identity.json"), fmt.Sprintf(`{"binary":"../bin/ex","binarySha256":%q,"symbol":"g"}`, sha))
	return &incrSpec{ID: "arm64:Q", Kind: "arm64", FW: []string{"embedded"}, Proofs: []string{"proofs/Q.lean"}, Arts: []string{"artq"},
		Files: []string{"bin/ex"}, Pins: []string{"pins/stubpins.go"}, Scripts: []string{"scripts/run.sh"}, Args: []string{"Proof.correctness"}}
}

func (x *incrFx) with(sp *incrSpec, f func()) {
	save := x.sp
	x.sp = sp
	defer func() { x.sp = save }()
	f()
}

func TestIncr2LeafChangeInvalidatesOnlyThatItem(t *testing.T) {
	for _, tc := range []struct {
		name  string
		edit  func(x *incrFx)
		wantP bool // P must still skip
		wantQ bool
	}{
		{"the leaf's own proof file", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "proofs", "Q.lean"), "import Janus\nimport Extracted\n\ntheorem q : True := by trivial\n")
		}, true, false},
		{"the leaf's own extraction", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "artq", "Extracted.lean"), "import Janus\nnamespace Extracted\ndef z := 1\nend Extracted\n")
		}, true, false},
		{"another item's proof file", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "proofs", "P.lean"), "import Janus\nimport Extracted\n\ntheorem x : True := by trivial\n")
		}, false, true},
		{"a file no item names (an example's other source)", func(x *incrFx) { wr(t, filepath.Join(x.root, "examples", "other", "x.go"), "package x\n") }, true, true},
		{"a doc", func(x *incrFx) { wr(t, filepath.Join(x.root, "docs", "NOTE.md"), "note\n") }, true, true},
		{"a framework module neither imports", func(x *incrFx) { x.fwFiles["Janus/Unused.lean"] = []byte("import Janus.C\n-- edited\n") }, true, true},
		{"a script for another kind", func(x *incrFx) { wr(t, filepath.Join(x.root, "scripts", "other-kind.sh"), "echo other\n") }, true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			x := newIncrFx(t)
			q := x.addItemQ()
			x.pass()
			x.with(q, x.pass)
			x.wantSkip()
			x.with(q, x.wantSkip)
			tc.edit(x)
			check := func(sp *incrSpec, want bool, who string) {
				x.with(sp, func() {
					got := strings.HasPrefix(x.run("check", nil), "SKIP\t")
					if got != want {
						t.Errorf("%s skipped=%v, want %v", who, got, want)
					}
				})
			}
			check(x.sp, tc.wantP, "P")
			check(q, tc.wantQ, "Q")
		})
	}
}

// A change to a module that is shared (imported by the umbrella the auditor loads, or by the item's proof) invalidates every
// dependent item: the expected, correct case. Nothing may skip.
func TestIncr2SharedModuleChangeInvalidatesEveryDependent(t *testing.T) {
	for _, mod := range []string{"Janus/C.lean", "Janus/D.lean", "Janus/E.lean", "Janus/A.lean", "Janus/B.lean", "Janus.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "Janus/Tools/Audit.lean"} {
		t.Run(mod, func(t *testing.T) {
			x := newIncrFx(t)
			q := x.addItemQ()
			x.pass()
			x.with(q, x.pass)
			x.fwFiles[mod] = append(append([]byte{}, x.fwFiles[mod]...), []byte("\n-- shared edit\n")...)
			x.wantRun()
			x.with(q, x.wantRun)
		})
	}
	t.Run("the compiled data of a shared module, source unchanged", func(t *testing.T) {
		x := newIncrFx(t)
		q := x.addItemQ()
		x.pass()
		x.with(q, x.pass)
		wr(t, filepath.Join(x.build, ".lake", "build", "lib", "lean", "Janus", "C.olean"), "a different olean")
		x.wantRun()
		x.with(q, x.wantRun)
	})
	t.Run("the verifier", func(t *testing.T) {
		x := newIncrFx(t)
		q := x.addItemQ()
		x.pass()
		x.with(q, x.pass)
		x.verifier = "src:v2"
		x.wantRun()
		x.with(q, x.wantRun)
	})
}

func TestIncr2ScriptAndToolchainChanges(t *testing.T) {
	t.Run("the script an item names", func(t *testing.T) {
		x := newIncrFx(t)
		q := x.addItemQ()
		other := *q
		other.ID, other.Scripts = "arm64:R", []string{"scripts/other.sh"}
		wr(t, filepath.Join(x.root, "scripts", "other.sh"), "echo other\n")
		x.pass()
		x.with(&other, x.pass)
		wr(t, filepath.Join(x.root, "scripts", "run.sh"), "#!/bin/sh\necho changed\n")
		x.wantRun()
		x.with(&other, x.wantSkip) // the script of another kind is not this item's input
	})
	t.Run("the toolchain version, the lean binary, the checker", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		x.tcver = "Lean (version 4.100)"
		x.wantRun()
		x.tcver = "Lean (version 4.99)"
		x.wantSkip()
		tc, _ := x.ctx.tchain("")
		for _, f := range []string{tc.lean, tc.leanchecker} {
			old, _ := os.ReadFile(f)
			os.WriteFile(f, append(old, '!'), 0o755)
			x.wantRun()
			os.WriteFile(f, old, 0o755) // (its mtime is part of the toolchain's identity: restored content is not the same key)
		}
	})
}

// ---- the scripts: every export of the gate is classified

// exportRe also finds an `export` inside a quoted string (gate.sh's laneenv echoes "export JANUS_LANE_TREE=..." into a lane's code)
var exportRe = regexp.MustCompile(`\bexport\s+([^\n;&|]*)`)
var nameRe = regexp.MustCompile(`^([A-Za-z_][A-Za-z0-9_]*)(=|$)`)

var (
	stmtSplitRe    = regexp.MustCompile(`;|&&|\|\||\||&`)
	allexportOnRe  = regexp.MustCompile(`^set\s+(?:.*\s)?(?:-[A-Za-z]*a[A-Za-z]*|-o\s+allexport)(?:\s|$)`)
	allexportOffRe = regexp.MustCompile(`^set\s+(?:.*\s)?(?:\+[A-Za-z]*a[A-Za-z]*|\+o\s+allexport)(?:\s|$)`)
	leadKeyword    = map[string]bool{"then": true, "do": true, "else": true, "{": true, "(": true, "if": true, "while": true, "until": true, "!": true}
)

// scanExports returns the variable names a shell script exports to its children, statically. The forms: `export NAME[=v] ...`,
// `declare|typeset|local ... -x ... NAME[=v]` (any flag cluster containing x: -x, -gx, -xg, -rx, ...), and every plain assignment
// `NAME=v` made while allexport is on (`set -a` / `set -o allexport` until `set +a` / `set +o allexport`, also in one line:
// `set -a; JANUS_X=5; set +a`). Comment lines are skipped; a statement is a piece of a line cut at ; && || | &.
func scanExports(src string) []string {
	return dedupe(scanExportsRaw(src, nil))
}

func dedupe(in []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, n := range in {
		if !seen[n] {
			seen[n] = true
			out = append(out, n)
		}
	}
	return out
}

func scanExportsRaw(src string, out []string) []string {
	allexport := false
	for _, line := range strings.Split(src, "\n") {
		if strings.HasPrefix(strings.TrimSpace(line), "#") {
			continue
		}
		for _, m := range exportRe.FindAllStringSubmatch(line, -1) {
			for _, a := range strings.Fields(m[1]) {
				if nm := nameRe.FindStringSubmatch(a); nm != nil {
					out = append(out, nm[1])
				}
			}
		}
		for _, st := range stmtSplitRe.Split(line, -1) {
			w := strings.Fields(st)
			for len(w) > 0 && (leadKeyword[w[0]] || strings.HasSuffix(w[0], "()")) {
				w = w[1:]
			}
			if len(w) == 0 {
				continue
			}
			joined := strings.Join(w, " ")
			if allexportOnRe.MatchString(joined) {
				allexport = true
				continue
			}
			if allexportOffRe.MatchString(joined) {
				allexport = false
				continue
			}
			// leading assignments (`A=1 B=2 cmd ...`), then the command word
			i := 0
			for i < len(w) {
				nm := nameRe.FindStringSubmatch(w[i])
				if nm == nil || nm[2] != "=" {
					break
				}
				if allexport {
					out = append(out, nm[1])
				}
				i++
			}
			if i >= len(w) {
				continue
			}
			switch w[i] {
			case "export":
				for _, a := range w[i+1:] {
					if nm := nameRe.FindStringSubmatch(a); nm != nil {
						out = append(out, nm[1])
					}
				}
			case "declare", "typeset", "local":
				x := false
				var names []string
				for _, a := range w[i+1:] {
					if strings.HasPrefix(a, "-") && !strings.HasPrefix(a, "--") {
						x = x || strings.Contains(a, "x")
					} else if nm := nameRe.FindStringSubmatch(a); nm != nil {
						names = append(names, nm[1])
					}
				}
				if x {
					out = append(out, names...)
				}
			}
		}
	}
	return out
}

// gateScriptPatterns are the scripts whose exports reach the gate's items and lanes (test scripts excluded).
var gateScriptPatterns = []string{"scripts/gate.sh", "scripts/verify-*.sh", "scripts/build-examples*.sh", "scripts/example-*.sh", "scripts/lib/*.sh",
	"audit/*.sh", "audit/*/*.sh", "audit/*/*/*.sh", "audit/*/*/*/*.sh"}

func gateScriptFiles(root string) []string {
	var files []string
	for _, pat := range gateScriptPatterns {
		m, _ := filepath.Glob(filepath.Join(root, pat))
		for _, f := range m {
			if !strings.Contains(filepath.Base(f), "test-") {
				files = append(files, f)
			}
		}
	}
	return files
}

// gateExportsIn are the variable names the gate's scripts under root export, with the scripts that export them.
func gateExportsIn(t *testing.T, root string) map[string][]string {
	t.Helper()
	out := map[string][]string{}
	for _, f := range gateScriptFiles(root) {
		b, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		rel, _ := filepath.Rel(root, f)
		for _, n := range scanExports(string(b)) {
			out[n] = append(out[n], rel)
		}
	}
	return out
}

func gateExports(t *testing.T) map[string][]string { t.Helper(); return gateExportsIn(t, repoRoot) }

// keyedGateExports: the variables the gate's scripts export that ARE in the item and lane keys, each with the reason that is
// sound. A NEW export that is relevant to the key fails TestIncr2EveryGateExportIsClassified: either it is bookkeeping
// (add it to incrEnvSkip with its reason, and to gateRunEnv above) or it can change what is checked (add it here).
func keyedGateExports() map[string]string {
	b, err := os.ReadFile(filepath.Join(repoRoot, "scripts", "lib", "incr-keyed-exports.txt"))
	if err != nil {
		panic(err)
	}
	m := map[string]string{}
	for _, l := range strings.Split(string(b), "\n") {
		if l == "" || strings.HasPrefix(l, "#") {
			continue
		}
		n, why, ok := strings.Cut(l, "\t")
		if !ok || n == "" || why == "" {
			panic("scripts/lib/incr-keyed-exports.txt: bad line " + l)
		}
		m[n] = why
	}
	return m
}

// unclassifiedExports lists the exported names that are in the key and neither skipped nor justified as keyed.
func unclassifiedExports(ex map[string][]string) []string {
	var bad []string
	for n := range ex {
		if (incrEnvRelevant(n) || incrEnvSkip[n]) && !incrEnvSkip[n] {
			if _, ok := keyedGateExports()[n]; !ok {
				bad = append(bad, n)
			}
		}
	}
	sort.Strings(bad)
	return bad
}

// The justification of the audit entries above: no audit script computes an item or lane key, so a run-specific variable they
// export can never be part of one.
func TestIncr2AuditScriptsComputeNoKeys(t *testing.T) {
	n := 0
	for _, f := range gateScriptFiles(repoRoot) {
		rel, _ := filepath.Rel(repoRoot, f)
		if !strings.HasPrefix(rel, "audit/") {
			continue
		}
		n++
		b, _ := os.ReadFile(f)
		for _, w := range []string{"incr_begin", "incr_lane", "janus incr", "lib/incr.sh"} {
			if strings.Contains(string(b), w) {
				t.Errorf("%s uses %q: its exports are no longer covered by the audit entries of keyedGateExports", rel, w)
			}
		}
	}
	if n < 10 {
		t.Fatalf("only %d audit scripts scanned", n)
	}
}

func TestIncr2EveryGateExportIsClassified(t *testing.T) {
	ex := gateExports(t)
	if len(ex) < 20 {
		t.Fatalf("found only %d exported names: the scan is broken", len(ex))
	}
	for _, n := range unclassifiedExports(ex) {
		t.Errorf("%s is exported by %v, is part of every item's and lane's key and is not classified: if its value differs from "+
			"one gate run to the next, no incremental gate run can ever skip anything (the bug of ad264a2). Bookkeeping: add it to "+
			"incrEnvSkip with its reason; a constant or something that changes what is checked: add it to scripts/lib/incr-keyed-exports.txt.", n, ex[n])
	}
	// the other direction: a classification of a name no script exports any more is stale
	for n := range keyedGateExports() {
		if _, ok := ex[n]; !ok && n != "JANUS_GO_TOOLCHAIN" && n != "JANUS_COLD" {
			t.Errorf("scripts/lib/incr-keyed-exports.txt lists %s, which no gate script exports (stale)", n)
		}
	}
}

// copyGateScripts copies every script the scan reads into a temp root (the mutation tests add a fake script there).
func copyGateScripts(t *testing.T) string {
	t.Helper()
	dst := t.TempDir()
	for _, f := range gateScriptFiles(repoRoot) {
		rel, _ := filepath.Rel(repoRoot, f)
		b, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		wr(t, filepath.Join(dst, rel), string(b))
	}
	return dst
}

// Mutation test of the scan: a fake script exporting a run-specific JANUS_ variable in each shell form, in every directory the
// scan covers, must be found (as an export) and must fail the classification; the unmutated copy is clean.
func TestIncr2ExportScanCatchesEveryForm(t *testing.T) {
	base := copyGateScripts(t)
	if bad := unclassifiedExports(gateExportsIn(t, base)); len(bad) != 0 {
		t.Fatalf("the copy is not clean: %v", bad)
	}
	forms := map[string]string{
		"export":         "export JANUS_FAKE_RUN=$RANDOM\n",
		"export-list":    "export A_OK JANUS_FAKE_RUN\n",
		"declare-x":      "declare -x JANUS_FAKE_RUN=1\n",
		"declare-gx":     "declare -gx JANUS_FAKE_RUN=1\n",
		"declare-xg":     "declare -xg JANUS_FAKE_RUN=1\n",
		"declare-r-x":    "declare -r -x JANUS_FAKE_RUN=1\n",
		"typeset-x":      "typeset -x JANUS_FAKE_RUN=1\n",
		"local-x":        "f() { local -x JANUS_FAKE_RUN=1; }\n",
		"set-a-block":    "set -a\nJANUS_FAKE_RUN=5\nset +a\n",
		"set-a-oneline":  "set -a; JANUS_FAKE_RUN=5; set +a\n",
		"set-o-allexp":   "set -o allexport\nJANUS_FAKE_RUN=5\nset +o allexport\n",
		"set-eua":        "set -eua\nJANUS_FAKE_RUN=5\n",
		"after-then":     "if true; then export JANUS_FAKE_RUN=1; fi\n",
		"after-or":       "[ -n \"$x\" ] || export JANUS_FAKE_RUN=1\n",
		"prefixed":       "FOO=1 export JANUS_FAKE_RUN=1\n",
		"allexport-pref": "set -a\nFOO=1 JANUS_FAKE_RUN=5 true\n",
	}
	dirs := []string{"scripts/lib", "scripts", "audit", "audit/round99", "audit/rt-x/deep", "audit/a/b/c"}
	for name, body := range forms {
		for _, d := range dirs {
			t.Run(name+"@"+d, func(t *testing.T) {
				root := copyGateScripts(t)
				name := "zz-fake.sh"
				if d == "scripts" {
					name = "verify-fake.sh"
				}
				wr(t, filepath.Join(root, d, name), "#!/usr/bin/env bash\n"+body)
				ex := gateExportsIn(t, root)
				if len(ex["JANUS_FAKE_RUN"]) != 1 {
					t.Fatalf("the form is not found: %v", ex["JANUS_FAKE_RUN"])
				}
				bad := unclassifiedExports(ex)
				if len(bad) != 1 || bad[0] != "JANUS_FAKE_RUN" {
					t.Fatalf("classification result %v", bad)
				}
			})
		}
	}
	// what is NOT an export stays unexported (no false alarms from comments, a plain assignment, `set +a` first, declare without x)
	for name, body := range map[string]string{
		"comment":       "# export JANUS_FAKE_RUN=1\n  # declare -x JANUS_FAKE_RUN=1\n",
		"assignment":    "JANUS_FAKE_RUN=1\n",
		"declare-plain": "declare -r JANUS_FAKE_RUN=1\ndeclare -a JANUS_FAKE_RUN\n",
		"after-off":     "set -a\nset +a\nJANUS_FAKE_RUN=1\n",
		"set-eu":        "set -euo pipefail\nJANUS_FAKE_RUN=1\n",
		"env-prefix":    "JANUS_FAKE_RUN=1 ./run.sh\n",
	} {
		t.Run("negative-"+name, func(t *testing.T) {
			if got := scanExports(body); len(got) != 0 {
				t.Fatalf("false alarm %v", got)
			}
		})
	}
}

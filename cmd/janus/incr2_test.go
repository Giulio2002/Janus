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

var exportRe = regexp.MustCompile(`(?m)\bexport\s+([^\n;&|]*)`)
var nameRe = regexp.MustCompile(`^([A-Za-z_][A-Za-z0-9_]*)(=|$)`)

// gateExports are the variable names the gate's scripts export (statically: `export NAME=...`, `export NAME NAME2`).
func gateExports(t *testing.T) map[string][]string {
	t.Helper()
	var files []string
	for _, pat := range []string{"scripts/gate.sh", "scripts/verify-*.sh", "scripts/build-examples*.sh", "scripts/example-*.sh", "scripts/lib/*.sh"} {
		m, _ := filepath.Glob(filepath.Join(repoRoot, pat))
		files = append(files, m...)
	}
	out := map[string][]string{}
	for _, f := range files {
		if strings.Contains(filepath.Base(f), "test-") {
			continue
		}
		b, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		for _, line := range strings.Split(string(b), "\n") {
			if strings.HasPrefix(strings.TrimSpace(line), "#") {
				continue
			}
			for _, m := range exportRe.FindAllStringSubmatch(line, -1) {
				for _, w := range strings.Fields(m[1]) {
					if nm := nameRe.FindStringSubmatch(w); nm != nil {
						rel, _ := filepath.Rel(repoRoot, f)
						out[nm[1]] = append(out[nm[1]], rel)
					}
				}
			}
		}
	}
	return out
}

// keyedGateExports: the variables the gate's scripts export that ARE in the item and lane keys, each with the reason that is
// sound. A NEW export that is relevant to the key fails TestIncr2EveryGateExportIsClassified: either it is bookkeeping
// (add it to incrEnvSkip with its reason, and to gateRunEnv above) or it can change what is checked (add it here).
var keyedGateExports = map[string]string{
	"LEAN_NUM_THREADS":       "a constant of the gate (4, capped); a different thread count is a different run",
	"JANUS_REAL_LAKE":        "the lake the gate found on PATH: a constant of the host, and the toolchain is keyed by its bytes anyway",
	"JANUS_MEM_MAX":          "the memory limit of a lane (set inside the lane's code, after its key is computed; a user's value is keyed)",
	"JANUS_LANE_TREE":        "set inside a lane's code after its key is computed",
	"JANUS_LANE_LAKE_LOCK":   "set inside a lane's code after its key is computed",
	"JANUS_CACHE_KEY_DIR":    "cold gate only (--cold is not combinable with --incremental)",
	"JANUS_COLD_XDG":         "cold gate only",
	"JANUS_COLD_PIN_LOG":     "cold gate only",
	"JANUS_COLD_PIN_CHECKED": "cold gate only",
	"JANUS_COLD_DONE":        "cold gate only",
	"JANUS_COLD":             "cold gate only",
	"JANUS_MODEL_PIN":        "cold gate only",
	"JANUS_MODEL_PIN_STALE":  "cold gate only",
	"ASL_CACHE":              "selects the ISA model cache directory: affects the ASL lanes, keyed on purpose",
	"RT_ASL_KEEP_DIR":        "not a key variable (no matching prefix)",
	"CGO_ENABLED":            "keyed on purpose",
	"CGO_CFLAGS":             "keyed on purpose",
	"GOTOOLCHAIN":            "set by the example build scripts, which run before the keys are computed; keyed on purpose",
	"JANUS_GO_TOOLCHAIN":     "keyed on purpose",
}

func TestIncr2EveryGateExportIsClassified(t *testing.T) {
	ex := gateExports(t)
	if len(ex) < 20 {
		t.Fatalf("found only %d exported names: the scan is broken", len(ex))
	}
	var names []string
	for n := range ex {
		names = append(names, n)
	}
	sort.Strings(names)
	for _, n := range names {
		switch {
		case !incrEnvRelevant(n) && !incrEnvSkip[n]:
			// no matching prefix: not in the key
		case incrEnvSkip[n]:
			// bookkeeping, reviewed in TestRT04EnvSkipListIsPinned
		default:
			if _, ok := keyedGateExports[n]; !ok {
				t.Errorf("%s is exported by %v, is part of every item's and lane's key and is not classified: if its value differs from "+
					"one gate run to the next, no incremental gate run can ever skip anything (the bug of ad264a2). Bookkeeping: add it to "+
					"incrEnvSkip with its reason; a constant or something that changes what is checked: add it to keyedGateExports.", n, ex[n])
			}
		}
	}
	// the other direction: a classification of a name no script exports any more is stale
	for n := range keyedGateExports {
		if _, ok := ex[n]; !ok && n != "JANUS_GO_TOOLCHAIN" && n != "JANUS_COLD" {
			t.Errorf("keyedGateExports lists %s, which no gate script exports (stale)", n)
		}
	}
}

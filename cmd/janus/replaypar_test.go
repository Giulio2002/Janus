package main

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"
)

// parTree makes a synthetic framework library (an olean per module) and returns the library, the
// toolchain stand-in and the pins of the library.
func parTree(t *testing.T, mods ...string) (lib, tcLib string, fw *pinnedLib) {
	t.Helper()
	base := t.TempDir()
	lib, tcLib = filepath.Join(base, "lib"), filepath.Join(base, "tc")
	os.MkdirAll(tcLib, 0o755)
	writeBytes(t, filepath.Join(tcLib, "Init.olean"), []byte("core"))
	if len(mods) == 0 {
		mods = []string{"Janus", "Janus.A", "Janus.Amd64", "Janus.Amd64.T", "Janus.Amd64.U", "Janus.B.C", "Janus.Tactic", "Janus.Tactic.X", "Janus.Z"}
	}
	for _, m := range mods {
		writeBytes(t, filepath.Join(lib, filepath.FromSlash(moduleRel(m))), []byte("olean of "+m))
	}
	fw, err := newPinnedLib("the Janus framework build", lib, nil)
	if err != nil {
		t.Fatal(err)
	}
	return lib, tcLib, fw
}

// fakeChecker models leanchecker's target semantics over the oleans found under dirs (plus the
// extra directories): a target replays every module it is a name prefix of, prints
// `replaying m` for each, and fails on a module in forged. It records the targets it was given.
type fakeChecker struct {
	mu        sync.Mutex
	dirs      []string
	forged    map[string]bool // modules (as named on the search path) whose replay fails
	forgedB   map[string]bool // alias module bytes: forged root
	calls     [][]string
	failRun   int  // 1-based index of the call that dies (exit error, no output); 0 none
	quiet     bool // exit 0 but print nothing
	drop      string
	dropAlias bool
	n         int
}

func (f *fakeChecker) run(extra []string, argv ...string) (string, error) {
	f.mu.Lock()
	f.n++
	n := f.n
	f.calls = append(f.calls, append([]string{}, argv...))
	f.mu.Unlock()
	if f.failRun == n {
		return "", fmt.Errorf("signal: killed")
	}
	S := map[string]bool{}
	dirs := append(append([]string{}, f.dirs...), extra...)
	for _, d := range dirs {
		filepath.WalkDir(d, func(p string, e os.DirEntry, err error) error {
			if err == nil && !e.IsDir() && strings.HasSuffix(p, ".olean") {
				rel, _ := filepath.Rel(d, p)
				S[strings.ReplaceAll(strings.TrimSuffix(rel, ".olean"), "/", ".")] = true
			}
			return nil
		})
	}
	var out strings.Builder
	seen := map[string]bool{}
	for _, tg := range argv[2:] {
		found := false
		var ms []string
		for m := range S {
			if m == tg || isNamePrefix(tg, m) {
				ms = append(ms, m)
			}
		}
		sort.Strings(ms)
		for _, m := range ms {
			found = true
			if seen[m] {
				continue
			}
			seen[m] = true
			if f.forged[m] || (strings.HasPrefix(m, rootAliasPrefix) && f.forged["Janus"]) {
				return "leanchecker found a problem in " + m + "\nforged\n", errors.New("exit status 1")
			}
			if m != f.drop && !(f.dropAlias && strings.HasPrefix(m, rootAliasPrefix)) && !f.quiet {
				fmt.Fprintf(&out, "replaying %s\n", m)
			}
		}
		if !found {
			return "Could not find any oleans for: " + tg, errors.New("exit status 1")
		}
	}
	return out.String(), nil
}

func parFor(t *testing.T, lib, tcLib string, fc *fakeChecker, workers int) *parReplay {
	fc.dirs = []string{lib, tcLib}
	return &parReplay{dirs: []string{lib, tcLib}, workers: workers, aliasBase: t.TempDir(), run: fc.run}
}

func TestScanJanusModules(t *testing.T) {
	lib, tcLib, _ := parTree(t)
	got, err := scanJanusModules([]string{lib, tcLib})
	if err != nil {
		t.Fatal(err)
	}
	want := "Janus,Janus.A,Janus.Amd64,Janus.Amd64.T,Janus.Amd64.U,Janus.B.C,Janus.Tactic,Janus.Tactic.X,Janus.Z"
	if strings.Join(got, ",") != want {
		t.Fatalf("scan %v", got)
	}
	// Non-olean files, other roots and a second directory's extra module.
	writeBytes(t, filepath.Join(lib, "Janus", "A.ilean"), []byte("x"))
	writeBytes(t, filepath.Join(lib, "Janus", "A.olean.server"), []byte("x"))
	writeBytes(t, filepath.Join(lib, "JanusTests.olean"), []byte("x"))
	extra := t.TempDir()
	writeBytes(t, filepath.Join(extra, "Janus", "Extra", "Deep.olean"), []byte("x"))
	got, err = scanJanusModules([]string{lib, extra, tcLib})
	if err != nil || strings.Join(got, ",") != want+",Janus.Extra.Deep" {
		// sorted: Janus.Extra.Deep sorts after Janus.B.C and before Janus.Tactic
		if err != nil || !strings.Contains(strings.Join(got, ","), "Janus.Extra.Deep") || len(got) != 10 {
			t.Fatalf("scan with extra: %v %v", got, err)
		}
	}
	// Environments the scan cannot mirror exactly are unsupported, not guessed.
	bad := map[string]func(d string) []string{
		"relative dir": func(d string) []string { return []string{"rel/dir"} },
		"nested dirs":  func(d string) []string { return []string{d, filepath.Join(d, "Janus")} },
		"symlink olean": func(d string) []string {
			os.Symlink(filepath.Join(lib, "Janus", "A.olean"), filepath.Join(d, "Janus", "Ln.olean"))
			return []string{d}
		},
		"symlinked root": func(d string) []string {
			os.RemoveAll(filepath.Join(d, "Janus"))
			os.Symlink(filepath.Join(lib, "Janus"), filepath.Join(d, "Janus"))
			return []string{d}
		},
		"odd component": func(d string) []string {
			writeBytes(t, filepath.Join(d, "Janus", "Foo.bar.olean"), []byte("x"))
			return []string{d}
		},
		"olean directory": func(d string) []string {
			os.MkdirAll(filepath.Join(d, "Janus", "Dir.olean"), 0o755)
			return []string{d}
		},
	}
	for name, mk := range bad {
		d := t.TempDir()
		writeBytes(t, filepath.Join(d, "Janus", "A.olean"), []byte("x"))
		_, err := scanJanusModules(mk(d))
		if !errors.Is(err, errPlanUnsupported) {
			t.Errorf("%s: err %v", name, err)
		}
	}
}

func TestReplayUnitsCoverage(t *testing.T) {
	_, _, _ = parTree(t)
	S := []string{"Janus", "Janus.A", "Janus.Amd64", "Janus.Amd64.T", "Janus.B.C", "Janus.Tactic", "Janus.Tactic.X"}
	units := buildReplayUnits(S, rootAliasPrefix+"Rabc")
	if err := checkUnitCoverage(S, units); err != nil {
		t.Fatal(err)
	}
	var args []string
	for _, u := range units {
		args = append(args, u.arg)
	}
	sort.Strings(args)
	if strings.Join(args, ",") != "Janus.A,Janus.Amd64,Janus.B.C,Janus.Tactic,JanusReplayRootRabc" {
		t.Fatalf("units %v", args)
	}
	// Mutations: a dropped unit, a doubled unit, a unit covering a module twice, a module that
	// is not scanned, and a coverage list that differs from what the target replays.
	for i := range units {
		cut := append(append([]replayUnit{}, units[:i]...), units[i+1:]...)
		if err := checkUnitCoverage(S, cut); err == nil || !strings.Contains(err.Error(), "not covered") {
			t.Errorf("dropping unit %s: %v", units[i].arg, err)
		}
	}
	dup := append(append([]replayUnit{}, units...), units[0])
	if err := checkUnitCoverage(S, dup); err == nil {
		t.Error("doubled unit accepted")
	}
	if err := checkUnitCoverage(S[1:], units); err == nil {
		t.Error("a unit covering a module that was not scanned accepted")
	}
	short := append([]replayUnit{}, units...)
	for i := range short {
		if short[i].arg == "Janus.Tactic" {
			short[i].covers = []string{"Janus.Tactic"}
		}
	}
	if err := checkUnitCoverage(S, short); err == nil {
		t.Error("a unit whose covers differ from its target accepted")
	}
	// Without a root module there is no alias.
	for _, u := range buildReplayUnits(S[1:], rootAliasPrefix+"Rabc") {
		if u.alias {
			t.Error("alias without a root module")
		}
	}
}

func TestAssignUnitsEveryUnitOnce(t *testing.T) {
	var units []replayUnit
	for i := 0; i < 23; i++ {
		units = append(units, replayUnit{arg: fmt.Sprintf("Janus.M%d", i), weight: int64(i%5 + 1)})
	}
	units = append(units, replayUnit{arg: rootAliasPrefix + "Rabc", alias: true})
	for _, n := range []int{1, 2, 4, 50} {
		ws := assignUnits(units, n)
		seen := map[string]int{}
		for _, w := range ws {
			for _, u := range w {
				seen[u.arg]++
			}
		}
		if len(seen) != len(units) {
			t.Fatalf("n=%d: %d of %d units assigned", n, len(seen), len(units))
		}
		for a, c := range seen {
			if c != 1 {
				t.Fatalf("n=%d: %s assigned %d times", n, a, c)
			}
		}
	}
}

// Every module of the plan is replayed exactly once across the workers, the union equals the
// single process's set, and a forged module in ANY partition (the root, a leaf, a module with
// descendants, a descendant, an extra module) fails the replay with that worker's output.
func TestParallelReplayCatchesForgeryInEveryPartition(t *testing.T) {
	lib, tcLib, fw := parTree(t)
	extra := t.TempDir()
	writeBytes(t, filepath.Join(extra, "Janus", "Planted", "Extra.olean"), []byte("extra"))
	run := func(forged string) (string, error, *fakeChecker) {
		fc := &fakeChecker{forged: map[string]bool{}}
		if forged != "" {
			fc.forged[forged] = true
		}
		par := parFor(t, lib, tcLib, fc, 3)
		par.dirs = []string{lib, extra, tcLib}
		fc.dirs = par.dirs
		out, err := runFrameworkReplay("leanchecker", func(argv ...string) (string, error) { t.Error("single-process fallback"); return "", nil }, par, fw)
		return out, err, fc
	}
	_, err, fc := run("")
	if err != nil {
		t.Fatal(err)
	}
	// Union of the targets' replays equals the single `leanchecker Janus` set, each once.
	S, _ := scanJanusModules([]string{lib, extra, tcLib})
	got := map[string]int{}
	for _, call := range fc.calls {
		if call[1] != "-v" {
			t.Fatalf("argv %v", call)
		}
		for _, tg := range call[2:] {
			if strings.HasPrefix(tg, rootAliasPrefix) {
				got["Janus"]++
				continue
			}
			for _, m := range unitCovers(S, tg) {
				got[m]++
			}
		}
	}
	if len(got) != len(S) {
		t.Fatalf("replayed %d modules, single process replays %d: %v", len(got), len(S), got)
	}
	for m, c := range got {
		if c != 1 {
			t.Errorf("%s replayed %d times", m, c)
		}
	}
	for _, m := range S {
		forged := m
		out, err, _ := run(forged)
		if err == nil || !strings.Contains(out, "problem in "+forged) {
			t.Errorf("forged %s: err %v out %q", forged, err, out)
		}
	}
	// The forged root is caught through its alias (the alias directory holds the root's bytes).
	fc2 := &fakeChecker{forged: map[string]bool{"Janus": true}}
	par := parFor(t, lib, tcLib, fc2, 3)
	if out, err := runFrameworkReplay("leanchecker", nil, par, fw); err == nil || !strings.Contains(out, "problem in "+rootAliasPrefix) {
		t.Errorf("forged alias: %v %q", err, out)
	}
}

func TestParallelReplayWorkerFailuresAreFailures(t *testing.T) {
	lib, tcLib, fw := parTree(t)
	for name, mk := range map[string]func() *fakeChecker{
		"killed worker":        func() *fakeChecker { return &fakeChecker{failRun: 2} },
		"killed first":         func() *fakeChecker { return &fakeChecker{failRun: 1} },
		"exit 0 and no output": func() *fakeChecker { return &fakeChecker{quiet: true} },
		"one module missing":   func() *fakeChecker { return &fakeChecker{drop: "Janus.Amd64.U"} },
		"root missing":         func() *fakeChecker { return &fakeChecker{dropAlias: true} },
	} {
		fc := mk()
		par := parFor(t, lib, tcLib, fc, 3)
		if out, err := runFrameworkReplay("leanchecker", func(argv ...string) (string, error) { return "", nil }, par, fw); err == nil {
			t.Errorf("%s: passed (%q)", name, out)
		}
	}
	// An extra line (a module nobody planned) is a failure too.
	fc := &fakeChecker{}
	par := parFor(t, lib, tcLib, fc, 3)
	inner := par.run
	par.run = func(extra []string, argv ...string) (string, error) {
		out, err := inner(extra, argv...)
		return out + "replaying Janus.Ghost\n", err
	}
	if _, err := runFrameworkReplay("leanchecker", nil, par, fw); err == nil {
		t.Error("an unplanned module in the output passed")
	}
}

// A module deleted from the scan (so from the plan) while the pinned framework has it fails; a
// plan that does not contain a scanned module fails the equality assertion.
func TestParallelReplayDeletedModuleFails(t *testing.T) {
	lib, tcLib, fw := parTree(t)
	os.Remove(filepath.Join(lib, "Janus", "Z.olean"))
	fc := &fakeChecker{}
	par := parFor(t, lib, tcLib, fc, 3)
	if out, err := runFrameworkReplay("leanchecker", nil, par, fw); err == nil || !strings.Contains(out, "Janus.Z") {
		t.Fatalf("deleted pinned module: %v %q", err, out)
	}
}

func TestParallelReplayFallsBackToSingleProcess(t *testing.T) {
	lib, tcLib, fw := parTree(t)
	os.Symlink(filepath.Join(lib, "Janus", "A.olean"), filepath.Join(lib, "Janus", "Ln.olean"))
	fc := &fakeChecker{}
	par := parFor(t, lib, tcLib, fc, 3)
	var argvs [][]string
	_, err := runFrameworkReplay("leanchecker", func(argv ...string) (string, error) { argvs = append(argvs, argv); return "", nil }, par, fw)
	if err != nil || len(argvs) != 1 || strings.Join(argvs[0], " ") != "leanchecker Janus" || len(fc.calls) != 0 {
		t.Fatalf("fallback: %v %v %v", err, argvs, fc.calls)
	}
	// workers = 1 is the single process too.
	argvs = nil
	par.workers = 1
	runFrameworkReplay("leanchecker", func(argv ...string) (string, error) { argvs = append(argvs, argv); return "", nil }, par, fw)
	if len(argvs) != 1 {
		t.Fatalf("workers=1: %v", argvs)
	}
}

// The root alias carries the pinned bytes exactly; bytes that differ from the pin fail.
func TestRootAliasMatchesPins(t *testing.T) {
	lib, _, fw := parTree(t)
	writeBytes(t, filepath.Join(lib, "Janus.olean.server"), []byte("server part"))
	fw, _ = newPinnedLib("fw", lib, nil)
	d, cleanup, err := makeRootAlias(t.TempDir(), lib, rootAliasPrefix+"Rx", fw)
	if err != nil {
		t.Fatal(err)
	}
	defer cleanup()
	for _, ext := range []string{".olean", ".olean.server"} {
		a, _ := os.ReadFile(filepath.Join(lib, "Janus"+ext))
		b, err := os.ReadFile(filepath.Join(d, rootAliasPrefix+"Rx"+ext))
		if err != nil || string(a) != string(b) {
			t.Fatalf("alias %s: %v", ext, err)
		}
	}
	writeBytes(t, filepath.Join(lib, "Janus.olean"), []byte("changed after pinning"))
	if _, _, err := makeRootAlias(t.TempDir(), lib, rootAliasPrefix+"Rx", fw); err == nil {
		t.Fatal("alias of bytes that differ from the pin accepted")
	}
}

// A parallel replay that passes records the verdict; one that fails records nothing.
func TestParallelReplayVerdict(t *testing.T) {
	privateCache(t)
	lib, tcLib, fw := parTree(t)
	k := frameworkVerdictKey("tc", fw)
	fc := &fakeChecker{forged: map[string]bool{"Janus.B.C": true}}
	par := parFor(t, lib, tcLib, fc, 3)
	f := startFrameworkReplayPar(defaultVerdictStore(), "leanchecker", nil, par, k, fw, false, nil, true, true)
	f.wait()
	if f.err == nil || hasFrameworkVerdict(k) || !strings.Contains(f.out, "Janus.B.C") {
		t.Fatalf("failing parallel replay: err %v verdict %v out %q", f.err, hasFrameworkVerdict(k), f.out)
	}
	f.release()
	fc2 := &fakeChecker{}
	f = startFrameworkReplayPar(defaultVerdictStore(), "leanchecker", nil, parFor(t, lib, tcLib, fc2, 3), k, fw, false, nil, true, true)
	f.wait()
	if f.err != nil || !hasFrameworkVerdict(k) {
		t.Fatalf("passing parallel replay: err %v", f.err)
	}
	f.release()
}

var heavyReplayMu sync.Mutex

// realParFixture: the repository's framework build, the toolchain and a runner for the real
// leanchecker (unsandboxed; the sandbox does not change what is replayed).
func realParFixture(t *testing.T) (lib string, tc *toolchain, fw *pinnedLib, runIn func(lib string) func(extra []string, argv ...string) (string, error)) {
	t.Helper()
	// JANUS_REQUIRE_FIXTURE=1 (set by the gate's go-test lane): a missing fixture is a failure,
	// never a silent skip.
	missing := func(msg string) {
		t.Helper()
		if os.Getenv("JANUS_REQUIRE_FIXTURE") == "1" {
			t.Fatalf("JANUS_REQUIRE_FIXTURE=1 but %s", msg)
		}
		t.Skip(msg)
	}
	if testing.Short() {
		missing("running with -short")
	}
	lake, lerr := findLake()
	if lerr != nil {
		missing("lake not installed")
	}
	lib = filepath.Join(repoRoot, ".lake", "build", "lib", "lean")
	if _, err := os.Stat(filepath.Join(lib, "Janus.olean")); err != nil {
		missing("the repository's Janus build is not present (run lake build Janus Janus.Tools.Audit)")
	}
	var err error
	if tc, err = findToolchain(lake, repoRoot); err != nil || !tc.hasChecker {
		missing("no leanchecker")
	}
	// The real-leanchecker tests do not run concurrently with each other (each already runs
	// parallel workers; together they exceed a gate shard's memory limit).
	heavyReplayMu.Lock()
	t.Cleanup(heavyReplayMu.Unlock)
	fwd, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	if fw, err = frameworkPins(lib, fwd.Files); err != nil {
		t.Fatal(err)
	}
	runIn = func(lib string) func(extra []string, argv ...string) (string, error) {
		return func(extra []string, argv ...string) (string, error) {
			return runLean(&sandbox{mode: "none"}, tc, t.TempDir(), nil, tc.leanPathEnv(append(append([]string{}, extra...), lib)...), argv...)
		}
	}
	return
}

func realPar(t *testing.T, tc *toolchain, lib string, runIn func(string) func([]string, ...string) (string, error), workers int) (string, error, [][]string) {
	var mu sync.Mutex
	var calls [][]string
	r := runIn(lib)
	par := &parReplay{
		dirs:      append(filepath.SplitList(tc.leanPathEnv(lib)), filepath.Join(tc.sysroot, "lib", "lean")),
		workers:   workers,
		aliasBase: t.TempDir(),
		run: func(extra []string, argv ...string) (string, error) {
			mu.Lock()
			calls = append(calls, argv)
			mu.Unlock()
			return r(extra, argv...)
		},
	}
	fwl, _ := frameworkPins(lib, mustFrameworkFiles(t))
	out, err := runFrameworkReplay(tc.leanchecker, func(argv ...string) (string, error) { return r(nil, argv...) }, par, fwl)
	return out, err, calls
}

func mustFrameworkFiles(t *testing.T) map[string][]byte {
	fwd, err := loadFramework(repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	return fwd.Files
}

// The real leanchecker: the parallel plan passes on the honest framework and replays exactly the
// modules `leanchecker -v Janus` replays (each once).
func TestParallelFrameworkReplayMatchesSingleProcess(t *testing.T) {
	defer parallel(t)()
	lib, tc, _, runIn := realParFixture(t)
	single, err := runIn(lib)(nil, tc.leanchecker, "-v", "Janus")
	if err != nil {
		t.Fatalf("single process: %v\n%s", err, single)
	}
	want := map[string]int{}
	for _, mm := range replayingLineRE.FindAllStringSubmatch(single, -1) {
		want[mm[1]]++
	}
	out, err, calls := realPar(t, tc, lib, runIn, 4)
	if err != nil {
		t.Fatalf("parallel: %v\n%s", err, out)
	}
	if len(calls) < 2 {
		t.Fatalf("not partitioned: %v", calls)
	}
	// Re-derive what each call replayed from the real leanchecker (one -v run per call).
	got := map[string]int{}
	for _, c := range calls {
		o, err := runIn(lib)(aliasExtra(t, lib, c), c...)
		if err != nil {
			t.Fatalf("worker %v: %v\n%s", c, err, o)
		}
		for _, mm := range replayingLineRE.FindAllStringSubmatch(o, -1) {
			if strings.HasPrefix(mm[1], rootAliasPrefix) {
				got["Janus"]++
			} else {
				got[mm[1]]++
			}
		}
	}
	if len(got) != len(want) {
		t.Fatalf("parallel replays %d modules, single process %d", len(got), len(want))
	}
	for m, n := range want {
		if got[m] != n || n != 1 {
			t.Errorf("%s: single %d, parallel %d", m, n, got[m])
		}
	}
}

// aliasExtra makes the root alias directory when the call names it.
func aliasExtra(t *testing.T, lib string, argv []string) []string {
	for _, a := range argv {
		if strings.HasPrefix(a, rootAliasPrefix) {
			fwl, _ := frameworkPins(lib, mustFrameworkFiles(t))
			d, cleanup, err := makeRootAlias(t.TempDir(), lib, a, fwl)
			if err != nil {
				t.Fatal(err)
			}
			t.Cleanup(cleanup)
			return []string{d}
		}
	}
	return nil
}

// A forged declaration (kernel check skipped) in the root module, a leaf, a module with
// descendants and a descendant of one is caught by the real kernel replay of the plan.
func TestParallelFrameworkReplayCatchesForgeryInEveryPartition(t *testing.T) {
	defer parallel(t)()
	lib0, tc, _, runIn := realParFixture(t)
	lake, _ := findLake()
	forge, _ := os.ReadFile(filepath.Join(repoRoot, "audit", "attacks", "R1_forged_lemma.lean"))
	for _, mod := range []string{"Janus", "Janus.GoABI", "Janus.Tactic", "Janus.Amd64.Tactic"} {
		rel := strings.ReplaceAll(mod, ".", "/")
		lib := filepath.Join(t.TempDir(), "lib")
		if err := copyTree(lib0, lib); err != nil {
			t.Fatal(err)
		}
		src, _ := os.ReadFile(filepath.Join(repoRoot, rel+".lean"))
		fdir := t.TempDir()
		writeBytes(t, filepath.Join(fdir, rel+".lean"), append(append([]byte("import Lean\n"), src...), forge...))
		cmd := exec.Command(lake, "env", "lean", "--root="+fdir, "-o", filepath.Join(lib, rel+".olean"), filepath.Join(fdir, rel+".lean"))
		cmd.Dir = repoRoot
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("forging %s: %v\n%s", mod, err, out)
		}
		out, err, _ := realPar(t, tc, lib, runIn, 4)
		var mk *memKillError
		if errors.As(err, &mk) || strings.Contains(out, "memory limit") {
			t.Fatalf("forged %s: the replay was OOM-killed (inconclusive), not a detection: %v\n%s", mod, err, out)
		}
		if err == nil || !strings.Contains(out, "leanchecker found a problem in") || !strings.Contains(out, "forged") {
			t.Errorf("forged %s: not a kernel detection: err %v\n%s", mod, err, out)
		}
	}
}

// The root alias must not be shadowable: anything named like it anywhere on the search path
// (library, toolchain directory, a directory, any case) fails the plan with a hard error, never
// the single-process fallback and never a pass, and no worker starts.
func TestParallelReplayRefusesAliasShadow(t *testing.T) {
	plant := map[string]func(lib, tc string){
		"JanusReplayRoot.olean in the library": func(lib, tc string) { writeBytes(t, filepath.Join(lib, "JanusReplayRoot.olean"), []byte("forged")) },
		"JanusReplayRoot directory": func(lib, tc string) {
			writeBytes(t, filepath.Join(lib, "JanusReplayRoot", "Foo.olean"), []byte("forged"))
		},
		"JanusReplayRoot.olean in the toolchain": func(lib, tc string) { writeBytes(t, filepath.Join(tc, "JanusReplayRoot.olean"), []byte("forged")) },
		"random-pattern name": func(lib, tc string) {
			writeBytes(t, filepath.Join(lib, "JanusReplayRootR0123456789abcdef0123456789abcdef.olean"), []byte("forged"))
		},
		"other case": func(lib, tc string) { writeBytes(t, filepath.Join(lib, "janusreplayroot.olean"), []byte("forged")) },
		"server part only": func(lib, tc string) {
			writeBytes(t, filepath.Join(lib, "JanusReplayRoot.olean.server"), []byte("forged"))
		},
	}
	for name, mk := range plant {
		lib, tcLib, fw := parTree(t)
		mk(lib, tcLib)
		fc := &fakeChecker{}
		par := parFor(t, lib, tcLib, fc, 4)
		fell := false
		out, err := runFrameworkReplay("leanchecker", func(argv ...string) (string, error) { fell = true; return "", nil }, par, fw)
		if err == nil || fell || len(fc.calls) != 0 || !strings.Contains(out, "shadow") {
			t.Errorf("%s: err %v fallback %v workers %d out %q", name, err, fell, len(fc.calls), out)
		}
	}
}

// Each plan names the alias differently, and the runner puts the alias directory first.
func TestParallelReplayAliasNameIsRandom(t *testing.T) {
	a, _ := newRootAliasName()
	b, _ := newRootAliasName()
	if a == b || !strings.HasPrefix(a, rootAliasPrefix) || len(a) < len(rootAliasPrefix)+32 {
		t.Fatalf("alias names %q %q", a, b)
	}
	lib, tcLib, fw := parTree(t)
	fc := &fakeChecker{}
	par := parFor(t, lib, tcLib, fc, 4)
	if _, err := runFrameworkReplay("leanchecker", nil, par, fw); err != nil {
		t.Fatal(err)
	}
	seen := ""
	for _, c := range fc.calls {
		for _, a := range c[2:] {
			if strings.HasPrefix(a, rootAliasPrefix) {
				seen = a
			}
		}
	}
	if seen == "" || seen == rootAliasPrefix {
		t.Fatalf("alias argument %q", seen)
	}
}

func TestReplayWorkersCapAndThreadsRule(t *testing.T) {
	for in, want := range map[string]int{"": 4, "0": 4, "-3": 4, "abc": 4, "1": 1, "6": 6, "8": 8, "9": 8, "1000000": 8} {
		t.Setenv("JANUS_REPLAY_WORKERS", in)
		if got := replayWorkers(); got != want {
			t.Errorf("JANUS_REPLAY_WORKERS=%q: %d, want %d", in, got, want)
		}
	}
}

func TestAliasShadowCaseFoldAndUnlistable(t *testing.T) {
	for _, n := range []string{"JanusReplayRoot", "JANUSREPLAYROOT.olean", "janusreplayroot", "JanuſReplayRoot.olean", "JanusReplayRootRabc"} {
		if !hasAliasPrefix(n) {
			t.Errorf("%q not recognised as the alias prefix", n)
		}
	}
	for _, n := range []string{"JanusReplayRoo", "xJanusReplayRoot", "Janus", ""} {
		if hasAliasPrefix(n) {
			t.Errorf("%q wrongly recognised", n)
		}
	}
	// A search directory that cannot be listed (here: below a regular file) is a hard error.
	d := t.TempDir()
	f := filepath.Join(d, "file")
	writeBytes(t, f, []byte("x"))
	if err := refuseAliasShadow([]string{filepath.Join(f, "sub")}); err == nil || !strings.Contains(err.Error(), "cannot list") {
		t.Errorf("unlistable directory: %v", err)
	}
	// A missing directory or a plain file in the path is skipped, as Lean does.
	if err := refuseAliasShadow([]string{filepath.Join(d, "missing"), f}); err != nil {
		t.Errorf("missing/non-directory entries: %v", err)
	}
}

// Expensive end-to-end test through `janus verify --janus-root` (production path: sandbox, memory
// guard, parallel framework replay with its default workers): the honest control records a
// framework verdict; a build whose ROOT olean is forged records none, with or without an honest
// copy planted as JanusReplayRoot.olean (which is refused).
func TestParallelReplayE2EForgedRootNoVerdict(t *testing.T) {
	_, _, _, _ = realParFixture(t)
	useTestCache(t)
	for _, plant := range []string{"control-honest-extra-decl", "forged-root", "forged-root-with-planted-honest-JanusReplayRoot"} {
		t.Run(plant, func(t *testing.T) {
			root := filepath.Join(t.TempDir(), "janus")
			for _, f := range []string{"lakefile.toml", "lake-manifest.json", "lean-toolchain", "Janus.lean"} {
				b, err := os.ReadFile(filepath.Join(repoRoot, f))
				if err != nil {
					t.Fatal(err)
				}
				writeBytes(t, filepath.Join(root, f), b)
			}
			if err := copyTree(filepath.Join(repoRoot, "Janus"), filepath.Join(root, "Janus")); err != nil {
				t.Fatal(err)
			}
			if err := copyTree(filepath.Join(repoRoot, ".lake", "build"), filepath.Join(root, ".lake", "build")); err != nil {
				t.Fatal(err)
			}
			lib := filepath.Join(root, ".lake", "build", "lib", "lean")
			honest, _ := os.ReadFile(filepath.Join(lib, "Janus.olean"))
			src, _ := os.ReadFile(filepath.Join(repoRoot, "Janus.lean"))
			forge := "\ntheorem Janus.okayRoot : 1 = 1 := rfl\n"
			if plant != "control-honest-extra-decl" {
				forge = "\nopen Lean in\nset_option debug.skipKernelTC true in\nrun_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {\n  name := `Janus.forgedRoot, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })\n"
			}
			fdir := filepath.Join(t.TempDir(), "forge")
			writeBytes(t, filepath.Join(fdir, "Janus.lean"), append(append([]byte{}, src...), forge...))
			lake, _ := findLake()
			os.Remove(filepath.Join(lib, "Janus.olean"))
			cmd := exec.Command(lake, "env", "lean", "--root="+fdir, "-o", filepath.Join(lib, "Janus.olean"), filepath.Join(fdir, "Janus.lean"))
			cmd.Dir = root
			if out, err := cmd.CombinedOutput(); err != nil {
				t.Fatalf("forging: %v\n%s", err, out)
			}
			if strings.HasSuffix(plant, "JanusReplayRoot") {
				writeBytes(t, filepath.Join(lib, "JanusReplayRoot.olean"), honest)
			}
			fwd, err := loadFramework(root)
			if err != nil {
				t.Fatal(err)
			}
			tc, err := findToolchain(lake, root)
			if err != nil {
				t.Fatal(err)
			}
			pinned, err := frameworkPins(lib, fwd.Files)
			if err != nil {
				t.Fatal(err)
			}
			k := frameworkVerdictKey(tc.cacheID(), pinned)
			if hasFrameworkVerdict(k) {
				t.Fatal("verdict already present")
			}
			add := mustExtract(t, "example.com/basic.Add")
			proof := filepath.Join(t.TempDir(), "Proof.lean")
			writeBytes(t, proof, []byte("import Extracted\nnamespace Proof\ntheorem correctness : Extracted.program.data.length = Extracted.program.data.length := rfl\nend Proof\n"))
			code, out, stderr := runJanus(t, "verify", add, "--proof", proof, "--janus-root", root)
			t.Logf("code=%d out=%q stderr=%.1500q", code, out, stderr)
			if plant == "control-honest-extra-decl" {
				if strings.Contains(stderr, "memory limit") {
					t.Errorf("control was killed for memory:\n%.800s", stderr)
				}
				if !hasFrameworkVerdict(k) {
					t.Errorf("control: no verdict recorded for an honest build (parallel path not exercised?)")
				}
				return
			}
			if hasFrameworkVerdict(k) {
				t.Errorf("a framework verdict was recorded for the forged-root build")
			}
			// A resource kill is inconclusive, never a detection: the rejection must be the kernel's.
			if strings.Contains(stderr, "memory limit") || strings.Contains(stderr, "resource limit") {
				t.Errorf("the verification was killed for memory, which proves nothing about the forgery:\n%.800s", stderr)
			} else if code == 0 || !strings.Contains(stderr, "Kernel replay rejected") {
				t.Errorf("forged root not rejected by the kernel replay: code %d\n%.800s", code, stderr)
			}
		})
	}
}

func TestReplaySizing(t *testing.T) {
	t.Setenv("JANUS_REPLAY_THREADS", "")
	const G = int64(1) << 30
	for _, c := range []struct {
		want                    int
		eff, guard              int64
		wantWorkers, wantThread int
		why                     string
	}{
		{4, 251 * G, 24 * G, 4, 4, "big host: 4 x 10 GiB fits in half"},
		{4, 80 * G, 24 * G, 4, 4, "4 x 10 = 40 = half of 80"},
		{4, 79 * G, 24 * G, 4, 2, "just under: 2 threads, 4 x 5 fits"},
		{4, 24 * G, 24 * G, 2, 2, "24 GiB enclosing cgroup (a gate shard): half = 12 GiB, 2 workers of 5"},
		{4, 8 * G, 8 * G, 1, 2, "tiny: one worker"},
		{8, 128 * G, 24 * G, 8, 2, "8 x 10 = 80 > 64: 2 threads, 8 x 5 = 40 fits"},
		{4, 251 * G, 11 * G, 4, 2, "guard limit below 12 GiB: 2 threads"},
		{4, 0, 0, 4, 2, "unknown limit: as requested, 2 threads"},
	} {
		w, th := replaySizing(c.want, c.eff, c.guard, -1)
		if w != c.wantWorkers || th != c.wantThread {
			t.Errorf("%s: %d workers x %d threads, want %d x %d", c.why, w, th, c.wantWorkers, c.wantThread)
		}
	}
	// Little headroom in the enclosing cgroup (other janus processes use it): fewer workers.
	t.Setenv("JANUS_REPLAY_THREADS", "")
	if w, th := replaySizing(4, 20*G, 20*G, 6*G); w != 1 || th != 2 {
		t.Errorf("20 GiB slot with 6 GiB free: %d x %d", w, th)
	}
	if w, th := replaySizing(4, 20*G, 20*G, 0); w != 1 || th != 2 {
		t.Errorf("no headroom: %d x %d, want the single worker", w, th)
	}
	t.Setenv("JANUS_REPLAY_THREADS", "3")
	if _, th := replaySizing(4, 251*G, 24*G, -1); th != 3 {
		t.Errorf("JANUS_REPLAY_THREADS must win: %d", th)
	}
}

// A fake cgroup tree with small memory.max values: the effective limit is the smallest on the
// path, and the host/guard limits count too.
func TestEffectiveLimitFakeCgroupTree(t *testing.T) {
	root := t.TempDir()
	write := func(rel, v string) {
		writeBytes(t, filepath.Join(root, rel, "memory.max"), []byte(v+"\n"))
	}
	write("", "max")
	write("a", "30000000000")
	write("a/b", "max")
	write("a/b/c", "24000000000")
	write("a/b/c/d", "max")
	if got := cgroupChainLimit(filepath.Join(root, "a/b/c/d"), root); got != 24000000000 {
		t.Errorf("chain limit %d", got)
	}
	write("a/b", "1000000000")
	if got := cgroupChainLimit(filepath.Join(root, "a/b/c/d"), root); got != 1000000000 {
		t.Errorf("chain limit with a smaller ancestor %d", got)
	}
	if got := cgroupChainLimit(filepath.Join(root, "x"), root); got != 0 {
		t.Errorf("no limits: %d", got)
	}
	const G = int64(1) << 30
	if got := effectiveLimit(251*G, 24*G, 24*G); got != 24*G {
		t.Errorf("effective %d", got)
	}
	if got := effectiveLimit(251*G, 0, 0); got != 251*G {
		t.Errorf("effective host only %d", got)
	}
	if got := effectiveLimit(16*G, 24*G, 24*G); got != 16*G {
		t.Errorf("effective small host %d", got)
	}
}

// The admission: workers never hold more than the budget at once (a lone oversized request is
// admitted alone), and everything is released.
func TestMemBudgetAdmission(t *testing.T) {
	b := newMemBudget(10)
	var mu sync.Mutex
	cur, maxCur := int64(0), int64(0)
	var wg sync.WaitGroup
	for i := 0; i < 12; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			rel := b.acquire(4)
			mu.Lock()
			cur += 4
			if cur > maxCur {
				maxCur = cur
			}
			mu.Unlock()
			time.Sleep(5 * time.Millisecond)
			mu.Lock()
			cur -= 4
			mu.Unlock()
			rel()
		}()
	}
	wg.Wait()
	if maxCur > 10 || b.used != 0 {
		t.Errorf("held up to %d of 10, used after %d", maxCur, b.used)
	}
	rel := b.acquire(1000)
	if b.used != 10 {
		t.Errorf("oversized request holds %d", b.used)
	}
	rel()
	if newMemBudget(0).acquire(5) == nil {
		t.Error("no budget: nil release")
	}
}

// The admission around every leanchecker command: a kill by the memory guard is retried ONCE with
// a single thread; another error is not retried; the second kill is still a memKillError (never a
// detection); concurrent commands stay within the budget.
func TestRunCheckerAdmittedRetriesOOMOnce(t *testing.T) {
	b := newMemBudget(workerPeak(2))
	var calls []int
	kill := &memKillError{ev: memEvent{Label: "x", Killed: true}, err: errors.New("signal: killed")}
	out, err := runCheckerAdmitted(b, 2, func(th int) (string, error) {
		calls = append(calls, th)
		if th == 2 {
			return "", kill
		}
		return "ok", nil
	})
	if err != nil || out != "ok" || len(calls) != 2 || calls[0] != 2 || calls[1] != 1 || b.used != 0 {
		t.Fatalf("retry: %v %q %v used %d", err, out, calls, b.used)
	}
	calls = nil
	_, err = runCheckerAdmitted(b, 4, func(th int) (string, error) { calls = append(calls, th); return "", kill })
	var mk *memKillError
	if !errors.As(err, &mk) || len(calls) != 2 {
		t.Fatalf("second kill: %v %v", err, calls)
	}
	calls = nil
	_, err = runCheckerAdmitted(b, 2, func(th int) (string, error) {
		calls = append(calls, th)
		return "leanchecker found a problem in Janus.X", errors.New("exit status 1")
	})
	if err == nil || len(calls) != 1 {
		t.Fatalf("kernel error retried or lost: %v %v", err, calls)
	}
	var mu sync.Mutex
	cur, maxCur := 0, 0
	var wg sync.WaitGroup
	for i := 0; i < 6; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			runCheckerAdmitted(b, 2, func(int) (string, error) {
				mu.Lock()
				cur++
				if cur > maxCur {
					maxCur = cur
				}
				mu.Unlock()
				time.Sleep(5 * time.Millisecond)
				mu.Lock()
				cur--
				mu.Unlock()
				return "", nil
			})
		}()
	}
	wg.Wait()
	if maxCur != 1 {
		t.Errorf("%d commands at once over a one-command budget", maxCur)
	}
}

func TestCgroupChainHeadroomFake(t *testing.T) {
	root := t.TempDir()
	set := func(rel, max, cur, inactive string) {
		writeBytes(t, filepath.Join(root, rel, "memory.max"), []byte(max+"\n"))
		writeBytes(t, filepath.Join(root, rel, "memory.current"), []byte(cur+"\n"))
		writeBytes(t, filepath.Join(root, rel, "memory.stat"), []byte("anon 1\ninactive_file "+inactive+"\n"))
	}
	set("", "max", "0", "0")
	set("slot", "20000000000", "12000000000", "2000000000") // 20 GB limit, 10 GB unreclaimable
	set("slot/lane", "max", "1000000000", "0")
	if got := cgroupChainHeadroom(filepath.Join(root, "slot/lane"), root); got != 10000000000 {
		t.Errorf("headroom %d, want 10e9", got)
	}
	if got := cgroupChainHeadroom(filepath.Join(root, "nolimit"), root); got != -1 {
		t.Errorf("unlimited: %d", got)
	}
}

// Mirror of a rounds slot: run under `memcap -m 20G` with JANUS_PRESSURE_TEST=1. Two honest
// framework replays run concurrently while this process holds a 10 GiB hog; both must complete
// (fewer workers, retried serially if killed) and the verdict for the honest build is recorded.
func TestReplayUnderMemoryPressure(t *testing.T) {
	if os.Getenv("JANUS_PRESSURE_TEST") != "1" {
		t.Skip("expensive: run under memcap -m 20G with JANUS_PRESSURE_TEST=1")
	}
	lib, tc, _, runIn := realParFixture(t)
	hog := make([]byte, 10<<30)
	for i := 0; i < len(hog); i += 4096 {
		hog[i] = 1
	}
	defer func(b []byte) { _ = b[0] }(hog)
	eff, head := effectiveMemLimit(), currentHeadroom()
	w, th := replaySizing(replayWorkers(), eff, guardLimitBytes(), head)
	t.Logf("effective %s headroom %s -> %d workers x %d threads", fmtBytes(eff), fmtBytes(head), w, th)
	if w >= 4 && head >= 0 && head < 20<<30 {
		t.Errorf("did not degrade under pressure: %d workers", w)
	}
	fwl, _ := frameworkPins(lib, mustFrameworkFiles(t))
	var wg sync.WaitGroup
	for i := 0; i < 2; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			r := runIn(lib)
			par := &parReplay{
				dirs:      append(filepath.SplitList(tc.leanPathEnv(lib)), filepath.Join(tc.sysroot, "lib", "lean")),
				workers:   w,
				aliasBase: t.TempDir(),
				run: func(extra []string, argv ...string) (string, error) {
					return runLeanProtectedThreads(&sandbox{mode: "none"}, tc, t.TempDir(), nil, nil, tc.leanPathEnv(append(append([]string{}, extra...), lib)...), th, argv...)
				},
			}
			_ = r
			if out, err := runFrameworkReplay(tc.leanchecker, func(argv ...string) (string, error) {
				return runLeanProtectedThreads(&sandbox{mode: "none"}, tc, t.TempDir(), nil, nil, tc.leanPathEnv(lib), 0, argv...)
			}, par, fwl); err != nil {
				t.Errorf("replay under pressure: %v\n%.500s", err, out)
			}
		}()
	}
	wg.Wait()
}

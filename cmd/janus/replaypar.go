package main

// Parallel kernel replay of the Janus framework (the same check as `leanchecker Janus`).
//
// What `leanchecker Janus` does (LeanChecker.lean of the toolchain, quoted in docs/SOUNDNESS.md):
// it walks every directory of the search path (LEAN_PATH, then the toolchain library) for
// `*.olean` files, keeps each module whose name Janus is a component-wise prefix of (Janus
// itself and every Janus.* module), and for each such module m, in its own task, reads m's
// olean (found by findOLean: the first search-path directory with a Janus entry), imports m's
// *imports* (loaded from their oleans, not replayed there) and replays m's OWN constants through
// the kernel into that environment. So a module's check depends only on its own bytes and on the
// bytes of its imports, never on whether another module is replayed in the same process, and
// the set of modules replayed is exactly the scanned set S. Partitioning S over several
// leanchecker processes is therefore sound and complete if (and only if) the union of what the
// processes replay is S and every worker succeeds.
//
// A leanchecker target is a name prefix, so a module with descendants (Janus, Janus.Amd64,
// Janus.Tactic) cannot be named exactly. The units are: every top-level group of S below the
// root (a module and its descendants, replayed by one target; leaves are groups of one), and the
// root module Janus, replayed through a byte-identical copy of its olean (and server/private
// parts) installed under the name JanusReplayRoot in a janus-made read-only directory: the
// replay reads only the file's bytes (its own name is not part of the module data), so the copy
// is checked exactly like the original and no descendant is replayed with it.
//
// Fail closed: the plan is built from the scanned S and re-checked (every module of S covered by
// exactly one unit, nothing else); each worker runs with -v and its `replaying <module>` lines
// must be exactly the modules its targets cover, so a divergence between this scan and
// leanchecker's own is a failure, never a pass. Any worker error, crash or missing line fails
// the replay. Environments the scan cannot mirror exactly (relative or nested search
// directories, symlinks or odd file names under Janus) use the single `leanchecker Janus`
// process instead.

import (
	"crypto/rand"
	"encoding/hex"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
)

// rootAliasPrefix starts the module name the root module's olean copy is replayed under; each
// replay appends fresh random hex (newRootAliasName), so a file planted before the run cannot
// have the name. Anything on the search path that starts with the prefix (any case) is refused.
const rootAliasPrefix = "JanusReplayRoot"

func newRootAliasName() (string, error) {
	var b [16]byte
	if _, err := rand.Read(b[:]); err != nil {
		return "", err
	}
	return rootAliasPrefix + "R" + hex.EncodeToString(b[:]), nil
}

// parReplay configures a parallel framework replay.
type parReplay struct {
	dirs      []string // the search path leanchecker sees: LEAN_PATH entries, then the toolchain library
	workers   int      // concurrent leanchecker processes (<= 1: the single process)
	aliasBase string   // directory under which the root alias directory is made
	// run runs leanchecker argv with the extra directories placed FIRST on the search path.
	run func(extra []string, argv ...string) (string, error)
}

// replayWorkers is the number of concurrent leanchecker processes of a parallel framework replay
// ($JANUS_REPLAY_WORKERS, default 4; 1 selects the single process).
func replayWorkers() int {
	if n, err := strconv.Atoi(os.Getenv("JANUS_REPLAY_WORKERS")); err == nil && n > 0 {
		return n
	}
	return 4
}

// errPlanUnsupported marks an environment whose module set the scan cannot mirror exactly; the
// caller uses the single process.
var errPlanUnsupported = errors.New("parallel replay plan unsupported")

func unsupported(format string, a ...any) error {
	return fmt.Errorf("%w: %s", errPlanUnsupported, fmt.Sprintf(format, a...))
}

var simpleComponent = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_]*$`)

// scanJanusModules mirrors leanchecker's target discovery for the target Janus: the module names
// of the form Janus(.component)* with an `.olean` file in some directory of dirs, as a sorted set.
func scanJanusModules(dirs []string) ([]string, error) {
	real := make([]string, 0, len(dirs))
	for _, d := range dirs {
		if d == "" || !filepath.IsAbs(d) {
			return nil, unsupported("search directory %q is not absolute", d)
		}
		st, err := os.Stat(d)
		if err != nil || !st.IsDir() {
			continue // Lean skips non-directories
		}
		r, err := filepath.EvalSymlinks(d)
		if err != nil {
			return nil, unsupported("search directory %q: %v", d, err)
		}
		real = append(real, filepath.Clean(r))
	}
	for i, a := range real {
		for j, b := range real {
			if i != j && a != b && strings.HasPrefix(b+string(filepath.Separator), a+string(filepath.Separator)) {
				return nil, unsupported("search directory %q is nested in %q", b, a)
			}
		}
	}
	set := map[string]bool{}
	for _, d := range real {
		if st, err := os.Lstat(filepath.Join(d, "Janus.olean")); err == nil {
			if !st.Mode().IsRegular() {
				return nil, unsupported("%s is not a regular file", filepath.Join(d, "Janus.olean"))
			}
			set["Janus"] = true
		}
		root := filepath.Join(d, "Janus")
		st, err := os.Lstat(root)
		if err != nil {
			continue
		}
		if !st.IsDir() { // a symlink or a plain file named Janus
			if st.Mode()&fs.ModeSymlink != 0 {
				return nil, unsupported("%s is a symlink", root)
			}
			continue
		}
		err = filepath.WalkDir(root, func(path string, e fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if e.Type()&fs.ModeSymlink != 0 {
				return unsupported("%s is a symlink", path)
			}
			if e.IsDir() {
				if strings.HasSuffix(e.Name(), ".olean") {
					return unsupported("%s is a directory named like an olean", path)
				}
				return nil
			}
			if !strings.HasSuffix(e.Name(), ".olean") {
				return nil
			}
			if !e.Type().IsRegular() {
				return unsupported("%s is not a regular file", path)
			}
			rel, _ := filepath.Rel(d, path)
			comps := strings.Split(strings.TrimSuffix(filepath.ToSlash(rel), ".olean"), "/")
			for _, c := range comps {
				if !simpleComponent.MatchString(c) {
					return unsupported("%s: module name component %q is not a plain identifier", path, c)
				}
			}
			set[strings.Join(comps, ".")] = true
			return nil
		})
		if err != nil {
			if errors.Is(err, errPlanUnsupported) {
				return nil, err
			}
			return nil, unsupported("scanning %s: %v", root, err)
		}
	}
	out := make([]string, 0, len(set))
	for m := range set {
		out = append(out, m)
	}
	sort.Strings(out)
	return out, nil
}

// replayUnit is one leanchecker target of the plan: the modules it replays (covers), and
// what its -v output must name (expect: the same, or the alias name for the root).
type replayUnit struct {
	arg    string
	alias  bool // the root module, replayed through its olean copy
	covers []string
	expect []string
	weight int64
}

// unitCovers is what leanchecker's target arg replays among the scanned modules S: arg itself
// and every module it is a name prefix of.
func unitCovers(S []string, arg string) []string {
	var out []string
	for _, m := range S {
		if m == arg || isNamePrefix(arg, m) {
			out = append(out, m)
		}
	}
	return out
}

// buildReplayUnits partitions S into units (see the file comment).
func buildReplayUnits(S []string, alias string) []replayUnit {
	var units []replayUnit
	var below []string
	for _, m := range S {
		if m == "Janus" {
			units = append(units, replayUnit{arg: alias, alias: true, covers: []string{"Janus"}, expect: []string{alias}})
			continue
		}
		below = append(below, m)
	}
	for _, m := range below { // sorted: an ancestor sorts before its descendants
		head := true
		for _, h := range below {
			if isNamePrefix(h, m) {
				head = false
				break
			}
		}
		if head {
			c := unitCovers(below, m)
			units = append(units, replayUnit{arg: m, covers: c, expect: append([]string{}, c...)})
		}
	}
	return units
}

// checkUnitCoverage asserts the plan's set equality with S: every module of S is covered by
// exactly one unit, the units' recorded coverage is what their targets replay among S, and no
// unit covers anything else. It is the guard against a module dropped (or doubled) by the
// partition.
func checkUnitCoverage(S []string, units []replayUnit) error {
	inS := map[string]bool{}
	for _, m := range S {
		inS[m] = true
	}
	seen := map[string]string{}
	for _, u := range units {
		if !u.alias {
			if got := unitCovers(S, u.arg); strings.Join(got, ",") != strings.Join(u.covers, ",") {
				return fmt.Errorf("replay plan: unit %s covers %v but its target replays %v", u.arg, u.covers, got)
			}
		} else if len(u.covers) != 1 || u.covers[0] != "Janus" {
			return fmt.Errorf("replay plan: alias unit covers %v", u.covers)
		}
		for _, m := range u.covers {
			if !inS[m] {
				return fmt.Errorf("replay plan: unit %s covers %s, which is not a scanned module", u.arg, m)
			}
			if prev, dup := seen[m]; dup {
				return fmt.Errorf("replay plan: module %s is covered by both %s and %s", m, prev, u.arg)
			}
			seen[m] = u.arg
		}
	}
	for _, m := range S {
		if _, ok := seen[m]; !ok {
			return fmt.Errorf("replay plan: module %s is not covered by any unit", m)
		}
	}
	return nil
}

// assignUnits distributes units over at most n workers (heaviest first onto the lightest
// worker); the alias unit is its own worker (it needs the alias directory on the search path).
// Every unit lands in exactly one worker.
func assignUnits(units []replayUnit, n int) [][]replayUnit {
	var alias, rest []replayUnit
	for _, u := range units {
		if u.alias {
			alias = append(alias, u)
		} else {
			rest = append(rest, u)
		}
	}
	sort.SliceStable(rest, func(i, j int) bool { return rest[i].weight > rest[j].weight })
	if n < 1 {
		n = 1
	}
	if n > len(rest) {
		n = len(rest)
	}
	bins := make([][]replayUnit, n)
	load := make([]int64, n)
	for _, u := range rest {
		b := 0
		for i := range load {
			if load[i] < load[b] {
				b = i
			}
		}
		bins[b] = append(bins[b], u)
		load[b] += u.weight
	}
	var out [][]replayUnit
	for _, a := range alias {
		out = append(out, []replayUnit{a})
	}
	for _, b := range bins {
		if len(b) > 0 {
			out = append(out, b)
		}
	}
	return out
}

// moduleFileWeight is the size of the olean of m as the replay resolves it (first directory with
// a Janus entry), plus a constant for importing; the weight only balances workers.
func moduleFileWeight(first string, m string) int64 {
	w := int64(1 << 20)
	if st, err := os.Stat(filepath.Join(first, filepath.FromSlash(moduleRel(m)))); err == nil {
		w += st.Size()
	}
	return w
}

// firstJanusDir is the search directory findOLean resolves Janus modules in: the first with a
// Janus directory or Janus.olean.
func firstJanusDir(dirs []string) string {
	for _, d := range dirs {
		if st, err := os.Stat(filepath.Join(d, "Janus")); err == nil && st.IsDir() {
			return d
		}
		if _, err := os.Stat(filepath.Join(d, "Janus.olean")); err == nil {
			return d
		}
	}
	return ""
}

// makeRootAlias installs byte-identical copies of the root module's olean (and its server and
// private parts, when present) under the alias name in a fresh directory under base, and checks
// the copies against the framework pins. It returns the directory and its cleanup.
func makeRootAlias(base, from, name string, fw *pinnedLib) (string, func(), error) {
	dir, err := os.MkdirTemp(base, "replay-root-")
	if err != nil {
		return "", func() {}, err
	}
	cleanup := func() { os.RemoveAll(dir) }
	for _, ext := range []string{".olean", ".olean.server", ".olean.private"} {
		src := filepath.Join(from, "Janus"+ext)
		st, err := os.Lstat(src)
		if err != nil {
			if ext == ".olean" {
				cleanup()
				return "", func() {}, unsupported("no Janus.olean in %s", from)
			}
			continue
		}
		if !st.Mode().IsRegular() {
			cleanup()
			return "", func() {}, unsupported("%s is not a regular file", src)
		}
		b, err := os.ReadFile(src)
		if err != nil {
			cleanup()
			return "", func() {}, err
		}
		if want, ok := fw.want["Janus"+ext]; ok && want != sha256Hex(b) {
			cleanup()
			return "", func() {}, fmt.Errorf("the framework's %s does not match its pin; the build changed during the replay", src)
		}
		if err := os.WriteFile(filepath.Join(dir, name+ext), b, 0o444); err != nil {
			cleanup()
			return "", func() {}, err
		}
	}
	return dir, cleanup, nil
}

var replayingLineRE = regexp.MustCompile(`(?m)^replaying (\S+)\s*$`)

// checkWorkerOutput requires the -v output of a worker that exited 0 to name exactly the
// modules its targets replay, each once.
func checkWorkerOutput(out string, units []replayUnit) error {
	want := map[string]int{}
	for _, u := range units {
		for _, m := range u.expect {
			want[m]++
		}
	}
	got := map[string]int{}
	for _, mm := range replayingLineRE.FindAllStringSubmatch(out, -1) {
		got[mm[1]]++
	}
	var bad []string
	for m, n := range want {
		if got[m] != n {
			bad = append(bad, fmt.Sprintf("%s: expected %d, got %d", m, n, got[m]))
		}
	}
	for m, n := range got {
		if want[m] == 0 {
			bad = append(bad, fmt.Sprintf("%s: unexpected (%d)", m, n))
		}
	}
	if len(bad) > 0 {
		sort.Strings(bad)
		return fmt.Errorf("the replay did not report exactly the planned modules (%s)", strings.Join(bad, "; "))
	}
	return nil
}

// planFrameworkReplay scans the search path and builds the partition. It returns
// errPlanUnsupported (wrapped) for environments the scan cannot mirror exactly.
func planFrameworkReplay(par *parReplay, fw *pinnedLib) ([][]replayUnit, error) {
	S, err := scanJanusModules(par.dirs)
	if err != nil {
		return nil, err
	}
	if len(S) == 0 {
		return nil, unsupported("no Janus module on the search path")
	}
	inS := map[string]bool{}
	for _, m := range S {
		inS[m] = true
	}
	for _, m := range frameworkModules(fw) {
		if !inS[m] {
			return nil, fmt.Errorf("replay plan: pinned framework module %s is not on the search path", m)
		}
	}
	if err := refuseAliasShadow(par.dirs); err != nil {
		return nil, err
	}
	aliasName, err := newRootAliasName()
	if err != nil {
		return nil, err
	}
	units := buildReplayUnits(S, aliasName)
	first := firstJanusDir(par.dirs)
	for i := range units {
		for _, m := range units[i].covers {
			units[i].weight += moduleFileWeight(first, m)
		}
	}
	if err := checkUnitCoverage(S, units); err != nil {
		return nil, err
	}
	return assignUnits(units, par.workers), nil
}

// runFrameworkReplay replays the framework: the single `leanchecker Janus` process, or the
// parallel plan (workers, with the single process as the fallback for unsupported environments).
// It returns leanchecker's output of the first failing worker (in plan order).
func runFrameworkReplay(checker string, run func(argv ...string) (string, error), par *parReplay, fw *pinnedLib) (string, error) {
	if par == nil || par.workers <= 1 {
		return run(checker, "Janus")
	}
	workers, err := planFrameworkReplay(par, fw)
	if errors.Is(err, errPlanUnsupported) {
		return run(checker, "Janus")
	}
	if err != nil {
		return err.Error(), err
	}
	var aliasDir string
	for _, w := range workers {
		for _, u := range w {
			if u.alias {
				d, cleanup, err := makeRootAlias(par.aliasBase, firstJanusDir(par.dirs), u.arg, fw)
				if errors.Is(err, errPlanUnsupported) {
					return run(checker, "Janus")
				}
				if err != nil {
					return err.Error(), err
				}
				defer cleanup()
				aliasDir = d
			}
		}
	}
	outs := make([]string, len(workers))
	errs := make([]error, len(workers))
	sem := make(chan struct{}, par.workers)
	var wg sync.WaitGroup
	for i, w := range workers {
		wg.Add(1)
		go func(i int, w []replayUnit) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()
			argv := []string{checker, "-v"}
			var extra []string
			for _, u := range w {
				argv = append(argv, u.arg)
				if u.alias {
					extra = []string{aliasDir}
				}
			}
			out, err := par.run(extra, argv...)
			if err == nil {
				err = checkWorkerOutput(out, w)
				if err != nil {
					out = err.Error() + "\n" + out
				}
			}
			outs[i], errs[i] = out, err
		}(i, w)
	}
	wg.Wait()
	for i := range workers {
		if errs[i] != nil {
			return outs[i], errs[i]
		}
	}
	return "", nil
}

// refuseAliasShadow fails the replay (hard, never the single-process fallback) when anything
// whose name starts with the alias prefix, in any case, exists in a search directory: such a
// file or directory could be resolved instead of the root's copy, and the real root would
// escape the kernel replay.
func refuseAliasShadow(dirs []string) error {
	for _, d := range dirs {
		ents, err := os.ReadDir(d)
		if err != nil {
			continue
		}
		for _, e := range ents {
			if strings.HasPrefix(strings.ToLower(e.Name()), strings.ToLower(rootAliasPrefix)) {
				return fmt.Errorf("replay plan: %s exists in %s and could shadow the root replay", e.Name(), d)
			}
		}
	}
	return nil
}

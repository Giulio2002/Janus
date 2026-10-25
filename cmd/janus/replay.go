package main

// Framework olean pinning and the kernel replay of a theorem's whole import closure. See
// docs/AUDIT.md (finding R1) and docs/SOUNDNESS.md (Trusted computing base).
//
// A compiled module (.olean) is only data, but it is the data every later step believes: the
// audit reads the statement's constants from it, and the kernel replay (leanchecker) checks a
// module's declarations against its imports *as loaded from their oleans*. Two defences make
// that safe when an untrusted step (the proof compile, a consumer's lakefile, a dependency's
// build) could reach a build directory:
//
//   - pins: the SHA-256 of every module-data file of the trusted framework build (and of the
//     trusted Extracted/JanusTrusted) is recorded right after the trusted build and re-verified
//     after every untrusted step, after the audit and after the replay. A replaced, corrupted,
//     missing or extra framework olean is rejected (`framework integrity`). Untrusted build
//     outputs (consumer and dependency modules, the proof) are pinned after the last step that
//     can write them, so the replay checks exactly the bytes the audit read.
//   - replay: every module of the theorem's import closure outside the Lean toolchain core
//     (Init, Std, Lean, Lake) is kernel-replayed: each Janus.* framework module, Extracted,
//     JanusTrusted, every dependency and every consumer module. Replay results are cached in the
//     trusted cache (never writable by a sandboxed process), keyed by the SHA-256 of the
//     module's data files and, recursively, the keys of its imports, so an unchanged framework
//     module is not replayed again while any change to it or below it is.

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
)

// coreRoots are the module roots shipped with the Lean toolchain: trusted, never replayed.
var coreRoots = map[string]bool{"Init": true, "Std": true, "Lean": true, "Lake": true}

func isCoreModule(m string) bool { return coreRoots[moduleRoot(m)] }

// moduleDataExts are the files Lean loads when importing a module (the olean and, for module
// system files, its server and private parts) plus its IR. They are what pins cover; Lake's
// .trace/.hash/.ilean bookkeeping is not loaded by Lean and is not pinned.
var moduleDataExts = []string{".olean", ".olean.server", ".olean.private", ".ir"}

func isModuleData(name string) bool {
	for _, e := range moduleDataExts {
		if strings.HasSuffix(name, e) {
			return true
		}
	}
	return false
}

// moduleRel is the slash path of a module's olean relative to a library dir.
func moduleRel(m string) string { return strings.ReplaceAll(m, ".", "/") + ".olean" }

// moduleOfRel is the module a library-relative module-data path belongs to.
func moduleOfRel(rel string) string {
	for _, e := range moduleDataExts {
		if strings.HasSuffix(rel, e) {
			return strings.ReplaceAll(strings.TrimSuffix(rel, e), "/", ".")
		}
	}
	return ""
}

// pins maps a library-relative slash path of a module-data file to its SHA-256.
type pins map[string]string

// pinLib hashes the module-data files under dir whose module keep accepts (nil: all). The
// files are hashed in parallel (the framework build alone is ~70 MB, re-hashed after every step).
func pinLib(dir string, keep func(mod string) bool) (pins, error) {
	p := pins{}
	var files []string // regular files to hash, as rel paths
	err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			if path == dir && os.IsNotExist(err) {
				return fs.SkipDir
			}
			return err
		}
		if d.IsDir() || !isModuleData(d.Name()) {
			return nil
		}
		rel, _ := filepath.Rel(dir, path)
		rel = filepath.ToSlash(rel)
		if keep != nil && !keep(moduleOfRel(rel)) {
			return nil
		}
		if !d.Type().IsRegular() {
			p[rel] = "not-a-regular-file"
			return nil
		}
		files = append(files, rel)
		return nil
	})
	if err != nil {
		return p, err
	}
	sums := make([]string, len(files))
	errs := make([]error, len(files))
	workers := runtime.NumCPU()
	if workers > 16 {
		workers = 16
	}
	var wg sync.WaitGroup
	next := make(chan int)
	for w := 0; w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for i := range next {
				b, err := os.ReadFile(filepath.Join(dir, filepath.FromSlash(files[i])))
				if err != nil {
					errs[i] = err
					continue
				}
				sums[i] = sha256Hex(b)
			}
		}()
	}
	for i := range files {
		next <- i
	}
	close(next)
	wg.Wait()
	for i, rel := range files {
		if errs[i] != nil {
			return p, errs[i]
		}
		p[rel] = sums[i]
	}
	return p, nil
}

// pinnedLib is a library directory with the pins its module-data files must match.
type pinnedLib struct {
	who  string // "the Janus framework build", …
	dir  string
	keep func(mod string) bool // which modules of dir the pins cover (nil: all)
	want pins
}

func newPinnedLib(who, dir string, keep func(string) bool) (*pinnedLib, error) {
	p, err := pinLib(dir, keep)
	if err != nil {
		return nil, err
	}
	return &pinnedLib{who: who, dir: dir, keep: keep, want: p}, nil
}

// diff describes how dir differs from the pins (empty when it matches).
func (l *pinnedLib) diff() []string {
	got, err := pinLib(l.dir, l.keep)
	if err != nil {
		return []string{"cannot read " + displayPath(l.dir) + ": " + err.Error()}
	}
	return diffPins(l.want, got)
}

func diffPins(want, got pins) []string {
	var problems []string
	for rel, h := range want {
		g, ok := got[rel]
		switch {
		case !ok:
			problems = append(problems, "missing "+rel)
		case g != h:
			problems = append(problems, fmt.Sprintf("modified %s (pinned SHA-256 %s, now %s)", rel, short(h), short(g)))
		}
	}
	for rel := range got {
		if _, ok := want[rel]; !ok {
			problems = append(problems, "unexpected "+rel)
		}
	}
	sort.Strings(problems)
	return problems
}

func short(h string) string {
	if len(h) > 16 {
		return h[:16] + "…"
	}
	return h
}

// pinSet is every pinned library of one verification.
type pinSet []*pinnedLib

// check re-verifies every pin; stage names the step that just ran.
func (ps pinSet) check(stage string) error {
	for _, l := range ps {
		if problems := l.diff(); len(problems) > 0 {
			shown := problems
			if len(shown) > 8 {
				shown = append(append([]string{}, shown[:8]...), fmt.Sprintf("… and %d more", len(problems)-8))
			}
			return &diag{Invalid: true, Stage: "framework integrity",
				Msg: fmt.Sprintf("%s (%s) changed after %s; its compiled modules no longer match the pinned SHA-256 hashes:\n  %s",
					l.who, displayPath(l.dir), stage, strings.Join(shown, "\n  ")),
				Next: "A build step (a lakefile, a dependency's build or the proof) wrote compiled modules it does not own. Remove that code; janus rebuilds the trusted framework on the next run."}
		}
	}
	return nil
}

// frameworkPins pins the module-data files of a trusted framework library build that belong to
// framework modules: Janus.* modules with a source file in the framework (files). A stray
// Janus.* olean without a framework source is not pinned, so it can never pass as framework.
func frameworkPins(janusLib string, files map[string][]byte) (*pinnedLib, error) {
	return newPinnedLib("the Janus framework build", janusLib, func(m string) bool {
		_, ok := files[strings.ReplaceAll(m, ".", "/")+".lean"]
		return moduleRoot(m) == "Janus" && ok
	})
}

// samePins reports whether a library's framework modules equal the trusted base's.
func samePins(base *pinnedLib, dir string) bool {
	got, err := pinLib(dir, base.keep)
	return err == nil && len(diffPins(base.want, got)) == 0
}

// closureCheck resolves every module of the audited environment on the search path (first
// directory wins, as Lean does) and enforces where each may come from: core modules from the
// toolchain library, Janus.* modules from the pinned framework build (and only modules the
// framework has), Extracted/JanusTrusted from their trusted home. It returns the non-core
// modules (the replay set) with their resolved olean paths.
func closureCheck(mods []string, searchDirs []string, toolchainLib string, framework *pinnedLib, homes map[string]string) (map[string]string, error) {
	bad := func(msg string) error {
		return &diag{Invalid: true, Stage: "framework integrity", Msg: msg,
			Next: "Only the trusted framework build may provide Janus.* modules and only the toolchain Init/Std/Lean/Lake; remove the injected module."}
	}
	resolved := map[string]string{}
	for _, m := range mods {
		rel := filepath.FromSlash(moduleRel(m))
		dir := ""
		for _, d := range searchDirs {
			if _, err := os.Stat(filepath.Join(d, rel)); err == nil {
				dir = d
				break
			}
		}
		if dir == "" {
			return nil, bad(fmt.Sprintf("the audited environment imports %s, which is not on the search path.", m))
		}
		switch {
		case isCoreModule(m):
			if dir != toolchainLib {
				return nil, bad(fmt.Sprintf("the toolchain module %s is shadowed by %s.", m, displayPath(filepath.Join(dir, rel))))
			}
			continue
		case moduleRoot(m) == "Janus":
			if dir != framework.dir {
				return nil, bad(fmt.Sprintf("the framework module %s is provided by %s, not by the trusted framework build.", m, displayPath(filepath.Join(dir, rel))))
			}
			if _, ok := framework.want[moduleRel(m)]; !ok {
				return nil, bad(fmt.Sprintf("the theorem's environment imports %s, which is not a module of the Janus framework (an injected framework-namespace module).", m))
			}
		}
		if home, ok := homes[m]; ok && dir != home {
			return nil, bad(fmt.Sprintf("%s is provided by %s, not by its trusted home %s.", m, displayPath(filepath.Join(dir, rel)), displayPath(home)))
		}
		resolved[m] = filepath.Join(dir, rel)
	}
	return resolved, nil
}

// replayPlan is the kernel replay of a closure: which modules to replay and which are cached.
type replayPlan struct {
	modules []string          // every non-core module, sorted
	keys    map[string]string // module -> cache key
	todo    []string          // modules with no cached passing replay
	cached  []string
	cacheOn bool
	done    map[string]bool // replayed and passed in this run
}

// replayCacheDir holds one empty marker per passing replay, named by its key. It lives in the
// cache, which sandboxed processes see read-only.
func replayCacheDir() string { return filepath.Join(cacheRoot(), "v1", "replay") }

// planReplay computes the cache keys of the non-core modules in resolved (module -> olean
// path), given the import graph from the audit (module -> direct imports), and splits them into
// cached and to-replay. A module's key covers the toolchain version, the module name, the bytes
// of every module-data file Lean loads for it and, recursively, the keys of its imports, so a
// cached result is reused only if nothing it was checked against changed.
func planReplay(resolved map[string]string, graph map[string][]string, toolchainVersion string, useCache bool) (*replayPlan, error) {
	p := &replayPlan{keys: map[string]string{}, cacheOn: useCache}
	for m := range resolved {
		p.modules = append(p.modules, m)
	}
	sort.Strings(p.modules)
	visiting := map[string]bool{}
	var key func(m string) (string, error)
	key = func(m string) (string, error) {
		if k, ok := p.keys[m]; ok {
			return k, nil
		}
		olean, ok := resolved[m]
		if !ok {
			return "", fmt.Errorf("the import graph names %s, which is not in the audited environment", m)
		}
		if visiting[m] {
			return "", fmt.Errorf("import cycle at %s", m)
		}
		visiting[m] = true
		h := sha256.New()
		fmt.Fprintf(h, "janus-replay-v1\n%s\n%s\n", toolchainVersion, m)
		for _, ext := range []string{"", ".server", ".private"} {
			f := olean + ext
			if b, err := os.ReadFile(f); err == nil {
				fmt.Fprintf(h, "part %q %s\n", ext, sha256Hex(b))
			} else if ext == "" {
				return "", err
			}
		}
		imps, ok := graph[m]
		if !ok {
			return "", fmt.Errorf("the audit reported no imports for %s", m)
		}
		for _, i := range imps {
			if isCoreModule(i) {
				fmt.Fprintf(h, "core %s\n", i)
				continue
			}
			k, err := key(i)
			if err != nil {
				return "", err
			}
			fmt.Fprintf(h, "import %s %s\n", i, k)
		}
		k := hex.EncodeToString(h.Sum(nil))
		p.keys[m] = k
		return k, nil
	}
	for _, m := range p.modules {
		if _, err := key(m); err != nil {
			return nil, &diag{Invalid: true, Stage: "kernel replay", Msg: "Cannot plan the kernel replay: " + err.Error()}
		}
	}
	for _, m := range p.modules {
		if useCache {
			if mk := filepath.Join(replayCacheDir(), p.keys[m][:2], p.keys[m]); fileExists(mk) {
				touchHit(mk)
				p.cached = append(p.cached, m)
				continue
			}
		}
		p.todo = append(p.todo, m)
	}
	return p, nil
}

// record stores a passing replay of mods.
func (p *replayPlan) record(mods []string) {
	if !p.cacheOn {
		return
	}
	for _, m := range mods {
		k := p.keys[m]
		d := filepath.Join(replayCacheDir(), k[:2])
		if os.MkdirAll(d, 0o755) == nil {
			_ = os.WriteFile(filepath.Join(d, k), []byte(m+"\n"), 0o644)
		}
	}
}

// importGraph turns the audit's [module, imports…] rows into a map.
func importGraph(rows [][]string) map[string][]string {
	g := map[string][]string{}
	for _, r := range rows {
		if len(r) > 0 {
			g[r[0]] = r[1:]
		}
	}
	return g
}

// replayParallel bounds how many leanchecker processes one replay runs at once. Each process
// replays one target (a module and its name-prefix descendants): leanchecker imports a separate
// environment per target, and inside one process every import after the first copies the
// already-mapped .olean files instead of mapping them, so one process per target is faster and
// holds one environment at a time. A large closure (a Mathlib import) is still one process per
// root, as before. At most two run at once (memory: each holds up to LEAN_NUM_THREADS environments).
func replayParallel() int {
	n := runtime.NumCPU()
	if n > 2 {
		n = 2
	}
	return n
}

// pending is the subset of mods without a cached (or already recorded) passing replay.
func (p *replayPlan) pending(mods []string) []string {
	var out []string
	for _, m := range mods {
		if p.passed(m) {
			continue
		}
		out = append(out, m)
	}
	return out
}

func (p *replayPlan) passed(m string) bool {
	for _, c := range p.cached {
		if c == m {
			return true
		}
	}
	return p.done[m]
}

// isNamePrefix: a is a proper name-component prefix of m (Janus of Janus.GoABI).
func isNamePrefix(a, m string) bool { return strings.HasPrefix(m, a+".") }

// replayTargets groups modules for leanchecker, whose (non --fresh) targets are name prefixes:
// `leanchecker Janus` replays Janus and every Janus.* module on the search path. Passing a
// module whose ancestor is also being replayed would only make leanchecker scan the search
// path once more (the scan per target dominates a cached run's cost), so each group is led by a
// module none of whose ancestors is in mods, and lists the modules it covers. leanchecker also
// replays any other descendant it finds on the search path; that only adds checking.
func replayTargets(mods []string) (targets []string, covers map[string][]string) {
	sorted := append([]string{}, mods...)
	sort.Strings(sorted)
	covers = map[string][]string{}
	for _, m := range sorted {
		lead := ""
		for _, t := range targets {
			if isNamePrefix(t, m) {
				lead = t
				break
			}
		}
		if lead == "" {
			targets = append(targets, m)
			lead = m
		}
		covers[lead] = append(covers[lead], m)
	}
	return targets, covers
}

// replay kernel-replays mods (those not yet passed) with leanchecker through run (the sandboxed
// runner with the verification's LEAN_PATH): one process per replay target (replayTargets),
// at most replayParallel at once. Each target's replay holds a lock in the replay cache, so
// concurrent verifications replaying the same modules (a fresh framework build) replay them
// once; a target whose modules all became cached while waiting is not replayed again. Passing
// targets are recorded in the replay cache. It returns leanchecker's output on the first failure
// (in target order).
func (p *replayPlan) replay(checker string, run func(argv ...string) (string, error), mods []string) (string, error) {
	targets, covers := replayTargets(p.pending(mods))
	if len(targets) == 0 {
		return "", nil
	}
	outs := make([]string, len(targets))
	errs := make([]error, len(targets))
	sem := make(chan struct{}, replayParallel())
	var wg sync.WaitGroup
	var mu sync.Mutex
	for i, t := range targets {
		wg.Add(1)
		go func(i int, t string) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()
			covered := covers[t]
			unlock := p.lockTarget(covered)
			defer unlock()
			if p.allCachedNow(covered) {
				mu.Lock()
				p.cached = append(p.cached, covered...)
				mu.Unlock()
				return
			}
			if out, err := run(checker, t); err != nil {
				outs[i], errs[i] = out, err
				return
			}
			mu.Lock()
			if p.done == nil {
				p.done = map[string]bool{}
			}
			for _, m := range covered {
				p.done[m] = true
			}
			mu.Unlock()
			p.record(covered)
		}(i, t)
	}
	wg.Wait()
	sort.Strings(p.cached)
	for i := range targets {
		if errs[i] != nil {
			return outs[i], errs[i]
		}
	}
	return "", nil
}

// lockTarget takes an exclusive lock named by the cache keys of mods (with the cache on), so
// only one janus process replays a given set of module bytes at a time. It returns the unlock.
func (p *replayPlan) lockTarget(mods []string) func() {
	if !p.cacheOn {
		return func() {}
	}
	h := sha256.New()
	for _, m := range mods {
		fmt.Fprintf(h, "%s %s\n", m, p.keys[m])
	}
	k := hex.EncodeToString(h.Sum(nil))
	d := filepath.Join(replayCacheDir(), "locks")
	if os.MkdirAll(d, 0o755) != nil {
		return func() {}
	}
	lk, err := lockFile(filepath.Join(d, k[:32]+".lock"), true)
	if err != nil {
		return func() {}
	}
	return lk.unlock
}

// allCachedNow reports whether every module of mods has a passing replay in the cache now
// (recorded by another janus process while this one waited for the target's lock).
func (p *replayPlan) allCachedNow(mods []string) bool {
	if !p.cacheOn || len(mods) == 0 {
		return false
	}
	for _, m := range mods {
		k := p.keys[m]
		if _, err := os.Stat(filepath.Join(replayCacheDir(), k[:2], k)); err != nil {
			return false
		}
	}
	return true
}

// replayFresh additionally replays module m with `leanchecker --fresh`: every constant of its
// environment, Lean core included, re-added to an empty environment. Cached under m's key.
func (p *replayPlan) replayFresh(checker string, run func(argv ...string) (string, error), m string) (string, error) {
	k := "fresh-" + p.keys[m]
	marker := filepath.Join(replayCacheDir(), k[6:8], k)
	if p.cacheOn {
		if fileExists(marker) {
			touchHit(marker)
			return "", nil
		}
	}
	if out, err := run(checker, "--fresh", m); err != nil {
		return out, err
	}
	if p.cacheOn && os.MkdirAll(filepath.Dir(marker), 0o755) == nil {
		_ = os.WriteFile(marker, []byte(m+" --fresh\n"), 0o644)
	}
	return "", nil
}

// report is the kernelReplay record for the modules mods of this plan.
func (p *replayPlan) report(mods []string, fresh string) kernelReplay {
	kr := kernelReplay{Tool: "leanchecker", Status: "passed", Modules: append([]string{}, mods...), Fresh: fresh}
	for _, m := range mods {
		for _, c := range p.cached {
			if c == m {
				kr.Cached = append(kr.Cached, m)
			}
		}
	}
	return kr
}

// replayCacheOK: the replay cache is used unless --fresh, and never without a sandbox (an
// unconfined proof could write cache entries).
func replayCacheOK(sb *sandbox, opts map[string]string) bool {
	return sb.mode != "none" && opts["fresh"] == ""
}

func replayDiag(out string) error {
	return &diag{Invalid: true, Msg: "Kernel replay rejected the environment:\n  " + strings.ReplaceAll(strings.TrimSpace(out), "\n", "\n  "),
		Stage: "kernel replay", Next: "A module manipulates the environment (e.g. debug.skipKernelTC or addDecl without checking) or a compiled module is corrupt; remove that."}
}

// replaySummary is the printed kernel replay line: module count, list, cache reuse, fresh.
func replaySummary(kr kernelReplay) string {
	s := fmt.Sprintf("%d modules: %s", len(kr.Modules), moduleList(kr.Modules))
	if len(kr.Modules) > 12 {
		s = moduleList(kr.Modules)
	}
	if n := len(kr.Cached); n > 0 {
		s += fmt.Sprintf("; %d reused from the replay cache", n)
	}
	if kr.Fresh != "" {
		s += "; " + kr.Fresh + " also replayed with --fresh"
	}
	return s
}

func sortedKeys(m map[string]string) []string {
	var out []string
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

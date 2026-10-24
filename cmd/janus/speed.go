package main

// Verification speed-ups that leave every check in place (docs/TESTING.md):
//
//   - the trusted compile of Extracted and JanusTrusted runs both compiles at once, and its
//     result is cached in the trusted cache keyed by everything the compile reads (the toolchain,
//     the pinned framework build and the two sources), so re-verifying the same extraction (a
//     second theorem, another proof, the test suite) reuses the compiled modules instead of
//     elaborating the program twice again;
//   - the kernel replay of the three per-verification modules (Extracted, JanusTrusted, Proof)
//     starts as soon as Proof.olean is pinned and runs alongside the audit, and the replay of the
//     framework (target Janus), when it is not cached, starts as soon as the framework build is
//     pinned and runs alongside the trusted compile, the proof compile and the audit. Their
//     results count only for modules the audit's closure then contains, with the same cache
//     keys, and the pins are re-checked after them as before.
//
// Like the replay cache, the trusted-compile cache lives in the cache that sandboxed processes
// see read-only, and is used only with a sandbox and without --fresh.

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"sync"
)

// pinsDigest is one SHA-256 over a set of pins (sorted "rel sha" lines).
func pinsDigest(p pins) string {
	keys := make([]string, 0, len(p))
	for k := range p {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	h := sha256.New()
	for _, k := range keys {
		fmt.Fprintf(h, "%s %s\n", k, p[k])
	}
	return hex.EncodeToString(h.Sum(nil))
}

// trustedCacheDir holds compiled Extracted/JanusTrusted modules by key.
func trustedCacheDir() string { return filepath.Join(cacheRoot(), "v1", "trusted") }

// trustedCacheKey covers every input of the trusted compile: the Lean toolchain (version and
// binary), the framework build's module data (its pins) and the bytes of both sources.
func trustedCacheKey(tc *toolchain, fw *pinnedLib, extracted, janusTrusted []byte) string {
	h := sha256.New()
	fmt.Fprintf(h, "janus-trusted-compile-v1\n%s\n%s\n", tc.cacheID(), tc.lean)
	fmt.Fprintf(h, "framework %s\n", pinsDigest(fw.want))
	fmt.Fprintf(h, "Extracted.lean %s\nJanusTrusted.lean %s\n", sha256Hex(extracted), sha256Hex(janusTrusted))
	return hex.EncodeToString(h.Sum(nil))
}

type trustedManifest struct {
	Key   string `json:"key"`
	Files pins   `json:"files"` // module-data files of the compile, with their SHA-256
	// MAC is HMAC-SHA256 of the key and the files under the result cache's key (round 8 M1),
	// which no sandboxed process can read: a manifest written by anything but janus is ignored.
	MAC string `json:"mac"`
}

// trustedMAC authenticates a trusted-compile manifest (key and file pins) under hk.
func trustedMAC(hk []byte, key string, files pins) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-trusted-compile-entry-v1\n%s\n%s\n", key, pinsDigest(files))
	return hex.EncodeToString(m.Sum(nil))
}

// readTrustedManifest reads the manifest of the entry directory for key and reports whether it is
// authentic: written by janus (its MAC verifies under the result cache's key), for this key, and
// non-empty. A manifest with no MAC or a wrong one (planted, or recorded before round 8) is not.
func readTrustedManifest(entry, key string) (trustedManifest, bool) {
	var m trustedManifest
	b, err := readPrivateFile(filepath.Join(entry, "manifest.json"), false)
	if err != nil {
		return m, false
	}
	if json.Unmarshal(b, &m) != nil || m.Key != key || len(m.Files) == 0 || m.MAC == "" {
		return m, false
	}
	hk, err := resultHMACKey()
	if err != nil || !hmac.Equal([]byte(m.MAC), []byte(trustedMAC(hk, key, m.Files))) {
		return m, false
	}
	return m, true
}

// loadTrustedCache copies a cached trusted compile into dir (which holds only the two
// sources). It reports whether it did; any missing or mismatching file is a miss, and the
// partial copy is removed.
func loadTrustedCache(key, dir string) bool {
	entry := filepath.Join(trustedCacheDir(), key[:2], key)
	m, ok := readTrustedManifest(entry, key)
	if !ok {
		return false
	}
	var copied []string
	undo := func() bool {
		for _, p := range copied {
			_ = os.Remove(p)
		}
		return false
	}
	for rel, want := range m.Files {
		if filepath.Base(rel) != rel || !isModuleData(rel) {
			return undo()
		}
		data, err := readPrivateFile(filepath.Join(entry, rel), false)
		if err != nil || sha256Hex(data) != want {
			return undo()
		}
		dst := filepath.Join(dir, rel)
		if err := os.WriteFile(dst, data, 0o644); err != nil {
			return undo()
		}
		copied = append(copied, dst)
	}
	return true
}

// storeTrustedCache records the module-data files of a trusted compile in dir under key
// (atomically: a complete entry or none).
func storeTrustedCache(key, dir string, files pins) {
	parent := filepath.Join(trustedCacheDir(), key[:2])
	final := filepath.Join(parent, key)
	if _, err := os.Lstat(final); err == nil {
		if _, ok := readTrustedManifest(final, key); ok {
			return
		}
		// An entry that is not authentic would otherwise make this key miss forever: move it
		// aside (atomically, so a concurrent reader sees it whole or not at all) and replace it.
		if old, err := os.MkdirTemp(parent, ".stale-"); err == nil {
			if os.Rename(final, filepath.Join(old, "entry")) != nil {
				os.Remove(old)
				return
			}
			os.RemoveAll(old)
		} else {
			return
		}
	}
	if os.MkdirAll(parent, 0o755) != nil {
		return
	}
	tmp, err := os.MkdirTemp(parent, ".tmp-")
	if err != nil {
		return
	}
	for rel := range files {
		data, err := os.ReadFile(filepath.Join(dir, rel))
		if err != nil || sha256Hex(data) != files[rel] || os.WriteFile(filepath.Join(tmp, rel), data, 0o644) != nil {
			os.RemoveAll(tmp)
			return
		}
	}
	hk, err := resultHMACKey()
	if err != nil {
		os.RemoveAll(tmp)
		return
	}
	b, _ := json.Marshal(trustedManifest{Key: key, Files: files, MAC: trustedMAC(hk, key, files)})
	if os.WriteFile(filepath.Join(tmp, "manifest.json"), b, 0o644) != nil || os.Rename(tmp, final) != nil {
		os.RemoveAll(tmp)
	}
}

// compileBoth runs compile on each module concurrently and returns the outputs and errors in
// order. The two trusted compiles are independent (JanusTrusted is a renamed copy that imports
// only Janus).
func compileBoth(compile func(mod string) (string, error), mods ...string) ([]string, []error) {
	outs := make([]string, len(mods))
	errs := make([]error, len(mods))
	var wg sync.WaitGroup
	for i, m := range mods {
		wg.Add(1)
		go func(i int, m string) {
			defer wg.Done()
			outs[i], errs[i] = compile(m)
		}(i, m)
	}
	wg.Wait()
	return outs, errs
}

// earlyReplay is the kernel replay of the per-verification modules, started before the audit.
type earlyReplay struct {
	mods []string
	wg   sync.WaitGroup
	err  error
	out  string
	ran  bool
}

// earlyReplayMarker names a passing early replay of exactly these module bytes (the trusted and
// proof pins), the framework build and toolchain, so a re-verification of the same proof does
// not start it again (the main replay then finds every module in the replay cache).
func earlyReplayMarker(tcVersion string, libs ...*pinnedLib) string {
	h := sha256.New()
	fmt.Fprintf(h, "janus-early-replay-v1\n%s\n", tcVersion)
	for _, l := range libs {
		fmt.Fprintf(h, "%s %s\n", l.who, pinsDigest(l.want))
	}
	k := hex.EncodeToString(h.Sum(nil))
	return filepath.Join(replayCacheDir(), "early", k[:2], k)
}

// startEarlyReplay runs `leanchecker m` for each of mods (one process each, at once, as the
// main replay does for its targets) through run in the background, unless marker exists (with
// the cache on).
func startEarlyReplay(checker string, run func(argv ...string) (string, error), mods []string, marker string, cacheOn bool) *earlyReplay {
	e := &earlyReplay{mods: mods}
	if cacheOn {
		if _, err := os.Stat(marker); err == nil {
			return e
		}
	}
	e.ran = true
	var mu sync.Mutex
	for _, m := range mods {
		e.wg.Add(1)
		go func(m string) {
			defer e.wg.Done()
			out, err := run(checker, m)
			if err != nil {
				mu.Lock()
				if e.err == nil {
					e.out, e.err = out, err
				}
				mu.Unlock()
			}
		}(m)
	}
	return e
}

func (e *earlyReplay) wait() {
	if e != nil {
		e.wg.Wait()
	}
}

// apply marks the early-replayed modules that the plan replays as passed in this run (only if
// the early replay passed; on failure the plan replays them itself and reports the failure).
func (e *earlyReplay) apply(p *replayPlan, marker string) {
	if e == nil || !e.ran {
		return
	}
	e.wait()
	if e.err != nil {
		return
	}
	// leanchecker's targets are name prefixes: target t replays t and every t.* module on its
	// search path, so it covers exactly those modules of the plan.
	var covered []string
	for _, m := range p.modules {
		if p.passed(m) {
			continue
		}
		for _, t := range e.mods {
			if m == t || isNamePrefix(t, m) {
				covered = append(covered, m)
				break
			}
		}
	}
	if p.done == nil {
		p.done = map[string]bool{}
	}
	for _, m := range covered {
		p.done[m] = true
	}
	p.record(covered)
	if p.cacheOn && os.MkdirAll(filepath.Dir(marker), 0o755) == nil {
		_ = os.WriteFile(marker, []byte("early replay passed\n"), 0o644)
	}
}

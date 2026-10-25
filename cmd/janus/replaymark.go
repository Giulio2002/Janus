package main

// Authenticated replay markers and the framework replay verdict (docs/SOUNDNESS.md "What the
// kernel replay covers", "The framework replay verdict").
//
// A replay marker (v1/replay/...) says "leanchecker passed on exactly these bytes"; its name is
// the cache key of what was replayed. Until now a marker was any file with that name, so anything
// that could create a file in the replay directory could make an unreplayed module count as
// replayed. Every marker now holds an HMAC-SHA256 of its kind and key under the cache's hidden
// key (the result cache's key, v1/result/.key, round 8 M1), which no sandboxed process can read:
// a marker janus did not write (planted, copied from another cache, or written before this change)
// is a miss, and the replay runs.
//
// The framework replay verdict is one such marker for the whole framework build: the kernel
// replay `leanchecker Janus` of every framework module passed, for the toolchain (cacheID: the
// version, the lean and leanchecker binaries and the toolchain library) and the SHA-256 of every
// framework module-data file (the framework pins). The verdict depends only on those, so it is
// looked up once per verification, before any untrusted step runs, and the framework is replayed
// at most once per (toolchain, framework build bytes) per cache; concurrent verifications of a
// framework build that has no verdict yet take a lock and replay it once.

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
)

// markerMAC authenticates a replay marker of kind for key under hk.
func markerMAC(hk []byte, kind, key string) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-replay-marker-v2\n%s\n%s\n", kind, key)
	return hex.EncodeToString(m.Sum(nil))
}

const markerHeader = "janus-replay-marker-v2 "

// markerOK reports whether the marker file at path is an authentic marker of kind for key: a
// regular file of this user (not a link), whose first line carries the MAC janus wrote. A missing,
// planted, foreign or unauthenticated marker is not.
func markerOK(path, kind, key string) bool {
	b, err := readPrivateFile(path, false)
	if err != nil {
		return false
	}
	line, _, _ := bytes.Cut(b, []byte("\n"))
	if !bytes.HasPrefix(line, []byte(markerHeader)) {
		return false
	}
	hk, err := resultHMACKey()
	if err != nil {
		return false
	}
	return hmac.Equal(bytes.TrimPrefix(line, []byte(markerHeader)), []byte(markerMAC(hk, kind, key)))
}

// writeMarker records an authentic marker of kind for key at path (atomically), with a note
// for humans on its second line. Without a usable cache key nothing is written (a miss later).
func writeMarker(path, kind, key, note string) {
	hk, err := resultHMACKey()
	if err != nil {
		return
	}
	if os.MkdirAll(filepath.Dir(path), 0o755) != nil {
		return
	}
	_ = writeFileAtomic(path, []byte(markerHeader+markerMAC(hk, kind, key)+"\n"+strings.ReplaceAll(note, "\n", " ")+"\n"))
}

// moduleMarkerPath is the marker of a passing replay of the module with replay key k.
func moduleMarkerPath(k string) string { return filepath.Join(replayCacheDir(), k[:2], k) }

// frameworkVerdictKey names the framework replay verdict: the toolchain and every framework
// module-data file's SHA-256 (the pins taken right after the trusted build, re-checked after every
// later step). Any change to a framework module, to the set of modules or to the toolchain is
// another key.
func frameworkVerdictKey(tcID string, fw *pinnedLib) string {
	h := sha256.New()
	fmt.Fprintf(h, "janus-framework-replay-v1\n%s\n%s\n", tcID, pinsDigest(fw.want))
	return hex.EncodeToString(h.Sum(nil))
}

func frameworkVerdictPath(k string) string {
	return filepath.Join(replayCacheDir(), "framework", k[:2], k)
}

// frameworkModules are the modules the framework pins cover (sorted).
func frameworkModules(fw *pinnedLib) []string {
	seen := map[string]bool{}
	var mods []string
	for rel := range fw.want {
		if m := moduleOfRel(rel); m != "" && !seen[m] {
			seen[m] = true
			mods = append(mods, m)
		}
	}
	sort.Strings(mods)
	return mods
}

// hasFrameworkVerdict reports whether an authentic passing verdict exists for k.
func hasFrameworkVerdict(k string) bool {
	p := frameworkVerdictPath(k)
	if markerOK(p, "framework", k) {
		touchHit(p)
		return true
	}
	return false
}

// recordFrameworkVerdict stores the verdict for k after `leanchecker Janus` passed on the
// pinned framework build fw.
func recordFrameworkVerdict(k string, fw *pinnedLib) {
	writeMarker(frameworkVerdictPath(k), "framework", k,
		fmt.Sprintf("leanchecker Janus passed: %d framework modules", len(frameworkModules(fw))))
}

// applyFrameworkVerdict marks the framework modules of the plan as replayed by the verdict
// (reported as reused from the replay cache). Only Janus.* modules that the framework pins cover
// qualify; closureCheck has already required each of them to resolve from the pinned framework
// build, whose pins are checked again after the replay.
func (p *replayPlan) applyFrameworkVerdict(fw *pinnedLib) {
	for _, m := range p.modules {
		if moduleRoot(m) != "Janus" || p.passed(m) {
			continue
		}
		if _, ok := fw.want[moduleRel(m)]; ok {
			p.cached = append(p.cached, m)
		}
	}
	sort.Strings(p.cached)
}

// lockReplayKey takes the exclusive replay lock named by k (with the cache on); it returns the
// unlock.
func lockReplayKey(k string) func() {
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

// The verdict's use lock (<verdict>.use, next to it): every verification that uses the verdict
// holds it shared until it ends, and the cache collector removes a verdict only under this lock,
// taken exclusively without waiting, so a verdict in use is never collected. Recording a verdict is
// serialised by a separate replay lock (v1/replay/locks), held only while `leanchecker Janus`
// runs, so concurrent verifications of a new framework build replay it once and nobody waits for
// another verification to end.
func frameworkVerdictUsePath(k string) string { return frameworkVerdictPath(k) + ".use" }

// useFrameworkVerdict returns the verdict's use lease (shared) if an authentic verdict for k
// exists, else nil. It does not wait for a collection holding the use lock: that is a miss.
func useFrameworkVerdict(k string) *fileLock {
	p := frameworkVerdictUsePath(k)
	if !hasFrameworkVerdict(k) || os.MkdirAll(filepath.Dir(p), 0o755) != nil {
		return nil
	}
	lk, err := lockFileMode(p, true, false)
	if err != nil {
		return nil
	}
	// Collected between the check and the lock: a miss.
	if !hasFrameworkVerdict(k) {
		lk.unlock()
		return nil
	}
	return lk
}

// lookupFrameworkVerdict reports whether an authentic verdict for k exists now, with its use lease.
func lookupFrameworkVerdict(k string) (bool, *fileLock) {
	lk := useFrameworkVerdict(k)
	return lk != nil, lk
}

// fwReplay is the kernel replay of the framework (target Janus) for one verification: nothing
// when the verdict was found up front, else `leanchecker Janus` started before the untrusted
// steps and running alongside them.
type fwReplay struct {
	key    string
	have   bool // an authentic verdict existed before any untrusted step ran
	waited bool // another process recorded the verdict while this one waited for its lock
	ran    bool
	wg     sync.WaitGroup
	err    error
	out    string
	lease  *fileLock
}

// startFrameworkReplay replays the framework through run unless have (lease: the verdict's use
// lease from lookupFrameworkVerdict). With write (a sandboxed run without --fresh) the replay
// holds the framework's replay lock and records the verdict before releasing it, and a
// verification that waited for that lock uses the verdict instead of replaying; with read only (no
// sandbox) a verdict is used but never recorded.
func startFrameworkReplay(checker string, run func(argv ...string) (string, error), key string, fw *pinnedLib, have bool, lease *fileLock, read, write bool) *fwReplay {
	f := &fwReplay{key: key, have: have, lease: lease}
	if have {
		return f
	}
	f.wg.Add(1)
	go func() {
		defer f.wg.Done()
		if write {
			// One replay of this build at a time: a verification that waited finds the verdict.
			unlock := lockReplayKey("framework-" + key)
			defer unlock()
		}
		if read {
			if lk := useFrameworkVerdict(key); lk != nil {
				f.waited, f.lease = true, lk
				return
			}
		}
		f.ran = true
		out, err := run(checker, "Janus")
		if err != nil {
			f.out, f.err = out, err
			return
		}
		if write {
			recordFrameworkVerdict(key, fw)
			f.lease = useFrameworkVerdict(key)
		}
	}()
	return f
}

// release waits for the replay and drops the verdict's lock.
func (f *fwReplay) release() {
	if f != nil {
		f.wg.Wait()
		f.lease.unlock()
	}
}

func (f *fwReplay) wait() {
	if f != nil {
		f.wg.Wait()
	}
}

// apply counts the framework modules of the plan as replayed when the verdict existed, was
// recorded by another process meanwhile, or this replay passed. On a failure nothing is counted:
// the plan replays those modules itself and reports leanchecker's error.
func (f *fwReplay) apply(p *replayPlan, fw *pinnedLib) {
	if f == nil {
		return
	}
	f.wait()
	switch {
	case f.have || f.waited:
		p.applyFrameworkVerdict(fw)
	case f.ran && f.err == nil:
		// `leanchecker Janus` replays Janus and every Janus.* module on its search path.
		var covered []string
		for _, m := range p.modules {
			if p.passed(m) || moduleRoot(m) != "Janus" {
				continue
			}
			if _, ok := fw.want[moduleRel(m)]; ok {
				covered = append(covered, m)
			}
		}
		if p.done == nil {
			p.done = map[string]bool{}
		}
		for _, m := range covered {
			p.done[m] = true
		}
		p.record(covered)
	}
}

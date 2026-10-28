package main

// J1 (verify fixed overhead): the integrity machinery behind the faster pipeline. Every row here
// pins one property that keeps the speed-ups sound: a measured hash is reused only where the same
// measurement is still checked afterwards, a cached intermediate (trusted compile, early-replay
// marker) that is corrupt, forged or for other bytes is a rebuild and never a pass, and the
// toolchain found without Lake is the one Lake finds. The end-to-end rows (false theorem, sorry,
// extra axiom, failed audit, pin mismatch, sandbox escape) are TestVerify, TestForeignFramework-
// WriteDetected and TestHardeningAttacks, which run through this pipeline.

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

// j1StampedFramework lays out a framework build the way a stamped one is: the sources in dir, the
// module data in dir/.lake/build/lib/lean, the auditor in dir/.lake/build/bin and the ready stamp
// next to it. It returns the framework value and the directory.
func j1StampedFramework(t *testing.T) (*framework, string) {
	t.Helper()
	privateCache(t)
	fw := &framework{Source: "embedded", Sha256: strings.Repeat("ab", 32), Toolchain: "leanprover/lean4:vtest",
		Files: map[string][]byte{
			"Janus.lean": []byte("import Janus.A\n"), "Janus/A.lean": []byte("def a := 1\n"),
			"lakefile.toml": []byte("name = \"janus\"\n"), "lake-manifest.json": []byte("{}\n"), "lean-toolchain": []byte("leanprover/lean4:vtest\n"),
		}}
	dir := filepath.Join(t.TempDir(), "base")
	if err := syncTree(dir, fw.Files, func(top string) bool { return top == ".lake" }); err != nil {
		t.Fatal(err)
	}
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	writeBytes(t, filepath.Join(lib, "Janus.olean"), []byte("janus-data"))
	writeBytes(t, filepath.Join(lib, "Janus", "A.olean"), []byte("a-data"))
	exe := auditExePath(dir)
	writeBytes(t, exe, []byte("auditor-exe"))
	p, err := frameworkPins(lib, fw.Files)
	if err != nil || len(p.want) != 2 {
		t.Fatalf("pins: %v %v", p, err)
	}
	st := frameworkStamp{Sha256: fw.Sha256, Manifest: sha256Hex(fw.Files["lake-manifest.json"]), Targets: []string{"Janus"},
		Pins: p.want, AuditExe: regularFileSha(exe)}
	_, stampPath := fw.buildPaths(dir)
	writeStamp(t, stampPath, st)
	return fw, dir
}

func writeStamp(t *testing.T, path string, st frameworkStamp) {
	t.Helper()
	b, err := json.Marshal(st)
	if err != nil {
		t.Fatal(err)
	}
	writeBytes(t, path, b)
}

// The readiness check returns the pins it measured (verify reuses them instead of hashing the
// framework again) and still refuses a build that differs from its stamp in any module, in the
// auditor, or in the sources.
func TestJ1ReadyInfoPinsAndRefusals(t *testing.T) {
	fw, dir := j1StampedFramework(t)
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	rdy, ok := fw.readyInfo(dir, nil)
	if !ok {
		t.Fatal("a stamped build was not ready")
	}
	own, err := frameworkPins(lib, fw.Files)
	if err != nil {
		t.Fatal(err)
	}
	if d := diffPins(own.want, rdy.pins.want); len(d) > 0 {
		t.Fatalf("returned pins differ from a fresh measurement: %v", d)
	}
	if rdy.exeSha != regularFileSha(auditExePath(dir)) || rdy.exeSha == "" {
		t.Fatalf("returned auditor hash %q", rdy.exeSha)
	}
	if !fw.ready(dir, nil) {
		t.Fatal("ready disagrees with readyInfo")
	}
	for _, c := range []struct {
		name   string
		break_ func()
		fix    func()
	}{
		{"module data rewritten", func() { writeBytes(t, filepath.Join(lib, "Janus", "A.olean"), []byte("A-data")) },
			func() { writeBytes(t, filepath.Join(lib, "Janus", "A.olean"), []byte("a-data")) }},
		{"module data removed", func() { os.Remove(filepath.Join(lib, "Janus", "A.olean")) },
			func() { writeBytes(t, filepath.Join(lib, "Janus", "A.olean"), []byte("a-data")) }},
		{"module data added", func() { writeBytes(t, filepath.Join(lib, "Janus", "A.olean.private"), []byte("p")) },
			func() { os.Remove(filepath.Join(lib, "Janus", "A.olean.private")) }},
		{"auditor executable rewritten", func() { writeBytes(t, auditExePath(dir), []byte("evil-exe")) },
			func() { writeBytes(t, auditExePath(dir), []byte("auditor-exe")) }},
		{"auditor executable removed", func() { os.Remove(auditExePath(dir)) },
			func() { writeBytes(t, auditExePath(dir), []byte("auditor-exe")) }},
		{"source edited", func() { writeBytes(t, filepath.Join(dir, "Janus", "A.lean"), []byte("def a := 2\n")) },
			func() { writeBytes(t, filepath.Join(dir, "Janus", "A.lean"), []byte("def a := 1\n")) }},
		{"a source added", func() { writeBytes(t, filepath.Join(dir, "Janus", "B.lean"), []byte("x")) },
			func() { os.Remove(filepath.Join(dir, "Janus", "B.lean")) }},
	} {
		c.break_()
		if _, ok := fw.readyInfo(dir, nil); ok {
			t.Errorf("%s: the build was ready", c.name)
		}
		c.fix()
		if _, ok := fw.readyInfo(dir, nil); !ok {
			t.Errorf("%s: restoring the bytes did not make the build ready again", c.name)
		}
	}
}

// A pin check made against the pins the readiness check returned detects what the check after an
// untrusted step is there for.
func TestJ1ReadyPinsDetectLaterWrite(t *testing.T) {
	fw, dir := j1StampedFramework(t)
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	rdy, ok := fw.readyInfo(dir, nil)
	if !ok {
		t.Fatal("not ready")
	}
	ps := pinSet{rdy.pins}
	if err := ps.check("a step"); err != nil {
		t.Fatalf("unchanged build failed the check: %v", err)
	}
	writeBytes(t, filepath.Join(lib, "Janus.olean"), []byte("forged!!!!"))
	err := ps.check("the proof compile")
	if err == nil || !strings.Contains(err.Error(), "modified Janus.olean") || !strings.Contains(err.Error(), "after the proof compile") {
		t.Fatalf("a write to the framework build was not reported: %v", err)
	}
}

// The trusted-compile entry's manifest hashes pin the files it loads: a file changed after the
// load (or an entry whose data does not match its manifest) never passes.
func TestJ1TrustedCachePinsAreVerifiedHashes(t *testing.T) {
	privateCache(t)
	src := t.TempDir()
	extracted, trusted := []byte("compiled Extracted"), []byte("compiled JanusTrusted")
	writeBytes(t, filepath.Join(src, "Extracted.olean"), extracted)
	writeBytes(t, filepath.Join(src, "JanusTrusted.olean"), trusted)
	files := pins{"Extracted.olean": sha256Hex(extracted), "JanusTrusted.olean": sha256Hex(trusted)}
	key := strings.Repeat("cd", 32)
	storeTrustedCache(key, src, files)
	dst := t.TempDir()
	got, ok := loadTrustedCache(key, dst)
	if !ok || len(diffPins(files, got)) > 0 {
		t.Fatalf("load: %v %v", ok, got)
	}
	lib := &pinnedLib{who: "the trusted build", dir: dst, want: got}
	if d := lib.diff(); len(d) > 0 {
		t.Fatalf("loaded files differ from the returned pins: %v", d)
	}
	writeBytes(t, filepath.Join(dst, "Extracted.olean"), []byte("compiled EXTRACTED"))
	if d := lib.diff(); len(d) != 1 || !strings.Contains(d[0], "modified Extracted.olean") {
		t.Fatalf("a changed loaded file was not detected: %v", d)
	}
	// An entry file that no longer matches its manifest is a miss (the caller recompiles).
	entry := filepath.Join(trustedCacheDir(), key[:2], key)
	writeBytes(t, filepath.Join(entry, "JanusTrusted.olean"), []byte("compiled JANUSTRUSTED"))
	d2 := t.TempDir()
	if p, ok := loadTrustedCache(key, d2); ok || p != nil {
		t.Fatalf("a corrupt entry was used: %v", p)
	}
	for _, f := range []string{"Extracted.olean", "JanusTrusted.olean"} {
		if _, err := os.Stat(filepath.Join(d2, f)); err == nil {
			t.Errorf("%s left behind after a rejected entry", f)
		}
	}
}

// The early-replay markers are per module and per context. A marker is used only if it is
// authentic and for exactly the bytes replayed; a forged, stale or corrupt one means the module
// is replayed, and a failed replay writes no marker.
func TestJ1EarlyReplayMarkers(t *testing.T) {
	privateCache(t)
	if _, err := resultHMACKey(); err != nil {
		t.Fatal(err)
	}
	fw := &pinnedLib{who: "fw", want: pins{"Janus.olean": "11"}}
	tr := &pinnedLib{who: "trusted", want: pins{"Extracted.olean": "22", "JanusTrusted.olean": "33"}}
	pf := &pinnedLib{who: "proof", want: pins{"Proof.olean": "44"}}
	mk := func(fw, tr, pf *pinnedLib) map[string]string {
		return map[string]string{
			"Extracted":    earlyReplayMarker("tc", "Extracted", fw, tr),
			"JanusTrusted": earlyReplayMarker("tc", "JanusTrusted", fw, tr),
			"Proof":        earlyReplayMarker("tc", "Proof", fw, tr, pf),
		}
	}
	mods := []string{"Extracted", "JanusTrusted", "Proof"}
	var mu sync.Mutex
	var ran []string
	fake := func(failOn string) func(argv ...string) (string, error) {
		return func(argv ...string) (string, error) {
			mu.Lock()
			ran = append(ran, argv[len(argv)-1])
			mu.Unlock()
			if argv[len(argv)-1] == failOn {
				return "boom", fmt.Errorf("exit 1")
			}
			return "", nil
		}
	}
	plan := func() *replayPlan {
		p := &replayPlan{modules: mods, keys: map[string]string{}, cacheOn: true}
		for _, m := range mods {
			p.keys[m] = sha256Hex([]byte(m))
		}
		return p
	}
	run := func(markers map[string]string, failOn string) []string {
		ran = nil
		e := startEarlyReplay("leanchecker", fake(failOn), mods, markers, true)
		e.wait()
		e.apply(plan())
		return append([]string{}, ran...)
	}
	m1 := mk(fw, tr, pf)
	if got := run(m1, "Proof"); len(got) != 3 {
		t.Fatalf("first run replayed %v", got)
	}
	// Proof failed: no marker for anything (the plan replays and reports the failure itself).
	for m, p := range m1 {
		if markerOK(p, "early", filepath.Base(p)) {
			t.Errorf("a marker for %s was written after a failed early replay", m)
		}
	}
	if got := run(m1, ""); len(got) != 3 {
		t.Fatalf("second run replayed %v", got)
	}
	// Everything passed: the same context replays nothing.
	if got := run(m1, ""); len(got) != 0 {
		t.Fatalf("an identical context replayed %v", got)
	}
	// A new proof of the same extraction replays only the proof.
	pf2 := &pinnedLib{who: "proof", want: pins{"Proof.olean": "45"}}
	if got := run(mk(fw, tr, pf2), ""); len(got) != 1 || got[0] != "Proof" {
		t.Fatalf("a new proof replayed %v, want only Proof", got)
	}
	// A changed framework build or trusted build replays everything it covers.
	fw2 := &pinnedLib{who: "fw", want: pins{"Janus.olean": "12"}}
	if got := run(mk(fw2, tr, pf), ""); len(got) != 3 {
		t.Fatalf("a changed framework replayed %v", got)
	}
	tr2 := &pinnedLib{who: "trusted", want: pins{"Extracted.olean": "23", "JanusTrusted.olean": "33"}}
	if got := run(mk(fw, tr2, pf), ""); len(got) != 3 {
		t.Fatalf("a changed trusted build replayed %v", got)
	}
	// Another toolchain is another marker.
	if earlyReplayMarker("tc", "Proof", fw, tr, pf) == earlyReplayMarker("tc2", "Proof", fw, tr, pf) {
		t.Fatal("the toolchain is not part of the marker")
	}
	// A planted marker (a file with the right name and no MAC, or someone else's MAC) is ignored.
	for name, body := range map[string]string{"empty": "", "no MAC": "janus-replay-marker-v2 \n", "garbage": "hello\n",
		"wrong MAC": markerHeader + strings.Repeat("0", 64) + "\n"} {
		m2 := mk(fw, tr, &pinnedLib{who: "proof", want: pins{"Proof.olean": "46" + name}})
		writeBytes(t, m2["Proof"], []byte(body))
		got := run(m2, "Proof")
		found := false
		for _, g := range got {
			if g == "Proof" {
				found = true
			}
		}
		if !found {
			t.Errorf("%s: a planted marker made the proof skip its replay", name)
		}
	}
}

// Keys computed from pinned hashes equal the keys computed by reading the files, and a wrong
// pinned hash is another key (so it can never select a cached verdict for other bytes).
func TestJ1PlanReplayPinnedKeys(t *testing.T) {
	privateCache(t)
	lib := t.TempDir()
	writeBytes(t, filepath.Join(lib, "A.olean"), []byte("a"))
	writeBytes(t, filepath.Join(lib, "B.olean"), []byte("b"))
	writeBytes(t, filepath.Join(lib, "B.olean.server"), []byte("s"))
	resolved := map[string]string{"A": filepath.Join(lib, "A.olean"), "B": filepath.Join(lib, "B.olean")}
	graph := map[string][]string{"A": {"Init"}, "B": {"A", "Init.Core"}}
	read, err := planReplay(resolved, graph, "v1", false)
	if err != nil {
		t.Fatal(err)
	}
	pl, err := newPinnedLib("lib", lib, nil)
	if err != nil {
		t.Fatal(err)
	}
	known := pinSet{pl}.absHashes()
	if len(known) != 3 {
		t.Fatalf("pins %v", known)
	}
	viaPins, err := planReplayPinned(resolved, graph, "v1", false, known)
	if err != nil {
		t.Fatal(err)
	}
	for m, k := range read.keys {
		if viaPins.keys[m] != k {
			t.Errorf("key of %s differs between reading and pins", m)
		}
	}
	wrong := map[string]string{}
	for k, v := range known {
		wrong[k] = v
	}
	wrong[filepath.Join(lib, "A.olean")] = sha256Hex([]byte("not a"))
	bad, err := planReplayPinned(resolved, graph, "v1", false, wrong)
	if err != nil {
		t.Fatal(err)
	}
	if bad.keys["A"] == read.keys["A"] || bad.keys["B"] == read.keys["B"] {
		t.Error("a different pinned hash gave the same key")
	}
	// A file that is not pinned is still read.
	partial, err := planReplayPinned(resolved, graph, "v1", false, map[string]string{})
	if err != nil || partial.keys["B"] != read.keys["B"] {
		t.Errorf("unpinned files not read: %v", err)
	}
}

// The streaming hash is the SHA-256 of the bytes, and an unreadable file is an error.
func TestJ1FileSha256(t *testing.T) {
	dir := t.TempDir()
	big := make([]byte, 3<<20+17)
	for i := range big {
		big[i] = byte(i * 7)
	}
	writeBytes(t, filepath.Join(dir, "big"), big)
	writeBytes(t, filepath.Join(dir, "empty"), nil)
	for name, b := range map[string][]byte{"big": big, "empty": nil} {
		got, err := fileSha256Hex(filepath.Join(dir, name))
		if err != nil || got != sha256Hex(b) {
			t.Errorf("%s: %q %v", name, got, err)
		}
	}
	if _, err := fileSha256Hex(filepath.Join(dir, "missing")); err == nil {
		t.Error("a missing file hashed")
	}
	if regularFileSha(dir) != "" {
		t.Error("a directory hashed as a regular file")
	}
}

// The toolchain found without Lake is the one `lake env` finds.
func TestJ1ToolchainDirectMatchesLake(t *testing.T) {
	needLean(t)
	lake, err := findLake()
	if err != nil {
		t.Skip(err)
	}
	direct := findToolchainDirect(lake, repoRoot)
	if direct == nil {
		t.Skip("no direct lookup on this host (the Lake path is used)")
	}
	t.Setenv("JANUS_TOOLCHAIN_VIA_LAKE", "1")
	via, err := findToolchain(lake, repoRoot)
	if err != nil {
		t.Fatal(err)
	}
	if direct.lean != via.lean || direct.leanchecker != via.leanchecker || direct.sysroot != via.sysroot ||
		direct.libDir != via.libDir || direct.version != via.version || direct.hasChecker != via.hasChecker {
		t.Fatalf("direct %+v\nlake   %+v", direct, via)
	}
	t.Setenv("LEAN_SYSROOT", direct.sysroot)
	if findToolchainDirect(lake, repoRoot) != nil {
		t.Error("LEAN_SYSROOT (which Lake honours) did not send the lookup through Lake")
	}
}

// A trusted-compile entry whose data was damaged after it was stored is a miss, and the next
// store replaces it (it does not stay broken forever).
func TestJ1TrustedCacheSelfHeals(t *testing.T) {
	privateCache(t)
	src := t.TempDir()
	data := []byte("compiled Extracted")
	writeBytes(t, filepath.Join(src, "Extracted.olean"), data)
	files := pins{"Extracted.olean": sha256Hex(data)}
	key := strings.Repeat("ef", 32)
	storeTrustedCache(key, src, files)
	entryFile := filepath.Join(trustedCacheDir(), key[:2], key, "Extracted.olean")
	writeBytes(t, entryFile, []byte("compiled EXTRACTED"))
	if _, ok := loadTrustedCache(key, t.TempDir()); ok {
		t.Fatal("a damaged entry was used")
	}
	storeTrustedCache(key, src, files)
	dst := t.TempDir()
	got, ok := loadTrustedCache(key, dst)
	if !ok || len(diffPins(files, got)) > 0 {
		t.Fatal("the entry was not replaced by the next store")
	}
	if b, _ := os.ReadFile(filepath.Join(dst, "Extracted.olean")); string(b) != string(data) {
		t.Fatalf("replaced entry holds %q", b)
	}
}

// fakeAuditor writes a shell script that speaks the `janus-audit --serve` protocol: it announces
// itself in pidFile, waits for one request line on standard input and answers with the marker
// and the request it received; without a request (end of input) it exits with status 3 and prints
// nothing.
func fakeAuditor(t *testing.T, pidFile string) string {
	t.Helper()
	p := filepath.Join(t.TempDir(), "janus-audit")
	script := "#!/bin/sh\n" +
		"echo $$ >> " + shQuote(pidFile) + "\n" +
		"if [ \"$1\" != --serve ]; then echo bad-invocation; exit 2; fi\n" +
		"if IFS= read -r line; then\n" +
		"  marker=$(printf '%s' \"$line\" | cut -f3)\n" +
		"  printf '%s%s\\n' \"$marker\" \"$line\"\n" +
		"else\n  exit 3\nfi\n"
	if err := os.WriteFile(p, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	return p
}

func j1ServeFixture(t *testing.T) (*toolchain, string) {
	t.Helper()
	tc := fakeToolchain(t)
	return tc, t.TempDir()
}

// A prestarted auditor gets its request after it has started, and its output is the answer; the
// request carries the theorem, the proof module, the marker and the final search path.
func TestJ1AuditServeRequest(t *testing.T) {
	tc, scratch := j1ServeFixture(t)
	pids := filepath.Join(scratch, "pids")
	exe := fakeAuditor(t, pids)
	sb := &sandbox{mode: "none"}
	as := startAuditServe(sb, tc, scratch, nil, exe, "JanusTrusted", "/serve/path", "/full/path:/work", []string{"Proof.correctness", "Proof.other"})
	defer as.stop()
	for i, thm := range []string{"Proof.correctness", "Proof.other"} {
		out, err := as.request(i, "marker-"+thm+": ", "/full/path:/work")
		if err != nil || !strings.Contains(out, "marker-"+thm+": "+thm+"\tProof\tmarker-"+thm+": \t/full/path:/work") {
			t.Fatalf("%s: %q %v", thm, out, err)
		}
	}
	// A separator in the request is refused before anything is sent.
	as2 := startAuditServe(sb, tc, scratch, nil, exe, "JanusTrusted", "/serve/path", "/p", []string{"Proof.correctness"})
	defer as2.stop()
	if _, err := as2.request(0, "bad\tmarker", "/p"); err == nil {
		t.Error("a request with a tab was sent")
	}
}

// Cancelling prestarted auditors (the proof did not compile, a pin check failed) ends them: no
// request is made, nothing runs on afterwards, and stop returns.
func TestJ1AuditServeStopEndsAuditors(t *testing.T) {
	tc, scratch := j1ServeFixture(t)
	pids := filepath.Join(scratch, "pids")
	exe := fakeAuditor(t, pids)
	// A slow auditor that would run for a minute if nothing ended it.
	slow := filepath.Join(t.TempDir(), "slow-audit")
	if err := os.WriteFile(slow, []byte("#!/bin/sh\necho $$ >> "+shQuote(pids)+"\nexec sleep 60\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	for _, e := range []string{exe, slow} {
		as := startAuditServe(&sandbox{mode: "none"}, tc, scratch, nil, e, "JanusTrusted", "/s", "/f", []string{"Proof.a", "Proof.b"})
		time.Sleep(300 * time.Millisecond)
		start := time.Now()
		as.stop()
		if d := time.Since(start); d > 10*time.Second {
			t.Errorf("stop took %v", d)
		}
		for _, j := range as.jobs {
			select {
			case <-j.done:
			default:
				t.Error("a job was still running after stop")
			}
		}
	}
	b, _ := os.ReadFile(pids)
	for _, f := range strings.Fields(string(b)) {
		pid, _ := strconv.Atoi(f)
		if pid > 0 && syscall.Kill(pid, 0) == nil {
			// a zombie awaiting reaping is not running; give the kernel a moment
			time.Sleep(200 * time.Millisecond)
			if syscall.Kill(pid, 0) == nil {
				if st, _ := os.ReadFile("/proc/" + f + "/stat"); !strings.Contains(string(st), ") Z ") {
					t.Errorf("auditor process %d still runs after stop", pid)
				}
			}
		}
	}
}

// More theorems than auditServeMax: the later auditors start when earlier ones finish, and every
// request is answered (no deadlock between the bound on running auditors and the requests).
func TestJ1AuditServeMoreThanTheBound(t *testing.T) {
	tc, scratch := j1ServeFixture(t)
	exe := fakeAuditor(t, filepath.Join(scratch, "pids"))
	var thms []string
	for i := 0; i < 3*auditServeMax; i++ {
		thms = append(thms, fmt.Sprintf("Proof.t%d", i))
	}
	as := startAuditServe(&sandbox{mode: "none"}, tc, scratch, nil, exe, "JanusTrusted", "/s", "/f", thms)
	defer as.stop()
	var wg sync.WaitGroup
	// requested in reverse order: a later theorem's request must not wait for an earlier one
	for i := len(thms) - 1; i >= 0; i-- {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			out, err := as.request(i, fmt.Sprintf("m%d: ", i), "/f")
			if err != nil || !strings.Contains(out, thms[i]+"\tProof\t") {
				t.Errorf("%s: %q %v", thms[i], out, err)
			}
		}(i)
	}
	done := make(chan struct{})
	go func() { wg.Wait(); close(done) }()
	select {
	case <-done:
	case <-time.After(60 * time.Second):
		t.Fatal("requests did not complete (deadlock)")
	}
}

// Digests frame their fields: pin sets that differ only by a space or newline inside a path give
// different digests.
func TestJ1DigestFraming(t *testing.T) {
	a := pins{"A B": "c"}
	b := pins{"A": "B c"}
	c := pins{"A\nB": "c"}
	if pinsDigest(a) == pinsDigest(b) || pinsDigest(a) == pinsDigest(c) || pinsDigest(b) == pinsDigest(c) {
		t.Fatal("ambiguous pin digest")
	}
	if earlyReplayMarker("tc", "m", &pinnedLib{who: "x y", want: a}) == earlyReplayMarker("tc", "m", &pinnedLib{who: "x", want: pins{"y " + "A B": "c"}}) {
		t.Fatal("ambiguous early marker")
	}
	if markerMAC([]byte("k"), "a b", "c") == markerMAC([]byte("k"), "a", "b c") {
		t.Fatal("ambiguous marker MAC")
	}
}

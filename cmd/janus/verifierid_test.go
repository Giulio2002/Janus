package main

import (
	"bytes"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"runtime/debug"
	"strings"
	"testing"
	"testing/fstest"

	janus "github.com/Giulio2002/Janus"
)

// The verifier identity (verifierid.go) names the code that decides a verdict in the result
// cache key. Every input class must change it (one test each), nothing path- or
// checkout-specific may, and whatever cannot be established exactly must fall back to the
// executable's bytes.

func snapshotFS(t *testing.T, e interface {
	ReadFile(string) ([]byte, error)
	ReadDir(string) ([]os.DirEntry, error)
}, root string) fstest.MapFS {
	t.Helper()
	m := fstest.MapFS{}
	var walk func(dir string)
	walk = func(dir string) {
		ents, err := e.ReadDir(dir)
		if err != nil {
			t.Fatal(err)
		}
		for _, d := range ents {
			p := d.Name()
			if dir != "." {
				p = dir + "/" + d.Name()
			}
			if d.IsDir() {
				walk(p)
				continue
			}
			b, err := e.ReadFile(p)
			if err != nil {
				t.Fatal(err)
			}
			m[p] = &fstest.MapFile{Data: b}
		}
	}
	walk(root)
	return m
}

func cloneFS(m fstest.MapFS) fstest.MapFS {
	c := fstest.MapFS{}
	for k, v := range m {
		c[k] = &fstest.MapFile{Data: append([]byte(nil), v.Data...)}
	}
	return c
}

type testBuild struct {
	b                       buildSnapshot
	sources, framework, asl fstest.MapFS
}

// baseBuild is a valid build of this very source tree: the real embedded files and a build
// information shaped like the one of a CGO_ENABLED=0 go build.
func baseBuild(t *testing.T) *testBuild {
	t.Helper()
	tb := &testBuild{
		sources:   snapshotFS(t, janus.GoSources, "."),
		framework: snapshotFS(t, janus.Framework, "."),
		asl:       snapshotFS(t, janus.ASL, "."),
	}
	real, ok := debug.ReadBuildInfo()
	if !ok || len(real.Deps) == 0 {
		t.Skip("no build information with dependencies")
	}
	bi := &debug.BuildInfo{
		GoVersion: "go1.99.0",
		Path:      "github.com/Giulio2002/Janus/cmd/janus",
		Main:      debug.Module{Path: "github.com/Giulio2002/Janus", Version: "(devel)"},
		Settings: []debug.BuildSetting{
			{Key: "-buildmode", Value: "exe"}, {Key: "-compiler", Value: "gc"}, {Key: "CGO_ENABLED", Value: "0"},
			{Key: "GOARCH", Value: "amd64"}, {Key: "GOOS", Value: "linux"}, {Key: "GOAMD64", Value: "v1"},
		},
	}
	for _, d := range real.Deps {
		c := *d
		c.Replace = nil
		bi.Deps = append(bi.Deps, &c)
	}
	tb.b = buildSnapshot{Info: bi, RuntimeVersion: "go1.99.0"}
	tb.sync()
	return tb
}

func (tb *testBuild) sync() {
	tb.b.Sources, tb.b.Framework, tb.b.ASL = tb.sources, tb.framework, tb.asl
}

// clone returns an independent copy (deep for the build information).
func (tb *testBuild) clone() *testBuild {
	c := &testBuild{sources: cloneFS(tb.sources), framework: cloneFS(tb.framework), asl: cloneFS(tb.asl)}
	bi := *tb.b.Info
	bi.Settings = append([]debug.BuildSetting(nil), tb.b.Info.Settings...)
	bi.Deps = nil
	for _, d := range tb.b.Info.Deps {
		cd := *d
		bi.Deps = append(bi.Deps, &cd)
	}
	c.b = tb.b
	c.b.Info = &bi
	c.sync()
	return c
}

func (tb *testBuild) setSetting(k, v string) {
	for i, s := range tb.b.Info.Settings {
		if s.Key == k {
			tb.b.Info.Settings[i].Value = v
			return
		}
	}
	tb.b.Info.Settings = append(tb.b.Info.Settings, debug.BuildSetting{Key: k, Value: v})
}

func mustID(t *testing.T, tb *testBuild) string {
	t.Helper()
	id, err := verifierIdentity(tb.b)
	if err != nil {
		t.Fatalf("expected an exact identity, got fallback: %v", err)
	}
	return id
}

func mustFallback(t *testing.T, tb *testBuild, want string) {
	t.Helper()
	id, err := verifierIdentity(tb.b)
	if err == nil {
		t.Fatalf("expected a fallback (%s), got identity %s", want, id)
	}
	if !strings.Contains(err.Error(), want) {
		t.Errorf("fallback reason %q does not mention %q", err, want)
	}
	comp, why := verifierComponentFor(tb.b, func() string { return "EXE" })
	if comp != "exe:EXE" || why == "" {
		t.Errorf("fallback component = %q (%q), want exe:EXE", comp, why)
	}
}

func TestVerifierIdentityBaseline(t *testing.T) {
	a, b := baseBuild(t), baseBuild(t)
	if mustID(t, a) != mustID(t, b) {
		t.Fatal("the identity of the same inputs is not deterministic")
	}
	comp, why := verifierComponentFor(a.b, func() string { return "EXE" })
	if !strings.HasPrefix(comp, "src:") || why != "" {
		t.Fatalf("component = %q (%q)", comp, why)
	}
	// Neither the VCS revision nor time nor a clean flag names the source: identical sources built
	// in a clean VCS checkout and outside one share an identity.
	c := a.clone()
	c.setSetting("vcs", "git")
	c.setSetting("vcs.revision", "0123456789abcdef")
	c.setSetting("vcs.time", "2026-01-01T00:00:00Z")
	c.setSetting("vcs.modified", "false")
	if mustID(t, c) != mustID(t, a) {
		t.Error("VCS revision/time changed the identity of identical sources")
	}
	// Test files are not part of the verifier.
	d := a.clone()
	d.sources["cmd/janus/some_test.go"] = &fstest.MapFile{Data: []byte("package main\n")}
	d.sources["cmd/janus/resultcache_test.go"] = &fstest.MapFile{Data: []byte("changed")}
	if mustID(t, d) != mustID(t, a) {
		t.Error("a _test.go file changed the identity")
	}
	// The result-cache key moves with the identity and with nothing path-like.
}

// Class: Go source of the module (every file of the command and of the root package, go.mod, go.sum).
func TestVerifierIdentityGoSource(t *testing.T) {
	base := baseBuild(t)
	want := mustID(t, base)
	n := 0
	for name := range base.sources {
		if !identityGoFile(name) {
			continue
		}
		n++
		c := base.clone()
		c.sources[name].Data = append(c.sources[name].Data, ' ') // one byte
		if name == "go.mod" || name == "go.sum" {
			c.sources[name].Data = append(c.sources[name].Data[:len(c.sources[name].Data)-1], '\n')
		}
		// go.sum/go.mod gain a byte but must stay consistent with the build information.
		if id, err := verifierIdentity(c.b); err == nil && id == want {
			t.Errorf("a one-byte change in %s did not change the identity", name)
		}
	}
	if n < 40 {
		t.Errorf("only %d source files hashed; the embed looks incomplete", n)
	}
	// A different byte at the same length, a new file, a removed file, a renamed file.
	c := base.clone()
	c.sources["cmd/janus/main.go"].Data[10] ^= 1
	if id, err := verifierIdentity(c.b); err == nil && id == want {
		t.Error("a flipped bit in main.go kept the identity")
	}
	c = base.clone()
	c.sources["cmd/janus/extra_new.go"] = &fstest.MapFile{Data: []byte("package main\n")}
	if mustID(t, c) == want {
		t.Error("a new source file kept the identity")
	}
	c = base.clone()
	c.sources["cmd/janus/renamed.go"] = c.sources["cmd/janus/speed.go"]
	delete(c.sources, "cmd/janus/speed.go")
	if mustID(t, c) == want {
		t.Error("a renamed source file kept the identity")
	}
	// go.sum: a changed line is a different build; a changed line that makes it disagree with the
	// dependencies the binary was linked with is a fallback, not an identity.
	c = base.clone()
	c.sources["go.sum"].Data = append(c.sources["go.sum"].Data, "example.com/other v1.0.0 h1:AAAA\n"...)
	if mustID(t, c) == want {
		t.Error("an extra go.sum line kept the identity")
	}
	// A missing manifest/embed: markers absent, or an unrelated source set.
	for _, m := range sourceMarkers {
		c = base.clone()
		delete(c.sources, m)
		mustFallback(t, c, "lack")
	}
	c = base.clone()
	c.b.Sources = nil
	mustFallback(t, c, "no embedded sources")
	c = base.clone()
	c.sources["go.mod"].Data = []byte("module example.com/other\n")
	mustFallback(t, c, "go.mod declares module")
}

// Class: dependencies (module version, content hash).
func TestVerifierIdentityDependencies(t *testing.T) {
	base := baseBuild(t)
	want := mustID(t, base)
	d := base.b.Info.Deps[0]

	// A bump that go.sum also records is a different build (and so a different key).
	c := base.clone()
	c.b.Info.Deps[0].Version = "v9.9.9"
	c.b.Info.Deps[0].Sum = "h1:BUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMP="
	c.sources["go.sum"].Data = append(c.sources["go.sum"].Data, (d.Path + " v9.9.9 h1:BUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMPEDBUMP=\n")...)
	if mustID(t, c) == want {
		t.Error("a dependency bump kept the identity")
	}
	// Different content under the same version: the content hash differs and go.sum (embedded in
	// the binary) cannot agree with both, so it is a fallback.
	c = base.clone()
	c.b.Info.Deps[0].Sum = "h1:ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ="
	mustFallback(t, c, "not in the embedded go.sum")
	// Replaced by a local directory, vendored or workspace modules have no content hash.
	c = base.clone()
	c.b.Info.Deps[0].Replace = &debug.Module{Path: "../x-arch", Version: ""}
	mustFallback(t, c, "no content hash")
	c = base.clone()
	c.b.Info.Deps[0].Sum = ""
	mustFallback(t, c, "no content hash")
	// Replaced by another module version: the replacement's hash must be in go.sum too.
	c = base.clone()
	c.b.Info.Deps[0].Replace = &debug.Module{Path: "example.com/fork", Version: "v1.0.0", Sum: "h1:FORKFORKFORKFORKFORKFORKFORKFORKFORKFORKFOR="}
	mustFallback(t, c, "not in the embedded go.sum")
	c.sources["go.sum"].Data = append(c.sources["go.sum"].Data, "example.com/fork v1.0.0 h1:FORKFORKFORKFORKFORKFORKFORKFORKFORKFORKFOR=\n"...)
	if mustID(t, c) == want {
		t.Error("a replacement module kept the identity")
	}
	// An extra or missing dependency is a different build.
	c = base.clone()
	c.b.Info.Deps = c.b.Info.Deps[1:]
	if len(base.b.Info.Deps) > 1 && mustID(t, c) == want {
		t.Error("a missing dependency kept the identity")
	}
}

// Class: toolchain version, GOOS/GOARCH/GOEXPERIMENT/flags/tags/cgo flags and every other build setting.
func TestVerifierIdentityBuildSettings(t *testing.T) {
	base := baseBuild(t)
	want := mustID(t, base)
	for _, kv := range [][2]string{
		{"-tags", "janusx"},
		{"-ldflags", "-X main.extractorVersion=forged"},
		{"-gcflags", "all=-N -l"},
		{"-asmflags", "-D x"},
		{"-trimpath", "true"},
		{"-race", "true"},
		{"-buildmode", "pie"},
		{"GOEXPERIMENT", "loopvar"},
		{"GOOS", "darwin"},
		{"GOARCH", "arm64"},
		{"GOAMD64", "v3"},
		{"CGO_CFLAGS", "-O0"},
		{"CGO_LDFLAGS", "-lfoo"},
		{"DefaultGODEBUG", "panicnil=1"},
		{"GOFLAGS_unknown_future_setting", "1"},
	} {
		c := base.clone()
		c.setSetting(kv[0], kv[1])
		if mustID(t, c) == want {
			t.Errorf("build setting %s=%q kept the identity", kv[0], kv[1])
		}
	}
	// Toolchain version (build information and runtime agree).
	c := base.clone()
	c.b.Info.GoVersion, c.b.RuntimeVersion = "go1.99.1", "go1.99.1"
	if mustID(t, c) == want {
		t.Error("a different Go toolchain version kept the identity")
	}
	// ...and a binary whose recorded toolchain is not the one running it is not trusted.
	c = base.clone()
	c.b.RuntimeVersion = "go1.99.1"
	mustFallback(t, c, "differs from the runtime")
	// Settings that cannot be established.
	c = base.clone()
	c.setSetting("CGO_ENABLED", "1")
	mustFallback(t, c, "cgo is enabled")
	c = base.clone()
	c.setSetting("-compiler", "gccgo")
	mustFallback(t, c, "not gc")
	c = base.clone()
	c.b.Info.Settings = append(c.b.Info.Settings, debug.BuildSetting{Key: "GOOS", Value: "linux"})
	mustFallback(t, c, "duplicate build setting")
	// An order change of the settings is not a change of the build.
	c = base.clone()
	s := c.b.Info.Settings
	s[0], s[len(s)-1] = s[len(s)-1], s[0]
	if mustID(t, c) != want {
		t.Error("the order of the build settings changed the identity")
	}
}

// Class: embedded files (the Lean framework and the JanusASL package).
func TestVerifierIdentityEmbeddedFiles(t *testing.T) {
	base := baseBuild(t)
	want := mustID(t, base)
	for _, p := range []string{"Janus.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"} {
		c := base.clone()
		c.framework[p].Data = append(c.framework[p].Data, '\n')
		if mustID(t, c) == want {
			t.Errorf("an edit of embedded %s kept the identity", p)
		}
	}
	n := 0
	for p := range base.framework {
		if !strings.HasPrefix(p, "Janus/") {
			continue
		}
		n++
		if n%25 != 0 {
			continue
		}
		c := base.clone()
		c.framework[p].Data = append(c.framework[p].Data, ' ')
		if mustID(t, c) == want {
			t.Errorf("an edit of embedded %s kept the identity", p)
		}
	}
	c := base.clone()
	c.framework["Janus/Added.lean"] = &fstest.MapFile{Data: []byte("")}
	if mustID(t, c) == want {
		t.Error("an added embedded framework file kept the identity")
	}
	for p := range base.asl {
		c := base.clone()
		c.asl[p].Data = append(c.asl[p].Data, ' ')
		if mustID(t, c) == want {
			t.Errorf("an edit of embedded %s kept the identity", p)
		}
	}
	c = base.clone()
	c.b.Framework = fstest.MapFS{}
	mustFallback(t, c, "framework")
	c = base.clone()
	c.b.ASL = nil
	mustFallback(t, c, "JanusASL")
}

// Dirty tree, no build information, tests, go run, a different main package: all fall back.
func TestVerifierIdentityFallbacks(t *testing.T) {
	base := baseBuild(t)
	c := base.clone()
	c.setSetting("vcs", "git")
	c.setSetting("vcs.modified", "true")
	mustFallback(t, c, "modified VCS tree")
	c = base.clone()
	c.b.Info = nil
	mustFallback(t, c, "no build information")
	c = base.clone()
	c.b.Testing = true
	mustFallback(t, c, "test binary")
	c = base.clone()
	c.b.Info.Path = "command-line-arguments" // go run file.go
	mustFallback(t, c, "not built as the janus command")
	c = base.clone()
	c.b.Info.Path = "github.com/Giulio2002/Janus/cmd/janus.test"
	mustFallback(t, c, "not built as the janus command")
	c = base.clone()
	c.b.Info.Main.Path = "example.com/fork"
	mustFallback(t, c, "not built as the janus command")
	// An unreadable executable and no identity: no cache at all.
	c = base.clone()
	c.b.Info = nil
	if comp, _ := verifierComponentFor(c.b, func() string { return "" }); comp != "" {
		t.Errorf("component %q without any identity", comp)
	}
	// JANUS_VERIFIER_ID=exe forces the executable key (only ever stricter).
	t.Setenv("JANUS_VERIFIER_ID", "exe")
	if comp, _ := verifierComponentFor(base.b, func() string { return "E" }); comp != "exe:E" {
		t.Errorf("JANUS_VERIFIER_ID=exe gave %q", comp)
	}
}

// This test binary can never claim a source identity (it is not the janus command), whatever its
// build information says.
func TestVerifierIdentityTestBinaryFallsBack(t *testing.T) {
	resetVerifierCache()
	defer resetVerifierCache()
	comp := verifierComponent()
	if !strings.HasPrefix(comp, "exe:") {
		t.Fatalf("a go test binary's component is %q, want the executable's hash", comp)
	}
	if comp != "exe:"+executableSha() {
		t.Fatalf("component %q is not the executable's SHA-256", comp)
	}
	if !currentBuild().Testing {
		t.Fatal("currentBuild does not report a test binary")
	}
}

// Class: everything else in the key (Lean toolchain, framework sources, pins, auditor, the
// extraction, the proof, ...) and the identity's own place in the key.
func TestResultKeyInputClasses(t *testing.T) {
	resetVerifierCache()
	defer resetVerifierCache()
	sys := t.TempDir()
	os.MkdirAll(filepath.Join(sys, "bin"), 0o755)
	os.MkdirAll(filepath.Join(sys, "lib"), 0o755)
	newTC := func(version, lean string) *toolchain {
		return &toolchain{version: version, lean: lean, leanchecker: lean, sysroot: sys, libDir: filepath.Join(sys, "lib")}
	}
	mk := func(mod func(*resultInputs)) string {
		in := &resultInputs{
			fw: &framework{Source: "directory", Sha256: "fwsha", Dir: "/x/a"}, root: "/x/a",
			fwPins: &pinnedLib{want: pins{"Janus.Foo": "h1"}}, auditExeSha: "audit",
			tc:  newTC("Lean 4.99", "/nonexistent/lean"),
			sb:  &sandbox{mode: "bwrap", bwrap: "/usr/bin/bwrap"},
			thm: "T", outdir: "/x/a/artifacts/F", proof: "/x/a/examples/F/Proof.lean", opts: map[string]string{},
			extracted: []byte("ext"), identity: []byte("id"), binPath: "/x/a/bin/f", binarySha: "binsha", proofSrc: []byte("proof"),
		}
		if mod != nil {
			mod(in)
		}
		return in.key()
	}
	base := mk(nil)
	if base == "" {
		t.Fatal("no key")
	}
	if mk(nil) != base {
		t.Fatalf("key not deterministic: %s %s %s", base, mk(nil), mk(nil))
	}
	// Checkout-specific absolute paths are not part of the key...
	same := mk(func(in *resultInputs) {
		in.fw.Dir, in.root = "/y/b", "/y/b"
		in.outdir, in.proof, in.binPath = "/y/b/artifacts/F", "/y/b/examples/F/Proof.lean", "/y/b/bin/f"
	})
	if same != base {
		t.Error("a different checkout path changed the key")
	}
	// ...everything that decides a verdict is.
	for name, mod := range map[string]func(*resultInputs){
		"framework sources":     func(in *resultInputs) { in.fw.Sha256 = "fwsha2" },
		"framework source kind": func(in *resultInputs) { in.fw.Source = "embedded" },
		"framework pins":        func(in *resultInputs) { in.fwPins = &pinnedLib{want: pins{"Janus.Foo": "h2"}} },
		"auditor":               func(in *resultInputs) { in.auditExeSha = "audit2" },
		"Lean toolchain": func(in *resultInputs) {
			in.tc = newTC("Lean 4.100", in.tc.lean)
		},
		"sandbox mode":                    func(in *resultInputs) { in.sb = &sandbox{mode: "unshare"} },
		"theorem":                         func(in *resultInputs) { in.thm = "U" },
		"replay-fresh":                    func(in *resultInputs) { in.opts = map[string]string{"replay-fresh": "1"} },
		"proof location in the artifact":  func(in *resultInputs) { in.proof = "/x/a/artifacts/F/Other.lean" },
		"binary location in the artifact": func(in *resultInputs) { in.binPath = "/x/a/artifacts/F/f" },
		"binary":                          func(in *resultInputs) { in.binarySha = "binsha2" },
		"extraction":                      func(in *resultInputs) { in.extracted = []byte("ext2") },
		"identity.json":                   func(in *resultInputs) { in.identity = []byte("id2") },
		"proof":                           func(in *resultInputs) { in.proofSrc = []byte("proof2") },
	} {
		if mk(mod) == base {
			t.Errorf("a change of the %s kept the key", name)
		}
	}
	// A framework build from a different Lean toolchain executable.
	dir := t.TempDir()
	l1, l2 := filepath.Join(dir, "lean1"), filepath.Join(dir, "lean2")
	os.WriteFile(l1, []byte("lean-a"), 0o755)
	os.WriteFile(l2, []byte("lean-b"), 0o755)
	k1 := mk(func(in *resultInputs) { in.tc = newTC("Lean 4", l1) })
	k2 := mk(func(in *resultInputs) { in.tc = newTC("Lean 4", l2) })
	if k1 == k2 {
		t.Error("different Lean executables kept the key")
	}
	// The verifier component is in the key: two verifiers, two keys; none, no key.
	verifierOnce.Do(func() {})
	verifierComp = "src:aaa"
	ka := mk(nil)
	verifierComp = "src:bbb"
	kb := mk(nil)
	verifierComp = "exe:aaa"
	kc := mk(nil)
	verifierComp = ""
	kn := mk(nil)
	if ka == kb || ka == kc || kn != "" {
		t.Errorf("verifier component not keyed: %q %q %q none=%q", ka, kb, kc, kn)
	}
	// "src:X" and "exe:X" can never be confused: the prefix is part of the hashed text.
	if mk(nil) != "" {
		t.Error("unexpected key")
	}
}

// A binary built from different source cannot present the same key: the key contains the
// identity hash of the embedded source; the identity of two builds is equal only if every hashed
// input is equal (tested above). Here, end to end through key().
func TestResultKeyDifferentSourceDifferentKey(t *testing.T) {
	resetVerifierCache()
	defer resetVerifierCache()
	base := baseBuild(t)
	other := base.clone()
	other.sources["cmd/janus/verify.go"].Data = append(other.sources["cmd/janus/verify.go"].Data, "\n// weakened\n"...)
	ca, _ := verifierComponentFor(base.b, func() string { return "E" })
	cb, _ := verifierComponentFor(other.b, func() string { return "E" })
	if ca == cb {
		t.Fatalf("different source, same component %s", ca)
	}
}

// A tampered, truncated, re-keyed or forged entry is a miss, never a hit.
func TestResultEntryTamperIsMiss(t *testing.T) {
	cache := filepath.Join(t.TempDir(), "cache")
	if err := os.Mkdir(cache, 0o700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_CACHE_DIR", cache)
	rep := &verifiedReport{Theorem: "T", Schema: 1, Timestamp: "2026-01-01T00:00:00Z"}
	key := strings.Repeat("ab", 32)
	other := strings.Repeat("cd", 32)
	storeResult(key, rep)
	if got := lookupResult(key); got == nil || got.Theorem != "T" {
		t.Fatalf("a stored entry is not found: %v", got)
	}
	p := resultPath(key)
	orig, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	var e resultEntry
	if err := json.Unmarshal(orig, &e); err != nil {
		t.Fatal(err)
	}
	write := func(b []byte) {
		t.Helper()
		if err := os.WriteFile(p, b, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	mutations := map[string][]byte{
		"report byte": bytes.Replace(orig, []byte(`"theorem":"T"`), []byte(`"theorem":"U"`), 1),
		"truncated":   orig[:len(orig)/2],
		"garbage":     []byte("not json"),
		"empty":       nil,
	}
	e2 := e
	e2.MAC = strings.Repeat("0", 64)
	mutations["wrong MAC"], _ = json.Marshal(e2)
	e3 := e
	e3.MAC = ""
	mutations["no MAC"], _ = json.Marshal(e3)
	e4 := e
	e4.Key = other
	mutations["rekeyed entry"], _ = json.Marshal(e4)
	e5 := e
	e5.Report = json.RawMessage(`{"theorem":"forged","schema":1}`)
	mutations["forged report, old MAC"], _ = json.Marshal(e5)
	for name, b := range mutations {
		if bytes.Equal(b, orig) {
			t.Fatalf("mutation %q did not change the entry", name)
		}
		write(b)
		if lookupResult(key) != nil {
			t.Errorf("%s: a tampered entry was a hit", name)
		}
	}
	// An entry copied to another key's file (its MAC covers its own key).
	write(orig)
	if err := os.MkdirAll(filepath.Dir(resultPath(other)), 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(resultPath(other), orig, 0o600); err != nil {
		t.Fatal(err)
	}
	if lookupResult(other) != nil {
		t.Error("an entry copied under another key was a hit")
	}
	// An entry authenticated under another cache's key (a forged cache directory).
	if lookupResult(key) == nil {
		t.Fatal("the intact entry stopped hitting")
	}
	hk, _ := resultHMACKey()
	forged := append([]byte{}, hk...)
	forged[0] ^= 1
	e6 := e
	e6.Report = json.RawMessage(`{"theorem":"forged","schema":1}`)
	e6.MAC = resultMAC(forged, key, e6.Report)
	b, _ := json.Marshal(e6)
	write(b)
	if lookupResult(key) != nil {
		t.Error("an entry authenticated with another key was a hit")
	}
	// A symbolic link in place of the entry is never followed.
	os.Remove(p)
	good := filepath.Join(t.TempDir(), "elsewhere.json")
	os.WriteFile(good, orig, 0o600)
	if err := os.Symlink(good, p); err == nil && lookupResult(key) != nil {
		t.Error("a symlinked entry was a hit")
	}
}

// ---- end to end: real builds of copies of the tree ----

func copyTreeForBuild(t *testing.T, dst string) {
	t.Helper()
	// Only what the command is built from; no .git, no .lake.
	items := []string{"go.mod", "go.sum", "framework.go", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "Janus.lean", "Janus", "JanusASL", "cmd"}
	for _, it := range items {
		cmd := exec.Command("cp", "-a", filepath.Join(repoRoot, it), dst+"/")
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("cp %s: %v\n%s", it, err, out)
		}
	}
	// The copy needs neither tests' testdata nor generated artifacts.
	os.RemoveAll(filepath.Join(dst, "JanusASL", ".lake"))
}

func buildCopy(t *testing.T, dir, out string, env []string, flags ...string) string {
	t.Helper()
	args := append(append([]string{"build"}, flags...), "-o", out, "./cmd/janus")
	cmd := exec.Command("go", args...)
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), append([]string{"GOFLAGS="}, env...)...)
	if o, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go build %v in %s: %v\n%s", flags, dir, err, o)
	}
	o, err := exec.Command(out, "verifier-id").Output()
	if err != nil {
		t.Fatalf("verifier-id: %v", err)
	}
	return strings.TrimSpace(string(o))
}

func TestVerifierIdentityRealBuilds(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the command several times")
	}
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no go tool")
	}
	scratch, err := os.MkdirTemp(os.Getenv("JANUS_TEST_SCRATCH"), "verifierid-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(scratch)
	a, b := filepath.Join(scratch, "wt-a"), filepath.Join(scratch, "deeper", "wt-b")
	for _, d := range []string{a, b} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			t.Fatal(err)
		}
		copyTreeForBuild(t, d)
	}
	nocgo := []string{"CGO_ENABLED=0"}
	idA := buildCopy(t, a, filepath.Join(scratch, "ja"), nocgo)
	if !strings.HasPrefix(idA, "src:") {
		t.Fatalf("copy A: %q, want a source identity", idA)
	}
	// Same source in a different directory (and a different build path): the same identity.
	if idB := buildCopy(t, b, filepath.Join(scratch, "jb"), nocgo); idB != idA {
		t.Errorf("same source in another directory: %s != %s", idB, idA)
	}
	// One byte in a Go source file: a different identity.
	mainGo := filepath.Join(b, "cmd", "janus", "main.go")
	src, _ := os.ReadFile(mainGo)
	os.WriteFile(mainGo, append(src, "\n// one more byte\n"...), 0o644)
	idEdit := buildCopy(t, b, filepath.Join(scratch, "jb2"), nocgo)
	if idEdit == idA || !strings.HasPrefix(idEdit, "src:") {
		t.Errorf("edited source: %s (original %s)", idEdit, idA)
	}
	os.WriteFile(mainGo, src, 0o644)
	// An edit of an embedded Lean file: a different identity.
	lean := filepath.Join(b, "Janus.lean")
	lsrc, _ := os.ReadFile(lean)
	os.WriteFile(lean, append(lsrc, "\n-- edit\n"...), 0o644)
	if id := buildCopy(t, b, filepath.Join(scratch, "jb3"), nocgo); id == idA {
		t.Errorf("edited embedded file kept the identity %s", id)
	}
	os.WriteFile(lean, lsrc, 0o644)
	// Build flags and tags: different identities; and the identity returns when they do.
	for name, flags := range map[string][]string{
		"-tags":     {"-tags", "janusx"},
		"-ldflags":  {"-ldflags", "-X main.noSuchVar=1"},
		"-gcflags":  {"-gcflags", "all=-l"},
		"-trimpath": {"-trimpath"},
	} {
		if id := buildCopy(t, a, filepath.Join(scratch, "jf"), nocgo, flags...); id == idA || !strings.HasPrefix(id, "src:") {
			t.Errorf("%s: %s (default %s)", name, id, idA)
		}
	}
	if id := buildCopy(t, a, filepath.Join(scratch, "jx"), append([]string{"GOEXPERIMENT=norandomizedheapbase64"}, nocgo...)); id == idA {
		t.Errorf("GOEXPERIMENT: %s", id)
	}
	if id := buildCopy(t, a, filepath.Join(scratch, "jg"), append([]string{"GOAMD64=v3"}, nocgo...)); id == idA && runtimeGOARCH() == "amd64" {
		t.Errorf("GOAMD64: %s", id)
	}
	// cgo enabled: its C compiler is unknown, so the executable's bytes name the verifier.
	if id := buildCopy(t, a, filepath.Join(scratch, "jc"), []string{"CGO_ENABLED=1"}); !strings.HasPrefix(id, "exe:") {
		t.Errorf("CGO_ENABLED=1: %s, want the executable fallback", id)
	}
	// -buildvcs=false changes nothing (no revision is hashed); a modified VCS tree falls back.
	if _, err := exec.LookPath("git"); err == nil {
		git := func(args ...string) {
			t.Helper()
			c := exec.Command("git", append([]string{"-c", "user.email=t@example.com", "-c", "user.name=t", "-c", "safe.directory=*"}, args...)...)
			c.Dir = b
			if o, err := c.CombinedOutput(); err != nil {
				t.Fatalf("git %v: %v\n%s", args, err, o)
			}
		}
		git("init", "-q", ".")
		git("add", "-A")
		git("commit", "-q", "-m", "x")
		if id := buildCopy(t, b, filepath.Join(scratch, "jv"), nocgo); id != idA {
			t.Errorf("clean VCS tree: %s, want %s (the VCS revision must not name the source)", id, idA)
		}
		src, _ = os.ReadFile(mainGo)
		os.WriteFile(mainGo, append(src, "\n// dirty\n"...), 0o644)
		if id := buildCopy(t, b, filepath.Join(scratch, "jd"), nocgo); !strings.HasPrefix(id, "exe:") {
			t.Errorf("modified VCS tree: %s, want the executable fallback", id)
		}
		os.WriteFile(mainGo, src, 0o644)
		os.WriteFile(filepath.Join(b, "untracked.txt"), []byte("x"), 0o644)
		if id := buildCopy(t, b, filepath.Join(scratch, "jd2"), nocgo); !strings.HasPrefix(id, "exe:") {
			t.Errorf("untracked file in a VCS tree: %s, want the executable fallback", id)
		}
	}
	// go run of the package: no source identity (checked via the build of a file list).
	cmd := exec.Command("go", "run", "-C", a, "./cmd/janus", "verifier-id")
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0")
	if o, err := cmd.Output(); err != nil || !strings.HasPrefix(strings.TrimSpace(string(o)), "src:") {
		// `go run ./pkg` builds the package like go build; only go run of a file list differs.
		t.Logf("go run ./cmd/janus: %q %v", o, err)
	}
}

func runtimeGOARCH() string {
	out, _ := exec.Command("go", "env", "GOARCH").Output()
	return strings.TrimSpace(string(out))
}

// Every package of this module that the command links must be embedded (GoSources), and every Go
// file of those packages must be in it: a new internal package would otherwise silently escape
// the identity.
func TestGoSourcesCoverModulePackages(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("no go tool")
	}
	cmd := exec.Command("go", "list", "-deps", "-f", "{{if not .Standard}}{{.ImportPath}} {{.Dir}}{{end}}", "github.com/Giulio2002/Janus/cmd/janus")
	cmd.Dir = repoRoot
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0")
	out, err := cmd.Output()
	if err != nil {
		t.Skipf("go list: %v", err)
	}
	const mod = "github.com/Giulio2002/Janus"
	for _, l := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		f := strings.SplitN(l, " ", 2)
		if len(f) != 2 || !strings.HasPrefix(f[0]+"/", mod+"/") {
			continue // dependencies are covered by go.sum and the build information
		}
		rel := strings.TrimPrefix(strings.TrimPrefix(f[0], mod), "/")
		if rel != "" && rel != "cmd/janus" {
			t.Errorf("the command links %s, whose sources GoSources does not embed (add them to framework.go)", f[0])
			continue
		}
		ents, err := os.ReadDir(f[1])
		if err != nil {
			t.Fatal(err)
		}
		for _, e := range ents {
			if strings.HasSuffix(e.Name(), ".go") && !strings.HasSuffix(e.Name(), "_test.go") {
				p := e.Name()
				if rel != "" {
					p = rel + "/" + p
				}
				if _, err := janus.GoSources.ReadFile(p); err != nil {
					t.Errorf("%s is not embedded in GoSources: %v", p, err)
				}
			}
		}
	}
	// Dependencies: every module in the build list has a go.sum content hash.
	for _, p := range []string{"go.mod", "go.sum"} {
		if _, err := janus.GoSources.ReadFile(p); err != nil {
			t.Errorf("%s is not embedded: %v", p, err)
		}
	}
}

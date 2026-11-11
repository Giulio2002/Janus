package main

import (
	"os"
	"path"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// Round 15a (test/redteam/rounds/round15a): Lake configurations whose sources or settings the result-cache key
// does not cover must not be cacheable. Every row below must be non-cacheable.
func TestRound15aLakefileNotCacheable(t *testing.T) {
	ok := func(toml string) bool {
		return lakefileCacheable(map[string][]byte{"lakefile.toml": []byte(toml)}, "lakefile.toml")
	}
	base := "name = \"p\"\ndefaultTargets = [\"P\"]\n\n[[require]]\nname = \"janus\"\ngit = \"https://x\"\nrev = \"abc\"\n\n[[lean_lib]]\nname = \"P\"\n"
	if !ok(base) {
		t.Fatal("the plain package is not cacheable")
	}
	for name, extra := range map[string]string{
		// the workspace keeps .lake across runs (syncTree keepLake) and the sandboxed build can write there:
		// sources under it are not in the snapshot, hence not in the key
		"srcDir in .lake":       "srcDir = \".lake/pre\"\n",
		"srcDir in .git":        "srcDir = \".git/x\"\n",
		"srcDir hidden":         "srcDir = \".hidden\"\n",
		"srcDir artifacts":      "srcDir = \"artifacts\"\n",
		"srcDir generated":      "srcDir = \"generated/x\"\n",
		"srcDir bin":            "srcDir = \"bin\"\n",
		"srcDir obj":            "srcDir = \"obj\"\n",
		"srcDir dotted deep":    "srcDir = \"a/.b/c\"\n",
		"srcDir leading dot/":   "srcDir = \"./.lake\"\n",
		"srcDir dir symlink":    "srcDir = \"a//.lake\"\n",
		"buildDir":              "buildDir = \"/x\"\n",
		"leanLibDir":            "leanLibDir = \"/x\"\n",
		"irDir":                 "irDir = \"/x\"\n",
		"packagesDir":           "packagesDir = \"/x\"\n",
		"testDriver":            "testDriver = \"x\"\n",
		"extraDepTargets":       "extraDepTargets = [\"x\"]\n",
		"needs":                 "needs = [\"x\"]\n",
		"nativeFacets":          "nativeFacets = [\"shared\"]\n",
		"leanArgs":              "leanArgs = [\"--load-dynlib=/x\"]\n",
		"server opts":           "moreServerOptions = [\"x\"]\n",
		"weak.debug":            "\n[leanOptions]\nweak.debug.skipKernelTC = true\n",
		"weak.weak.debug":       "\n[leanOptions]\nweak.weak.debug.skipKernelTC = true\n",
		"leanOptions plugin":    "\n[leanOptions]\nweak.plugin = 1\n",
		"leanOptions dotdot":    "\n[leanOptions]\npp..x = 1\nlinter..y=true\ndebug.x=1\n",
		"Lean.ofReduceBool":     "\n[leanOptions]\ndebug.moduleNameAtTimeout = false\n",
		"leanOptions as inline": "leanOptions = {debug.skipKernelTC = true}\n",
		"table in table":        "\n[lean_lib.x]\nname=\"y\"\n",
		"BOM":                   "\xef\xbb\xbf" + base,
		"NUL":                   "name = \"p\x00\"\n",
		"tab key":               "\tsrcDir\t=\t\"/abs\"\n",
		"lone CR in comment":    "# a\rsrcDir = \"/abs\"\n",
		"form feed":             "\fsrcDir = \"/abs\"\n",
		"vertical tab":          "\vsrcDir = \"/abs\"\n",
		"unicode key":           "srcDir = \"/abs\"\n",
		"line sep":              "name = \"a\" srcDir = \"/abs\"\n",
		"escaped quote":         "srcDir = \"a\\\"b\"\n",
		"literal backslash":     "srcDir = 'a\\..\\b'\n",
		"literal dotdot":        "srcDir = '..'\n",
		"srcDir empty":          "srcDir = \"\"\n",
		"srcDir colon":          "srcDir = \"a:b\"\n",
		"dotdot not first":      "srcDir = \"a/b/../../..\"\n",
		"integer srcDir":        "srcDir = 1\n",
		"bool srcDir":           "srcDir = true\n",
		"roots nul":             "roots = [\"A\x00\"]\n",
		"root ..":               "root = \"..\"\n",
		"name ..":               "name = \"..\"\n",
		"defaultTargets ..":     "defaultTargets = [\"../x\"]\n",
	} {
		if ok(base + extra) {
			t.Errorf("%s was cacheable", name)
		}
	}
}

// Invariant (round 15a): for every accepted configuration, each file Lake could resolve for a root
// under srcDir that exists on disk is a file of the hashed snapshot.
func TestRound15aResolvableSubsetOfSnapshot(t *testing.T) {
	dir := t.TempDir()
	for _, f := range []string{"A.lean", "src/B.lean", ".lake/pre/A.lean", ".lake/B.lean", "bin/A.lean", "bin/X.lean", "artifacts/A.lean",
		"generated/A.lean", "obj/A.lean", ".git/A.lean", ".hid/A.lean", "src/.hid/A.lean", "src/bin/A.lean", "lib/.lake/A.lean"} {
		writeFile(t, filepath.Join(dir, f), "x")
	}
	snap, err := snapshotDir(dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	base := "name = \"p\"\n\n[[lean_lib]]\nname = \"P\"\n"
	accepted := 0
	for _, sd := range []string{"", ".", "src", "./src", ".lake/pre", ".lake", ".hid", "src/.hid", "bin", "src/bin", "artifacts", "generated", "obj", ".git", "lib/.lake"} {
		for _, root := range []string{"A", "B", "X", "bin.A", "bin.X", ".lake.B", "lake.A", "hid.A", "A.", ".A", "src.B", "generated.A", "artifacts.A"} {
			cfg := base + "roots = [\"" + root + "\"]\n"
			if sd != "" {
				cfg += "srcDir = \"" + sd + "\"\n"
			}
			if !lakefileCacheable(map[string][]byte{"lakefile.toml": []byte(cfg)}, "lakefile.toml") {
				continue
			}
			accepted++
			rel := path.Join(sd, strings.ReplaceAll(root, ".", "/")+".lean")
			if _, err := os.Stat(filepath.Join(dir, rel)); err != nil {
				continue
			}
			if _, ok := snap[rel]; !ok {
				t.Errorf("accepted srcDir=%q root=%q resolves %s, which is not in the snapshot", sd, root, rel)
			}
		}
	}
	if accepted == 0 {
		t.Fatal("no configuration accepted: the test checks nothing")
	}
}

// A cached consumer-package pass must MISS when the janus binary, the framework (sources or build)
// or the Lean toolchain changes (round 15a, follow-up 3). The key is the whole cache lookup (an
// entry is found only under an identical key), so this exercises it through consumerResultInputs.key
// with a stored entry: the entry is a hit under the recorded inputs and a miss under each change.
func TestRound15aConsumerCacheMissOnVerifierFrameworkToolchain(t *testing.T) {
	resetVerifierCache()
	defer resetVerifierCache()
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	if err := os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700); err != nil {
		t.Fatal(err)
	}
	sys := t.TempDir()
	os.MkdirAll(filepath.Join(sys, "bin"), 0o755)
	os.MkdirAll(filepath.Join(sys, "lib"), 0o755)
	leanA, leanB := filepath.Join(sys, "leanA"), filepath.Join(sys, "leanB")
	os.WriteFile(leanA, []byte("lean-a"), 0o755)
	os.WriteFile(leanB, []byte("lean-b"), 0o755)
	newTC := func(v, lean string) *toolchain {
		return &toolchain{version: v, lean: lean, leanchecker: lean, sysroot: sys, libDir: filepath.Join(sys, "lib")}
	}
	toml := []byte("name = \"p\"\n\n[[lean_lib]]\nname = \"P\"\n")
	mk := func(mod func(in *consumerResultInputs)) string {
		pkg := &consumerPkg{Root: "/x/p", Lakefile: "lakefile.toml", Files: map[string][]byte{"lakefile.toml": toml, "P.lean": []byte("p")}}
		pkg.Sha256 = treeSha(pkg.Files)
		out := t.TempDir()
		in := &consumerResultInputs{
			fw: &framework{Source: "directory", Sha256: "fwsha"}, fwPins: &pinnedLib{want: pins{"Janus.Foo": "h1"}},
			auditExeSha: "audit", tc: newTC("Lean 4.99", leanA), lakeSha: "lake", sb: &sandbox{mode: "bwrap", bwrap: "/usr/bin/bwrap"},
			thm: "P.correctness", opts: map[string]string{}, pkg: pkg,
			req: &consumerRequest{Outdir: out, rel: "P.lean", proofSrc: []byte("p"),
				cr: &CheckResult{BinPath: filepath.Join(out, "bin"), Lean: []byte("ext"), Identity: &Identity{BinarySha256: "bin"}}},
		}
		if mod != nil {
			mod(in)
		}
		return in.key()
	}
	verifierMu.Lock()
	verifierDone = true
	verifierMu.Unlock()
	verifierComp = "src:aaa"
	base := mk(nil)
	if base == "" {
		t.Fatal("no key")
	}
	rep := &verifiedReport{Theorem: "P.correctness"}
	storeResult(base, rep)
	if lookupResult(base) == nil {
		t.Fatal("the recorded entry is not found under its own key")
	}
	miss := func(name, key string) {
		t.Helper()
		if key == base || lookupResult(key) != nil {
			t.Errorf("%s: a cached pass was served (key unchanged or entry found)", name)
		}
	}
	verifierComp = "src:bbb" // (a) a different janus binary (source identity) ...
	miss("janus source", mk(nil))
	verifierComp = "exe:aaa" // ... or an executable fallback of the same text
	miss("janus executable", mk(nil))
	verifierComp = "src:aaa"
	miss("framework sources", mk(func(in *consumerResultInputs) { in.fw.Sha256 = "fwsha2" })) // (b)
	miss("framework build", mk(func(in *consumerResultInputs) { in.fwPins = &pinnedLib{want: pins{"Janus.Foo": "h2"}} }))
	miss("auditor build", mk(func(in *consumerResultInputs) { in.auditExeSha = "audit2" }))
	miss("toolchain version", mk(func(in *consumerResultInputs) { in.tc = newTC("Lean 4.100", leanA) })) // (c)
	miss("toolchain executable", mk(func(in *consumerResultInputs) { in.tc = newTC("Lean 4.99", leanB) }))
	miss("lake executable", mk(func(in *consumerResultInputs) { in.lakeSha = "lake2" }))
	if mk(nil) != base || lookupResult(mk(nil)) == nil {
		t.Error("the unchanged inputs no longer hit")
	}
}

func TestRound15aParseImports(t *testing.T) {
	for _, c := range []struct {
		src  string
		want []string
		ok   bool
	}{
		{"import A\nimport B.C\n\ntheorem x : True := trivial", []string{"A", "B.C"}, true},
		{"/- c /- nested -/ -/\n-- x\nimport  A -- y\npublic import B\npublic meta import all C\nnamespace Q\nimport Z", []string{"A", "B", "C"}, true},
		// Lean's module system: modifiers precede `import`; `all` follows it (EthLib's header shape)
		{"module\n\npublic import EthLib.A\npublic import EthLib.B\nmeta import M\nprivate import P\nimport all Q\n\n@[expose] public section\ndef x := 1", []string{"EthLib.A", "EthLib.B", "M", "P", "Q"}, true},
		{"module\npublic section\nimport A", nil, true}, // `public` before something else ends the header
		{"import all\nimport B", nil, false},            // Lean rejects `import all` without a module
		{"public import «A»", nil, false},
		{"module\nprelude\nimport Init.Core", []string{"Init.Core"}, true},
		{"/-! doc -/\nimport A", nil, true}, // a module doc ends the header: no import after it counts
		{"@[simp] theorem t : True := trivial\nimport A", nil, true},
		{"import «A»", nil, false},
		{"import A.\n", nil, false},
		{"import A..B\n", nil, false},
		{"/- never closed\nimport A", nil, false},
		{"import Ä\n", nil, false},
		{"", nil, true},
	} {
		got, ok := parseImports([]byte(c.src))
		if ok != c.ok || strings.Join(got, ",") != strings.Join(c.want, ",") {
			t.Errorf("parseImports(%q) = %v %v, want %v %v", c.src, got, ok, c.want, c.ok)
		}
	}
}

func TestRound15aCompileConfig(t *testing.T) {
	// the lakefile.toml of a typical fv-uint256 package is in the subset
	fv := "# c\nname = \"fv256\"\ndefaultTargets = [\"Fv256\"]\n\n[[require]]\nname = \"janus\"\ngit = \"/srv/janus\"\nrev = \"f1d61dc1fc23f83dda0a465afa81ecec1f469fdf\"\n\n[[lean_lib]]\nname = \"Fv256\"\n"
	sd, do, ok := compileConfig(map[string][]byte{"lakefile.toml": []byte(fv)}, "lakefile.toml")
	if !ok || len(do) != 0 || strings.Join(sd, ",") != "" {
		t.Fatalf("plain package: %v %v %v", sd, do, ok)
	}
	opt := fv + "srcDir = \"lean\"\n\n[leanOptions]\nmaxHeartbeats = 400_000\nautoImplicit = false\nweak.linter.unusedVariables = false\npp.unicode = true\n"
	sd, do, ok = compileConfig(map[string][]byte{"lakefile.toml": []byte(opt)}, "lakefile.toml")
	if !ok || strings.Join(sd, ",") != ",lean" || strings.Join(do, " ") != "-DmaxHeartbeats=400000 -DautoImplicit=false -Dweak.linter.unusedVariables=false -Dpp.unicode=true" {
		t.Fatalf("options: %v %v %v", sd, do, ok)
	}
	for name, cfg := range map[string]string{
		"array option":    fv + "\n[leanOptions]\nmaxHeartbeats = [1]\n",
		"float option":    fv + "\n[leanOptions]\nmaxHeartbeats = 1.5\n",
		"srcDir in .lake": fv + "srcDir = \".lake/x\"\n",
		"more args":       fv + "moreLeanArgs = [\"-DfooBar=1\"]\n",
	} {
		if _, _, ok := compileConfig(map[string][]byte{"lakefile.toml": []byte(cfg)}, "lakefile.toml"); ok {
			t.Errorf("%s accepted", name)
		}
	}
	if _, _, ok := compileConfig(map[string][]byte{"lakefile.lean": []byte("import Lake")}, "lakefile.lean"); ok {
		t.Error("lakefile.lean accepted")
	}
}

// The olean store: a tampered olean, a tampered entry and a swapped entry are misses.
func TestRound15aOleanStore(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	if err := os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700); err != nil {
		t.Fatal(err)
	}
	k1, k2 := strings.Repeat("a", 64), strings.Repeat("b", 64)
	oleanStorePut(k1, modParts{".olean": []byte("olean-1")})
	oleanStorePut(k2, modParts{".olean": []byte("olean-2")})
	if d, ok := oleanStoreGet(k1); !ok || string(d[".olean"]) != "olean-1" {
		t.Fatalf("stored olean not found: %q %v", d, ok)
	}
	dir := func(k string) string { return filepath.Join(oleanStoreDir(), k[:2]) }
	// planted bytes under the right entry
	os.WriteFile(filepath.Join(dir(k1), k1+".olean"), []byte("forged"), 0o600)
	if _, ok := oleanStoreGet(k1); ok {
		t.Error("a modified olean was served")
	}
	// the entry of k2 copied under k1's name
	b, _ := os.ReadFile(filepath.Join(dir(k2), k2+".json"))
	os.WriteFile(filepath.Join(dir(k1), k1+".json"), b, 0o600)
	os.WriteFile(filepath.Join(dir(k1), k1+".olean"), []byte("olean-2"), 0o600)
	if _, ok := oleanStoreGet(k1); ok {
		t.Error("another key's entry was served")
	}
	// an entry with a forged hash and no valid MAC
	os.WriteFile(filepath.Join(dir(k2), k2+".json"), []byte(`{"key":"`+k2+`","sha256":"`+sha256Hex([]byte("x"))+`","parts":{".olean":"`+sha256Hex([]byte("x"))+`"},"mac":"00"}`), 0o600)
	os.WriteFile(filepath.Join(dir(k2), k2+".olean"), []byte("x"), 0o600)
	if _, ok := oleanStoreGet(k2); ok {
		t.Error("an entry without a valid MAC was served")
	}
}

// The olean store keeps every part of a module-system module (server, private, IR) under one authenticated entry:
// a modified part, a part dropped from the store, and a v0.2.0-style entry (olean hash only) are misses.
func TestOleanStoreModuleParts(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	if err := os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700); err != nil {
		t.Fatal(err)
	}
	k := strings.Repeat("c", 64)
	full := modParts{".olean": []byte("o"), ".olean.server": []byte("s"), ".olean.private": []byte("p"), ".ir": []byte("i")}
	oleanStorePut(k, full)
	d, ok := oleanStoreGet(k)
	if !ok || len(d) != 4 || string(d[".olean.server"]) != "s" || d.digest() != full.digest() {
		t.Fatalf("stored parts not served whole: %v %v", d, ok)
	}
	dir := filepath.Join(oleanStoreDir(), k[:2])
	os.WriteFile(filepath.Join(dir, k+".olean.server"), []byte("forged"), 0o600)
	if _, ok := oleanStoreGet(k); ok {
		t.Error("a modified server part was served")
	}
	oleanStorePut(k, full)
	os.Remove(filepath.Join(dir, k+".olean.private"))
	if _, ok := oleanStoreGet(k); ok {
		t.Error("a module with a missing part was served")
	}
	// an entry in the v0.2.0 format (no parts) is not authentic under the v2 MAC
	oleanStorePut(k, full)
	os.WriteFile(filepath.Join(dir, k+".json"), []byte(`{"key":"`+k+`","sha256":"`+sha256Hex([]byte("o"))+`","mac":"00"}`), 0o600)
	if _, ok := oleanStoreGet(k); ok {
		t.Error("an old-format entry was served")
	}
	// the digest of an olean-only module is the olean's SHA-256 (keys of non-module files unchanged)
	if got := (modParts{".olean": []byte("o")}).digest(); got != sha256Hex([]byte("o")) {
		t.Errorf("olean-only digest = %s", got)
	}
	if full.digest() == sha256Hex([]byte("o")) {
		t.Error("the digest ignores the server/private/IR parts")
	}
}

// readModParts takes every part lean -o wrote; write puts them next to the olean and removes stale parts.
func TestModPartsReadWrite(t *testing.T) {
	src, dst := t.TempDir(), t.TempDir()
	for ext, b := range map[string]string{".olean": "o", ".olean.server": "s", ".ir": "i"} {
		os.WriteFile(filepath.Join(src, "out"+ext), []byte(b), 0o600)
	}
	p, err := readModParts(filepath.Join(src, "out.olean"))
	if err != nil || len(p) != 3 || string(p[".olean.server"]) != "s" {
		t.Fatalf("readModParts = %v, %v", p, err)
	}
	target := filepath.Join(dst, "A", "B.olean")
	os.MkdirAll(filepath.Dir(target), 0o755)
	os.WriteFile(filepath.Join(dst, "A", "B.olean.private"), []byte("stale"), 0o600)
	if err := p.write(target); err != nil {
		t.Fatal(err)
	}
	for ext, want := range map[string]string{".olean": "o", ".olean.server": "s", ".ir": "i"} {
		if b, _ := os.ReadFile(filepath.Join(dst, "A", "B"+ext)); string(b) != want {
			t.Errorf("%s = %q", ext, b)
		}
	}
	if _, err := os.Stat(filepath.Join(dst, "A", "B.olean.private")); !os.IsNotExist(err) {
		t.Error("a stale part was kept")
	}
	if _, err := readModParts(filepath.Join(src, "missing.olean")); err == nil {
		t.Error("a missing olean was accepted")
	}
}

// Round 15a, olean provenance: a planted Lake olean (the variant's olean and output hashes, the
// genuine trace kept) is never the environment that is audited and replayed: janus compiled the
// module itself from the hashed source. The unchanged package reuses the stored olean (no compile).
func TestRound15aPlantedOlean(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	add := mustExtract(t, "example.com/basic.Add")
	pkgS := consumerCopy(t, "toml")
	pkgV := consumerCopyAt(t, "toml", repoRoot, filepath.Join(t.TempDir(), "variant"))
	vsrc := filepath.Join(pkgV, "ConsumerExample", "Add.lean")
	b, err := os.ReadFile(vsrc)
	if err != nil {
		t.Fatal(err)
	}
	vb := strings.Replace(string(b), "Computes Extracted.program Extracted.entry addSpec :=", "Computes Extracted.program Extracted.entry (fun x y => addSpec x y) :=", 1)
	if vb == string(b) {
		t.Fatal("cannot build the variant")
	}
	os.WriteFile(vsrc, []byte(vb), 0o644)
	verify := func(pkg string) *verifiedReport {
		t.Helper()
		code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"), "--proof-root", pkg,
			"--theorem", "ConsumerExample.Add.correctness", "--theorem", "ConsumerExample.Add.Witness.nonvacuous", "--no-result-cache")
		if code != 0 {
			t.Fatalf("verify %s: %d\n%s\n%s", pkg, code, out, stderr)
		}
		return readReport(t, add)
	}
	t0 := time.Now()
	rS := verify(pkgS)
	cold := time.Since(t0)
	if rS.OleanProvenance != provChecked || strings.Contains(rS.Statement, "fun x y") {
		t.Fatalf("provenance %q, statement %s", rS.OleanProvenance, rS.Statement)
	}
	// the unchanged package: the stored oleans are reused, nothing is compiled again
	before := ownCompiles.Load()
	t0 = time.Now()
	verify(pkgS)
	warm := time.Since(t0)
	if n := ownCompiles.Load() - before; n != 0 {
		t.Errorf("an unchanged package compiled %d module(s) again", n)
	}
	t.Logf("provenance overhead: cold %v, warm %v", cold, warm)
	rV := verify(pkgV)
	if !strings.Contains(rV.Statement, "fun x y") {
		t.Fatalf("the variant's statement is not distinguishable: %s", rV.Statement)
	}
	L := filepath.Join(".lake", "build", "lib", "lean", "ConsumerExample")
	planted := 0
	for _, f := range []string{"Add.olean", "Add.ilean", "Add.olean.hash", "Add.ilean.hash"} {
		data, err := os.ReadFile(filepath.Join(rV.Consumer.Workspace, "root", L, f))
		if err != nil {
			data = []byte("garbage, not an olean") // Lake no longer builds the module: plant garbage
		}
		os.MkdirAll(filepath.Join(rS.Consumer.Workspace, "root", L), 0o755)
		if err := os.WriteFile(filepath.Join(rS.Consumer.Workspace, "root", L, f), data, 0o644); err != nil {
			t.Fatal(err)
		}
		planted++
	}
	if planted == 0 {
		t.Fatal("nothing planted")
	}
	r2 := verify(pkgS)
	if r2.Statement != rS.Statement || strings.Contains(r2.Statement, "fun x y") || r2.OleanProvenance != provChecked {
		t.Errorf("the planted olean decided the audited statement:\n%s\nwant\n%s", r2.Statement, rS.Statement)
	}
}

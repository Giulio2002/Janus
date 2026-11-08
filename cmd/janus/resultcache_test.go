package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// TestResultCache: a repeated identical verification is a cache hit that prints the same report
// plus "Cached:"; any changed input, --fresh, --unsafe-no-sandbox and a tampered entry are
// misses. (audit/round7 attacks the cache from a proof and a lakefile.)
func TestResultCache(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	proof := filepath.Join(t.TempDir(), "resultcache-proof", "Add.lean")
	if err := os.MkdirAll(filepath.Dir(proof), 0o755); err != nil {
		t.Fatal(err)
	}
	src, err := os.ReadFile(filepath.Join(repoRoot, "examples", "proofs", "Add.lean"))
	if err != nil {
		t.Fatal(err)
	}
	// A per-run comment: the shared test cache keeps other runs' entries.
	src = append(src, fmt.Sprintf("\n-- TestResultCache run %d\n", time.Now().UnixNano())...)
	if err := os.WriteFile(proof, src, 0o644); err != nil {
		t.Fatal(err)
	}
	verify := func(extra ...string) (string, string) {
		t.Helper()
		code, out, stderr := runJanus(t, append([]string{"verify", add, "--proof", proof, "--janus-root", repoRoot}, append(append([]string{}, proofThms...), extra...)...)...)
		if code != 0 {
			t.Fatalf("verify %v: %d\n%s\n%s", extra, code, out, stderr)
		}
		return out, stderr
	}
	isCached := func(out string) bool { return strings.Contains(out, "\n  Cached: ") }
	withoutCached := func(out string) string {
		var keep []string
		for _, l := range strings.Split(out, "\n") {
			if !strings.HasPrefix(l, "  Cached: ") {
				keep = append(keep, l)
			}
		}
		return strings.Join(keep, "\n")
	}

	first, _ := verify()
	if isCached(first) {
		t.Fatalf("first verification reported as cached:\n%s", first)
	}
	second, _ := verify()
	if !isCached(second) {
		t.Fatalf("identical second verification not a cache hit:\n%s", second)
	}
	if withoutCached(second) != first {
		t.Errorf("a hit must print what a fresh run prints, plus Cached:\nfresh:\n%s\nhit:\n%s", first, second)
	}
	if r := readReport(t, add); !r.Cached || r.CachedFrom == "" {
		t.Errorf("verified.json of a hit: cached %v from %q", r.Cached, r.CachedFrom)
	}
	if out, _ := verify("--fresh"); isCached(out) {
		t.Errorf("--fresh used the cache")
	}
	if out, _ := verify("--unsafe-no-sandbox"); isCached(out) {
		t.Errorf("--unsafe-no-sandbox used the cache")
	}
	// A changed proof (a comment) is a different input.
	if err := os.WriteFile(proof, append(append([]byte{}, src...), "\n-- edited\n"...), 0o644); err != nil {
		t.Fatal(err)
	}
	if out, _ := verify(); isCached(out) {
		t.Errorf("an edited proof hit the cache")
	}
	if out, _ := verify(); !isCached(out) {
		t.Errorf("the edited proof was not recorded")
	}
	// A tampered entry (its report altered without the HMAC) is ignored. This proof's entries are
	// the ones whose report has its SHA-256 (the shared test cache holds other runs' entries).
	edited, _ := os.ReadFile(proof)
	wantSha := `"proofSha256":"` + sha256Hex(edited) + `"`
	var entries []string
	_ = filepath.WalkDir(resultCacheDir(), func(p string, d os.DirEntry, err error) error {
		if err == nil && !d.IsDir() && strings.HasSuffix(p, ".json") {
			if b, err := os.ReadFile(p); err == nil && strings.Contains(string(b), wantSha) {
				entries = append(entries, p)
			}
		}
		return nil
	})
	if len(entries) == 0 {
		t.Fatal("no recorded entry for this proof")
	}
	for _, e := range entries {
		b, _ := os.ReadFile(e)
		tampered := strings.Replace(string(b), "x.toNat + y.toNat", "x.toNat * y.toNat", 1)
		if tampered == string(b) {
			t.Fatalf("entry %s does not contain the statement", e)
		}
		if err := os.WriteFile(e, []byte(tampered), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	out, _ := verify()
	if isCached(out) || strings.Contains(out, "x.toNat * y.toNat") || !strings.Contains(out, "x.toNat + y.toNat") {
		t.Errorf("a tampered entry was used:\n%s", out)
	}
}

// TestTreeShaUnambiguous: a file name that imitates a further "hash  path" line of the old
// encoding no longer collides with the two-file set (red team: a cached PASS served for a package
// that fails fresh); such names are rejected by the snapshot anyway.
func TestTreeShaUnambiguous(t *testing.T) {
	a := map[string][]byte{"x.lean": []byte("A"), "y.lean": []byte("B")}
	b := map[string][]byte{"x.lean\n" + sha256Hex([]byte("B")) + "  y.lean": []byte("A")}
	if treeSha(a) == treeSha(b) {
		t.Fatal("treeSha collides for different file sets")
	}
	if err := checkFileNames(b, "the package"); err == nil {
		t.Fatal("a file name with a newline was accepted")
	}
	if err := checkFileNames(a, "the package"); err != nil {
		t.Fatalf("plain names rejected: %v", err)
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "x.lean\n"+sha256Hex([]byte("B"))+"  y.lean"), []byte("A"), 0o644); err != nil {
		t.Skipf("cannot create the file: %v", err)
	}
	if _, err := snapshotDir(dir, nil); err == nil {
		t.Fatal("snapshotDir accepted a file name with a newline")
	}
}

// TestLakefileCacheable: configurations the result-cache key does not cover are not cached (red
// team: an absolute srcDir makes Lake read sources outside the snapshot).
func TestLakefileCacheable(t *testing.T) {
	ok := func(toml string) bool {
		return lakefileCacheable(map[string][]byte{"lakefile.toml": []byte(toml)}, "lakefile.toml")
	}
	base := "name = \"p\"\ndefaultTargets = [\"P\"]\n\n[[require]]\nname = \"janus\"\ngit = \"https://x\"\nrev = \"abc\"\n\n[[lean_lib]]\nname = \"P\"\n"
	if !ok(base) {
		t.Fatal("the plain package is not cacheable")
	}
	if !ok(base + "srcDir = \"src/lean\"\n") {
		t.Error("a relative srcDir inside the package must be cacheable")
	}
	if !ok(base + "roots = [\"A\", # c\n  'B',\n]\nprecompileModules = true\n\n[leanOptions]\npp.unicode.fun = true\nautoImplicit = false\nweak.linter.unusedVariables = false\nmaxHeartbeats = 400000\n") {
		t.Error("arrays, comments, booleans and leanOptions must be cacheable")
	}
	for name, extra := range map[string]string{
		"absolute srcDir":        "srcDir = \"/tmp/ext\"\n",
		"escaping srcDir":        "srcDir = \"../ext\"\n",
		"nested escape":          "srcDir = \"a/../../ext\"\n",
		"home srcDir":            "srcDir = \"~/x\"\n",
		"escaped srcDir":         "srcDir = \"a\\\\x2e\\\\x2e\"\n",
		"plugin args":            "moreLeanArgs = [\"--load-dynlib=/tmp/p.so\"]\n",
		"weak args":              "weakLeanArgs = [\"-DfooBar\"]\n",
		"link args":              "moreLinkArgs = [\"-L/x\"]\n",
		"unknown table":          "\n[[input_file]]\nname = \"x\"\n",
		"inline srcDir":          "srcDir=\"/abs\"\n",
		"srcDir with tail":       "srcDir = \"/abs\" # c\n",
		"roots escape":           "roots = [\"«..».«..».X\"]\n",
		"roots slash":            "roots = [\"A/B\"]\n",
		"roots backslash":        "roots = ['A\\B']\n",
		"roots dotdot":           "roots = [\"A..B\"]\n",
		"globs escape":           "globs = [\"«..».+\"]\n",
		"libName slash":          "libName = \"a/b\"\n",
		"root slash":             "root = \"../X\"\n",
		"exeName guille":         "exeName = \"«x»\"\n",
		"debug option":           "\n[leanOptions]\ndebug.skipKernelTC = true\n",
		"plugin option":          "\n[leanOptions]\nplugin = \"x\"\n",
		"trace output":           "\n[leanOptions]\ntrace.profiler.output = \"/tmp/x\"\n",
		"quoted key":             "\"srcDir\" = \"/abs/ext\"\n",
		"literal key":            "'srcDir' = '/abs/ext'\n",
		"quoted link args":       "\"moreLinkArgs\" = [\"-L/x\"]\n",
		"literal string":         "srcDir = '/abs/ext'\n",
		"dotted key":             "a.b = 1\n",
		"inline table":           "x = { srcDir = \"/abs\" }\n",
		"multiline string":       "description = \"\"\"\nx\n\"\"\"\n",
		"CR line endings":        "srcDir = \"/abs/ext\"\r\n",
		"CR only":                "name = \"x\"\rsrcDir = \"/abs\"\n",
		"array then quoted key":  "roots = [\n  \"A\",\n]\n\"srcDir\" = \"/abs\"\n",
		"srcDir array":           "srcDir = [\"a\"]\n",
		"srcDir dot dot":         "srcDir = \"a/..\"\n",
		"unterminated":           "srcDir = \"a\n",
		"header trailing":        "[[lean_lib]] x\n",
		"single bracket require": "[require]\nname = \"x\"\n",
	} {
		if ok(base + extra) {
			t.Errorf("%s was cacheable", name)
		}
	}
	for _, f := range []string{"examples/consumer/lakefile.toml"} {
		// the consumer example's plain lakefile is cacheable
		if b, err := os.ReadFile(filepath.Join(repoRoot, f)); err == nil && !lakefileCacheable(map[string][]byte{"lakefile.toml": b}, "lakefile.toml") {
			t.Errorf("%s is not cacheable", f)
		}
	}
	if lakefileCacheable(map[string][]byte{"lakefile.lean": []byte("import Lake\n")}, "lakefile.lean") {
		t.Error("a lakefile.lean package was cacheable")
	}
	if lakefileCacheable(map[string][]byte{}, "lakefile.toml") {
		t.Error("a missing lakefile was cacheable")
	}
}

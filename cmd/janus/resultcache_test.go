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
	t.Parallel()
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
		code, out, stderr := runJanus(t, append([]string{"verify", add, "--proof", proof, "--janus-root", repoRoot}, extra...)...)
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

package main

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// hmacHexV1 is the v0.2.0 entry MAC (key and olean hash only).
func hmacHexV1(hk []byte, key, sha string) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-olean-entry-v1\n%q\n%q\n", key, sha)
	return hex.EncodeToString(m.Sum(nil))
}

// Red-team of the olean store entry v2 (PR #1): every tampering of a stored module is a miss, never a hit.
func TestOleanStoreRedTeam(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	if err := os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700); err != nil {
		t.Fatal(err)
	}
	hk, err := resultHMACKey()
	if err != nil {
		t.Fatal(err)
	}
	k1, k2 := strings.Repeat("d", 64), strings.Repeat("e", 64)
	mk := func(tag string) modParts {
		return modParts{".olean": []byte("o" + tag), ".olean.server": []byte("s" + tag), ".olean.private": []byte("p" + tag), ".ir": []byte("i" + tag)}
	}
	dir := func(k string) string { return filepath.Join(oleanStoreDir(), k[:2]) }
	fresh := func() {
		os.RemoveAll(oleanStoreDir())
		oleanStorePut(k1, mk("1"))
		oleanStorePut(k2, mk("2"))
		if d, ok := oleanStoreGet(k1); !ok || len(d) != 4 {
			t.Fatal("setup: entry not served")
		}
	}
	readEntry := func(k string) oleanEntry {
		var e oleanEntry
		b, err := os.ReadFile(filepath.Join(dir(k), k+".json"))
		if err != nil || json.Unmarshal(b, &e) != nil {
			t.Fatal(err)
		}
		return e
	}
	writeEntry := func(k string, e oleanEntry) {
		b, _ := json.Marshal(e)
		if err := os.WriteFile(filepath.Join(dir(k), k+".json"), b, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	miss := func(name, k string) {
		t.Helper()
		if d, ok := oleanStoreGet(k); ok {
			t.Errorf("%s: served %v", name, d)
		}
	}
	part := func(k, ext string) string { return filepath.Join(dir(k), k+ext) }
	copyPart := func(from, to, ext string) {
		b, _ := os.ReadFile(part(from, ext))
		os.WriteFile(part(to, ext), b, 0o600)
	}

	fresh()
	copyPart(k2, k1, ".olean.server")
	miss("server part swapped from another entry", k1)

	fresh()
	copyPart(k2, k1, ".olean")
	miss("olean swapped from another entry", k1)

	fresh()
	copyPart(k2, k1, ".ir")
	miss("ir swapped", k1)

	fresh()
	e := readEntry(k1)
	e.Parts[".olean.extra"] = sha256Hex([]byte("x")) // not in the MAC: only the part-count check sees it
	writeEntry(k1, e)
	os.WriteFile(part(k1, ".olean.extra"), []byte("x"), 0o600)
	miss("unknown-extension part", k1)

	fresh()
	os.Remove(part(k1, ".olean.server"))
	miss("part file dropped, entry kept", k1)

	fresh()
	os.Remove(part(k1, ".olean"))
	miss("olean dropped", k1)

	// an entry with a valid MAC whose Parts lack .olean (a module with only its other parts)
	fresh()
	sp := modParts{".olean.server": []byte("s1"), ".ir": []byte("i1")}
	shas := map[string]string{".olean.server": sha256Hex(sp[".olean.server"]), ".ir": sha256Hex(sp[".ir"])}
	writeEntry(k1, oleanEntry{Key: k1, Sha: sp.digest(), Parts: shas, MAC: oleanMAC(hk, k1, shas)})
	miss("authentic entry without an olean part", k1)

	// a v1-format entry with a valid v1 MAC and a matching olean file
	fresh()
	o := []byte("o1")
	writeEntry(k1, oleanEntry{Key: k1, Sha: sha256Hex(o), MAC: hmacHexV1(hk, k1, sha256Hex(o))})
	os.WriteFile(part(k1, ".olean"), o, 0o600)
	miss("v1 entry with a valid v1 MAC", k1)

	// the Sha field is not in the MAC: a tampered Sha with intact parts must still be a miss
	fresh()
	e = readEntry(k1)
	e.Sha = sha256Hex([]byte("tampered"))
	writeEntry(k1, e)
	miss("tampered Sha", k1)

	// a part replaced by a symlink to identical content
	fresh()
	real := filepath.Join(t.TempDir(), "real")
	os.WriteFile(real, []byte("s1"), 0o600)
	os.Remove(part(k1, ".olean.server"))
	if err := os.Symlink(real, part(k1, ".olean.server")); err != nil {
		t.Fatal(err)
	}
	miss("symlinked part", k1)

	// the olean itself a symlink
	fresh()
	real2 := filepath.Join(t.TempDir(), "real2")
	os.WriteFile(real2, []byte("o1"), 0o600)
	os.Remove(part(k1, ".olean"))
	os.Symlink(real2, part(k1, ".olean"))
	miss("symlinked olean", k1)

	// a truncated (empty) server part
	fresh()
	os.WriteFile(part(k1, ".olean.server"), nil, 0o600)
	miss("emptied server part", k1)

	// an entry whose recorded server hash is the empty string
	fresh()
	e = readEntry(k1)
	e.Parts[".olean.server"] = ""
	writeEntry(k1, e)
	miss("empty recorded hash", k1)

	// a part dropped from Parts without a fresh MAC
	fresh()
	os.Remove(part(k1, ".ir"))
	e = readEntry(k1)
	delete(e.Parts, ".ir")
	writeEntry(k1, e)
	miss("part dropped from Parts without re-MAC", k1)

	// a known part added to an entry that does not have it (Parts, file and Sha all agree; only the MAC does not)
	fresh()
	os.Remove(part(k1, ".ir"))
	os.Remove(part(k1, ".olean.private"))
	oleanStorePut(k1, modParts{".olean": []byte("o1"), ".olean.server": []byte("s1")})
	if _, ok := oleanStoreGet(k1); !ok {
		t.Fatal("setup: two-part entry not served")
	}
	e = readEntry(k1)
	e.Parts[".ir"] = sha256Hex([]byte("evil"))
	os.WriteFile(part(k1, ".ir"), []byte("evil"), 0o600)
	e.Sha = (modParts{".olean": []byte("o1"), ".olean.server": []byte("s1"), ".ir": []byte("evil")}).digest()
	writeEntry(k1, e)
	miss("known part added without re-MAC", k1)

	// the entry and part files of another key relabelled to this key (only the MAC binds the key besides e.Key)
	fresh()
	e = readEntry(k2)
	e.Key = k1
	writeEntry(k1, e)
	for _, ext := range moduleDataExts {
		copyPart(k2, k1, ext)
	}
	miss("entry and parts of another key relabelled", k1)

	// put refuses an empty olean
	os.RemoveAll(oleanStoreDir())
	oleanStorePut(k1, modParts{".olean": nil, ".olean.server": []byte("s")})
	miss("empty olean stored", k1)

	// an entry of another key under this key's name
	fresh()
	b, _ := os.ReadFile(part(k2, ".json"))
	os.WriteFile(part(k1, ".json"), b, 0o600)
	miss("entry of another key", k1)
}

// A module's digest must separate olean-only from multi-part modules and bind each part to its extension.
func TestModPartsDigestBinding(t *testing.T) {
	a := modParts{".olean": []byte("o"), ".olean.server": []byte("s")}
	b := modParts{".olean": []byte("o"), ".olean.private": []byte("s")}
	if a.digest() == b.digest() {
		t.Error("the digest does not bind a part to its extension")
	}
	if a.digest() == (modParts{".olean": []byte("o")}).digest() {
		t.Error("an added part does not change the digest")
	}
	if a.digest() == (modParts{".olean": []byte("o"), ".olean.server": []byte("s"), ".ir": nil}).digest() {
		t.Error("an added empty part does not change the digest")
	}
}

// write over an existing module removes parts the new data lacks, and fails closed on a directory in the way.
func TestModPartsWriteStale(t *testing.T) {
	d := t.TempDir()
	target := filepath.Join(d, "M.olean")
	full := modParts{".olean": []byte("o"), ".olean.server": []byte("s"), ".olean.private": []byte("p"), ".ir": []byte("i")}
	if err := full.write(target); err != nil {
		t.Fatal(err)
	}
	if err := (modParts{".olean": []byte("o2")}).write(target); err != nil {
		t.Fatal(err)
	}
	for _, ext := range []string{".olean.server", ".olean.private", ".ir"} {
		if _, err := os.Lstat(filepath.Join(d, "M"+ext)); !os.IsNotExist(err) {
			t.Errorf("stale %s kept", ext)
		}
	}
	if b, _ := os.ReadFile(target); string(b) != "o2" {
		t.Errorf("olean = %q", b)
	}
}

// parseImports against Lean 4.34.1's own header parser (`lean --deps`, checked by hand: see the report).
func TestParseImportsAgainstLean(t *testing.T) {
	for _, c := range []struct {
		src  string
		want []string
		ok   bool
	}{
		// Lean: `all` is a modifier even across a newline or a comment -> imports B
		{"module\nimport all\n  B\n", []string{"B"}, true},
		{"module\nimport all /- c -/ B\n", []string{"B"}, true},
		{"module\nimport all -- c\n  JanusTrusted.X\n", []string{"JanusTrusted.X"}, true},
		{"module\nimport all B\n", []string{"B"}, true},
		{"module\nimport all all\n", []string{"all"}, true},
		// Lean 4.34.1 rejects `import all` with nothing after it (it panics): janus must not read a module `all`
		{"module\nimport all\n", nil, false},
		{"module\nimport all", nil, false},
		{"module\nimport all\nimport B\n", nil, false},
		// comments and newlines between modifiers and `import`
		{"module\npublic /- c -/ meta -- e\n import A\n", []string{"A"}, true},
		{"module\npublic\n\nmeta\nimport A", []string{"A"}, true},
		{"module\npublic section\nimport A", nil, true},
		// `import` at EOF
		{"module\nimport", nil, false},
		{"module\npublic import", nil, false},
		// a doc comment ends the header
		{"module\n/-- d -/ import A", nil, true},
		{"import A\n/-! d -/\nimport B", []string{"A"}, true},
	} {
		got, ok := parseImports([]byte(c.src))
		if ok != c.ok || strings.Join(got, ",") != strings.Join(c.want, ",") {
			t.Errorf("parseImports(%q) = %v, %v; want %v, %v", c.src, got, ok, c.want, c.ok)
		}
	}
}

// readModParts refuses an empty olean and an unreadable part (not only a missing one).
func TestReadModPartsRefusals(t *testing.T) {
	d := t.TempDir()
	os.WriteFile(filepath.Join(d, "e.olean"), nil, 0o600)
	os.WriteFile(filepath.Join(d, "e.olean.server"), []byte("s"), 0o600)
	if _, err := readModParts(filepath.Join(d, "e.olean")); err == nil {
		t.Error("an empty olean was accepted")
	}
	os.WriteFile(filepath.Join(d, "f.olean"), []byte("o"), 0o600)
	os.Mkdir(filepath.Join(d, "f.olean.server"), 0o700) // a part that cannot be read as a file
	if _, err := readModParts(filepath.Join(d, "f.olean")); err == nil {
		t.Error("an unreadable server part was skipped")
	}
}

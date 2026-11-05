package main

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"sync"
	"testing"
)

// ---- the module store (modstore.go): keys, entries, tampering, concurrent writers ----

var msFw = map[string][]byte{
	"Janus.lean":           []byte("import Janus.Core\nimport Janus.Other\n"),
	"Janus/Core.lean":      []byte("import Init\n"),
	"Janus/Other.lean":     []byte("import Janus.Core\n"),
	"Janus/Unrelated.lean": []byte("import Janus.Core\n"),
	"Extracted.lean":       []byte("import Janus.Core\n"),
	"JanusTrusted.lean":    []byte("import Janus.Core\n"),
}

func msWant(extra string) pins {
	return pins{"Janus/Core.olean": "c1", "Janus/Other.olean": "o1", "Janus/Unrelated.olean": "u1" + extra,
		"Extracted.olean": "e" + extra, "JanusTrusted.olean": "t", "Janus.olean": "j"}
}

func msPkg(files map[string]string) (*consumerPkg, *consumerWS) {
	f := map[string][]byte{"lakefile.toml": []byte("name = \"pkg\"\ndefaultTargets = [\"Pkg\"]\n\n[[lean_lib]]\nname = \"Pkg\"\n")}
	for k, v := range files {
		f[k] = []byte(v)
	}
	return &consumerPkg{Files: f, Lakefile: "lakefile.toml"}, &consumerWS{Root: "/ws/root", DepsDir: "/ws/deps"}
}

var msMods = map[string]string{
	"Pkg/A.lean": "import Janus.Other\n",
	"Pkg/B.lean": "import Pkg.A\nimport Lean\n",
	"Pkg/C.lean": "import Extracted\nimport Pkg.A\n", // touches Extracted
	"Pkg/D.lean": "import Pkg.C\n",                   // through C
	"Pkg/E.lean": "import Init\n",
	"Pkg/F.lean": "import JanusTrusted\n",
	"Pkg/G.lean": "import Mathlib.Tactic\n", // a module nobody provides
}

func TestModstoreEligibility(t *testing.T) {
	pkg, ws := msPkg(msMods)
	got := storeModules("tc1", ws, pkg, msFw, msWant(""))
	var names []string
	for m := range got {
		names = append(names, m)
	}
	for _, want := range []string{"Pkg.A", "Pkg.B", "Pkg.E"} {
		if got[want] == nil {
			t.Errorf("%s not covered (covered %v)", want, names)
		}
	}
	for _, never := range []string{"Pkg.C", "Pkg.D", "Pkg.F", "Pkg.G"} {
		if got[never] != nil {
			t.Errorf("%s is covered but its closure touches Extracted/JanusTrusted or is unknown", never)
		}
	}
}

func TestModstoreKeys(t *testing.T) {
	base := func(files map[string]string, tc string, want pins, fw map[string][]byte) map[string]*storeMod {
		pkg, ws := msPkg(files)
		return storeModules(tc, ws, pkg, fw, want)
	}
	k0 := base(msMods, "tc1", msWant(""), msFw)
	// a different extraction (the Extracted olean differs), a framework module outside the closure: same keys
	k1 := base(msMods, "tc1", msWant("-other-extraction"), msFw)
	for _, m := range []string{"Pkg.A", "Pkg.B", "Pkg.E"} {
		if k0[m].key != k1[m].key {
			t.Errorf("%s: the key changed with an unrelated framework module/Extracted", m)
		}
	}
	// a changed import closure (a framework module the module reads): new key, transitively
	w := msWant("")
	w["Janus/Core.olean"] = "c2"
	k2 := base(msMods, "tc1", w, msFw)
	if k2["Pkg.A"].key == k0["Pkg.A"].key || k2["Pkg.B"].key == k0["Pkg.B"].key {
		t.Error("the key ignores the olean of a framework module in the closure")
	}
	if k2["Pkg.E"].key != k0["Pkg.E"].key {
		t.Error("E reads no framework module, its key must not change")
	}
	// a key-collision attempt through a changed import: B's source now imports another module
	files := map[string]string{}
	for k, v := range msMods {
		files[k] = v
	}
	files["Pkg/B.lean"] = "import Pkg.E\nimport Lean\n"
	k3 := base(files, "tc1", msWant(""), msFw)
	if k3["Pkg.B"].key == k0["Pkg.B"].key {
		t.Error("B imports another module and has the same key")
	}
	// the imported module's source changed: the importer's key changes (its closure is in the key)
	files = map[string]string{}
	for k, v := range msMods {
		files[k] = v
	}
	files["Pkg/A.lean"] = "import Janus.Other\n-- changed\n"
	k4 := base(files, "tc1", msWant(""), msFw)
	if k4["Pkg.A"].key == k0["Pkg.A"].key || k4["Pkg.B"].key == k0["Pkg.B"].key {
		t.Error("a changed source did not change the keys of the module and its importer")
	}
	// a dependency's revision in the lakefile (a framework bump) is not a build setting
	pkgR, wsR := msPkg(msMods)
	pkgR.Files["lakefile.toml"] = append(pkgR.Files["lakefile.toml"], []byte("\n[[require]]\nname = \"janus\"\ngit = \"/x\"\nrev = \"abc\"\n")...)
	kR := storeModules("tc1", wsR, pkgR, msFw, msWant(""))
	if kR["Pkg.A"].key != k0["Pkg.A"].key {
		t.Error("a [[require]] entry changed the key")
	}
	// ... but a Lean option is
	pkgO, wsO := msPkg(msMods)
	pkgO.Files["lakefile.toml"] = append(pkgO.Files["lakefile.toml"], []byte("\n[leanOptions]\nautoImplicit = false\n")...)
	if kO := storeModules("tc1", wsO, pkgO, msFw, msWant("")); kO == nil || kO["Pkg.A"].key == k0["Pkg.A"].key {
		t.Errorf("a leanOption did not change the key (%v)", kO)
	}
	// another toolchain
	k5 := base(msMods, "tc2", msWant(""), msFw)
	if k5["Pkg.A"].key == k0["Pkg.A"].key {
		t.Error("the key ignores the toolchain")
	}
}

func msBuild(t *testing.T, dir, mod, olean string) {
	t.Helper()
	for _, f := range []string{"lib/lean/%s.olean", "lib/lean/%s.ilean", "lib/lean/%s.trace", "ir/%s.c"} {
		p := filepath.Join(dir, filepath.FromSlash(strings.Replace(f, "%s", mod, 1)))
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			t.Fatal(err)
		}
		content := f + olean
		if err := os.WriteFile(p, []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}

func TestModstoreRoundTripAndTamper(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	src, dst := t.TempDir(), t.TempDir()
	msBuild(t, src, "Pkg/A", "v1")
	key := strings.Repeat("ab", 32)
	if !modstorePut(key, src, "Pkg/A") {
		t.Fatal("put failed")
	}
	if !modstoreLoad(key, dst) {
		t.Fatal("load missed")
	}
	got, _ := os.ReadFile(filepath.Join(dst, "lib", "lean", "Pkg", "A.olean"))
	if string(got) != "lib/lean/%s.oleanv1" {
		t.Fatalf("loaded %q", got)
	}
	// tamper: one byte of the stored olean changes, the key and manifest stay: rejected
	entry := modstoreEntry(key)
	if err := os.WriteFile(filepath.Join(entry, "lib", "lean", "Pkg", "A.olean"), []byte("forged"), 0o644); err != nil {
		t.Fatal(err)
	}
	dst2 := t.TempDir()
	if modstoreLoad(key, dst2) {
		t.Fatal("a tampered olean was accepted")
	}
	_ = filepath.WalkDir(dst2, func(p string, d os.DirEntry, err error) error {
		if err == nil && !d.IsDir() {
			t.Errorf("a partial copy of a rejected entry stayed: %s", p)
		}
		return nil
	})
	// the manifest forged to match the forged file: the MAC (hidden key) rejects it
	mp := filepath.Join(entry, "manifest.json")
	m, _ := readModstoreManifest(entry, key)
	_ = m
	b, _ := os.ReadFile(mp)
	forged := strings.Replace(string(b), `"files":{`, `"files":{"lib/lean/Pkg/A.olean":"`+sha256Hex([]byte("forged"))+`",`, 1)
	_ = os.WriteFile(mp, []byte(forged), 0o644)
	if modstoreLoad(key, t.TempDir()) {
		t.Fatal("a forged manifest was accepted")
	}
	// a path escaping the build directory in a manifest is not followed
	if modstoreRelOK("lib/lean/../../../etc/x.olean") || modstoreRelOK("/abs.olean") || modstoreRelOK("other/A.olean") {
		t.Fatal("modstoreRelOK accepts a path outside lib/lean and ir")
	}
	// put replaces the damaged entry (moved aside), and never an intact one
	msBuild(t, src, "Pkg/A", "v2")
	if !modstorePut(key, src, "Pkg/A") {
		t.Fatal("put over a damaged entry failed")
	}
	dst3 := t.TempDir()
	if !modstoreLoad(key, dst3) {
		t.Fatal("the replaced entry misses")
	}
	got, _ = os.ReadFile(filepath.Join(dst3, "lib", "lean", "Pkg", "A.olean"))
	if string(got) != "lib/lean/%s.oleanv2" {
		t.Fatalf("replaced entry holds %q", got)
	}
	msBuild(t, src, "Pkg/A", "v3")
	modstorePut(key, src, "Pkg/A") // intact entry: not overwritten
	dst4 := t.TempDir()
	modstoreLoad(key, dst4)
	got, _ = os.ReadFile(filepath.Join(dst4, "lib", "lean", "Pkg", "A.olean"))
	if string(got) != "lib/lean/%s.oleanv2" {
		t.Fatalf("an intact entry was overwritten: %q", got)
	}
}

// A store entry is found by its key only: the key of another toolchain is another entry.
func TestModstoreOtherToolchain(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	pkg, ws := msPkg(msMods)
	a := storeModules("toolchain-A", ws, pkg, msFw, msWant(""))["Pkg.E"]
	b := storeModules("toolchain-B", ws, pkg, msFw, msWant(""))["Pkg.E"]
	src := t.TempDir()
	msBuild(t, src, "Pkg/E", "A")
	if !modstorePut(a.key, src, "Pkg/E") {
		t.Fatal("put")
	}
	if modstoreLoad(b.key, t.TempDir()) {
		t.Fatal("an entry of another toolchain was loaded")
	}
	if !modstoreLoad(a.key, t.TempDir()) {
		t.Fatal("own entry misses")
	}
}

// Two writers of one key at once: one complete entry, never a mixture, nobody fails.
func TestModstoreConcurrentPut(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	key := strings.Repeat("cd", 32)
	var wg sync.WaitGroup
	srcs := make([]string, 8)
	for i := range srcs {
		srcs[i] = t.TempDir()
		msBuild(t, srcs[i], "Pkg/A", "same")
	}
	res := make([]bool, len(srcs))
	for i := range srcs {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			res[i] = modstorePut(key, srcs[i], "Pkg/A")
		}(i)
	}
	wg.Wait()
	for i, r := range res {
		if !r {
			t.Errorf("writer %d reported no entry", i)
		}
	}
	m, ok := readModstoreManifest(modstoreEntry(key), key)
	if !ok || !modstoreIntact(modstoreEntry(key), m) {
		t.Fatal("the entry after parallel puts is not authentic and intact")
	}
	ents, _ := os.ReadDir(filepath.Dir(modstoreEntry(key)))
	for _, e := range ents {
		if strings.HasPrefix(e.Name(), ".tmp-") || strings.HasPrefix(e.Name(), ".stale-") {
			t.Errorf("left %s behind", e.Name())
		}
	}
}

// seed and harvest on workspaces: a second workspace gets the modules the first built, and a module that
// imports Extracted is never stored.
func TestModstoreSeedHarvest(t *testing.T) {
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	pkg, ws1 := msPkg(msMods)
	ws1.Root, ws1.DepsDir = t.TempDir(), t.TempDir()
	mods1 := storeModules("tc1", ws1, pkg, msFw, msWant(""))
	b1 := filepath.Join(ws1.Root, ".lake", "build")
	for m := range msMods {
		msBuild(t, b1, "Pkg/"+strings.TrimSuffix(strings.TrimPrefix(m, "Pkg/"), ".lean"), "x")
	}
	if n := ws1.modstoreHarvest(mods1); n != 3 {
		t.Fatalf("harvested %d, want 3 (A, B, E)", n)
	}
	for _, never := range []string{"Pkg.C", "Pkg.D", "Pkg.F", "Pkg.G"} {
		if mods1[never] != nil {
			t.Fatalf("%s covered", never)
		}
	}
	// second extraction: a fresh workspace (Extracted differs), its build directory empty
	ws2 := &consumerWS{Root: t.TempDir(), DepsDir: t.TempDir()}
	mods2 := storeModules("tc1", ws2, pkg, msFw, msWant("-second"))
	seeded := ws2.modstoreSeed(mods2)
	if len(seeded) != 3 {
		t.Fatalf("seeded %v, want A, B, E", seeded)
	}
	for _, m := range []string{"A", "B", "E"} {
		if _, err := os.Stat(filepath.Join(ws2.Root, ".lake", "build", "lib", "lean", "Pkg", m+".olean")); err != nil {
			t.Errorf("%s not seeded", m)
		}
	}
	if _, err := os.Stat(filepath.Join(ws2.Root, ".lake", "build", "lib", "lean", "Pkg", "C.olean")); err == nil {
		t.Error("the Extracted-importing module was seeded")
	}
	// a module the workspace has is left alone
	if again := ws2.modstoreSeed(mods2); len(again) != 0 {
		t.Errorf("seeded again: %v", again)
	}
}

// TestConsumerModstoreAcrossFamilies: the same package at another path is another family (no sibling to
// seed from), yet its Extracted-free module comes from the module store instead of a build, for a
// different extraction; the module that imports Extracted is rebuilt and is not in the store.
func TestConsumerModstoreAcrossFamilies(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	verify := func(pkg, outdir, proof, thm string) *verifiedReport {
		code, out, stderr := runJanus(t, "verify", outdir, "--proof", filepath.Join(pkg, proof), "--proof-root", pkg, "--theorem", thm)
		if code != 0 {
			t.Fatalf("%s: %d\n%s\n%s", thm, code, out, stderr)
		}
		return readReport(t, outdir)
	}
	add := mustExtract(t, "example.com/basic.Add")
	max := mustExtract(t, "example.com/basic.Max")
	pkg1 := consumerCopy(t, "toml")
	verify(pkg1, add, "ConsumerExample/Add.lean", "ConsumerExample.Add.correctness")
	// another path, another family; another extraction
	pkg2 := consumerCopy(t, "toml")
	r := verify(pkg2, max, "ConsumerExample/Max.lean", "ConsumerExample.Max.correctness")
	if !strings.Contains(" "+strings.Join(r.Consumer.FromStore, " ")+" ", " ConsumerExample.Spec ") {
		t.Errorf("Spec not from the store: from store %v, rebuilt %v", r.Consumer.FromStore, r.Consumer.Rebuilt)
	}
	if strings.Contains(" "+strings.Join(r.Consumer.Rebuilt, " ")+" ", " ConsumerExample.Spec ") {
		t.Errorf("Spec was rebuilt: %v", r.Consumer.Rebuilt)
	}
	if !reflect.DeepEqual(r.Consumer.Rebuilt, []string{"ConsumerExample.Max", "Extracted"}) {
		t.Errorf("rebuilt %v, want the module that imports Extracted and Extracted", r.Consumer.Rebuilt)
	}
	// red team: one byte of the stored olean of Spec is changed (same key, same manifest): a third family
	// does not take it, rebuilds the module, and the verification still passes
	var hit []string
	filepath.WalkDir(modstoreDir(), func(p string, d os.DirEntry, err error) error {
		if err == nil && !d.IsDir() && strings.HasSuffix(p, "/lib/lean/ConsumerExample/Spec.olean") {
			hit = append(hit, p)
		}
		return nil
	})
	if len(hit) == 0 {
		t.Fatal("no stored Spec olean")
	}
	for _, p := range hit {
		b, _ := os.ReadFile(p)
		b[len(b)/2] ^= 0xff
		if err := os.WriteFile(p, b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	pkg3 := consumerCopy(t, "toml")
	add2 := mustExtract(t, "example.com/basic.Add")
	r3 := verify(pkg3, add2, "ConsumerExample/Add.lean", "ConsumerExample.Add.correctness")
	if strings.Contains(" "+strings.Join(r3.Consumer.FromStore, " ")+" ", " ConsumerExample.Spec ") {
		t.Errorf("a tampered store entry was used: %v", r3.Consumer.FromStore)
	}
	if !strings.Contains(" "+strings.Join(r3.Consumer.Rebuilt, " ")+" ", " ConsumerExample.Spec ") {
		t.Errorf("Spec not rebuilt after the tampered entry: %v", r3.Consumer.Rebuilt)
	}
	// no store entry holds a module whose closure touches Extracted
	filepath.WalkDir(modstoreDir(), func(p string, d os.DirEntry, err error) error {
		if err == nil && !d.IsDir() && strings.HasSuffix(p, "/ConsumerExample/Max.olean") {
			t.Errorf("a module importing Extracted was stored: %s", p)
		}
		return nil
	})
}

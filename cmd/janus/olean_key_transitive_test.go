package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestOleanStoreKeyTransitive: a change deep in a module's import closure must invalidate the
// stored olean of every module above it, even when an intermediate module's olean comes out
// byte-identical. Deep defines a reducible Prop; Mid only names it (its olean does not depend
// on Deep's body); Add's theorem unfolds it. Changing Deep's body must recompile Add, not reuse
// its stored olean (before the fix the store key covered only the direct imports' olean bytes,
// so Add's stale olean was reused and the kernel replay rejected it).
func TestOleanStoreKeyTransitive(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	add := mustExtract(t, "example.com/basic.Add")
	pkg := consumerCopy(t, "toml")
	dir := filepath.Join(pkg, "ConsumerExample")
	writeFile(t, filepath.Join(dir, "Deep.lean"), "@[reducible] def ConsumerExample.deepP : Prop := 0 < 1\n")
	writeFile(t, filepath.Join(dir, "Mid.lean"), "import ConsumerExample.Deep\n@[reducible] def ConsumerExample.midP : Prop := ConsumerExample.deepP\n")
	asrc := filepath.Join(dir, "Add.lean")
	b, err := os.ReadFile(asrc)
	if err != nil {
		t.Fatal(err)
	}
	ab := strings.Replace(string(b), "import ConsumerExample.Spec\n", "import ConsumerExample.Spec\nimport ConsumerExample.Mid\n", 1)
	// a proof that unfolds Deep's body through Mid: holds for both bodies, so Add compiles either way,
	// but its proof term depends on the body (Props are erased from compiled code, so Mid's olean
	// does not)
	ab += "\ntheorem ConsumerExample.deepOK : ConsumerExample.midP := by decide\n"
	if ab == string(b) {
		t.Fatal("cannot edit Add.lean")
	}
	writeFile(t, asrc, ab)
	verify := func() {
		t.Helper()
		code, out, stderr := runJanus(t, "verify", add, "--proof", asrc, "--proof-root", pkg,
			"--theorem", "ConsumerExample.Add.correctness", "--theorem", "ConsumerExample.Add.Witness.nonvacuous", "--no-result-cache")
		if code != 0 {
			t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
		}
	}
	verify()
	before := ownCompiles.Load()
	verify()
	if n := ownCompiles.Load() - before; n != 0 {
		t.Fatalf("an unchanged package compiled %d module(s) again", n)
	}
	// change only Deep's body
	writeFile(t, filepath.Join(dir, "Deep.lean"), "@[reducible] def ConsumerExample.deepP : Prop := 0 < 2\n")
	before = ownCompiles.Load()
	verify()
	// Deep, Mid and Add must all be compiled again (Mid's olean is byte-identical, so before the fix
	// only Deep and Mid were, and Add's stale olean was reused)
	if n := ownCompiles.Load() - before; n != 3 {
		t.Errorf("after a change of Deep, %d module(s) were compiled again, want 3 (Deep, Mid, Add)", n)
	}
}

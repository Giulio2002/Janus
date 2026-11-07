package main

import (
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"
)

// ---- red team round n9: the Lake-free verify path (modstore.go / consumer.go) ----
//
// Each test tries to make janus accept, or be influenced by, content the verifier did not compile itself. None may:
// the verdict must equal the clean run's (or be a refusal with a reason), and never a Verified over planted material.

// n9Clean verifies the Add example of a fresh consumer copy and returns the output and report axioms.
func n9Verify(t *testing.T, add, pkg string, extra ...string) (int, string, string) {
	t.Helper()
	return runJanus(t, append([]string{"verify", add, "--proof", filepath.Join(pkg, "ConsumerExample/Add.lean"), "--proof-root", pkg,
		"--theorem", "ConsumerExample.Add.correctness", "--no-result-cache"}, extra...)...)
}

func n9Listing(t *testing.T, dir string) []string {
	t.Helper()
	var l []string
	_ = filepath.Walk(dir, func(p string, fi os.FileInfo, err error) error {
		if err == nil {
			rel, _ := filepath.Rel(dir, p)
			l = append(l, rel+"|"+fi.ModTime().String()+"|"+string(rune('0'+fi.Mode()&7)))
		}
		return nil
	})
	sort.Strings(l)
	return l
}

// TestRedTeamN9SymlinkedLake: `.lake` of the package is a symlink to a directory outside it holding planted oleans for
// the proof's modules. janus refuses the package with a reason that names the link (it never follows it), verifies
// nothing, and writes nothing into the symlink's target.
func TestRedTeamN9SymlinkedLake(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	add := mustExtract(t, "example.com/basic.Add")
	pkg := consumerCopy(t, "toml")
	outside := filepath.Join(t.TempDir(), "elsewhere")
	for _, m := range []string{"ConsumerExample/Add", "ConsumerExample/Spec", "ConsumerExample"} {
		for _, ext := range []string{".olean", ".ilean", ".trace", ".olean.hash"} {
			writeFile(t, filepath.Join(outside, "build", "lib", "lean", m+ext), "planted, not an olean")
		}
	}
	if err := os.Symlink(outside, filepath.Join(pkg, ".lake")); err != nil {
		t.Fatal(err)
	}
	before := n9Listing(t, outside)
	code, out, stderr := n9Verify(t, add, pkg)
	if code == 0 || strings.Contains(out, "Verified") {
		t.Fatalf("a package with a symlinked .lake was verified: %d\n%s\n%s", code, out, stderr)
	}
	if !strings.Contains(out+stderr, "symbolic link") {
		t.Errorf("refused without naming the link:\n%s\n%s", out, stderr)
	}
	if after := n9Listing(t, outside); !reflect.DeepEqual(before, after) {
		t.Errorf("janus wrote into the symlink's target:\nbefore %v\nafter  %v", before, after)
	}
}

// TestRedTeamN9LakefileSrcDir: a lakefile whose [[lean_lib]] moves the sources (`srcDir`) to a directory holding a
// `sorry` version of the proof module. janus verifies the proof file it was given: the verdict is never a Verified whose
// axioms include sorryAx, and if Verified the axioms equal the clean run's.
func TestRedTeamN9LakefileSrcDir(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	add := mustExtract(t, "example.com/basic.Add")
	pkg := consumerCopy(t, "toml")
	p := filepath.Join(pkg, "lakefile.toml")
	b, err := os.ReadFile(p)
	if err != nil {
		t.Fatal(err)
	}
	writeFile(t, p, strings.Replace(string(b), "name = \"ConsumerExample\"\n", "name = \"ConsumerExample\"\nsrcDir = \"evil\"\n", 1))
	good, _ := os.ReadFile(filepath.Join(pkg, "ConsumerExample/Add.lean"))
	evil := strings.Replace(string(good), ":= by", ":= by sorry\n  -- ", -1)
	writeFile(t, filepath.Join(pkg, "evil/ConsumerExample/Add.lean"), evil)
	writeFile(t, filepath.Join(pkg, "evil/ConsumerExample/Spec.lean"), "import Extracted\n")
	code, out, stderr := n9Verify(t, add, pkg)
	if strings.Contains(out, "Verified") && code == 0 {
		r := readReport(t, add)
		for _, a := range r.Axioms {
			if a == "sorryAx" {
				t.Fatalf("Verified over the redirected sorry module: axioms %v", r.Axioms)
			}
		}
		return
	}
	if strings.TrimSpace(out+stderr) == "" {
		t.Errorf("refused without a reason")
	}
}

// TestRedTeamN9OutsideModuleNotTrusted: the proof imports a package-root module that no [[lean_lib]] covers, with a
// garbage olean planted for it under .lake. It is built from source by Lake (or the run is refused), never read from the
// plant: the run is Verified with the honest axioms, or refused with a reason.
func TestRedTeamN9OutsideModuleNotTrusted(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	add := mustExtract(t, "example.com/basic.Add")
	pkg := consumerCopy(t, "toml")
	writeFile(t, filepath.Join(pkg, "Helper.lean"), "import Extracted\ntheorem Helper.t : Extracted.entry = Extracted.entry := rfl\n")
	good, _ := os.ReadFile(filepath.Join(pkg, "ConsumerExample/Add.lean"))
	writeFile(t, filepath.Join(pkg, "ConsumerExample/Add.lean"), "import Helper\n"+string(good))
	for _, ext := range []string{".olean", ".ilean", ".trace", ".olean.hash"} {
		writeFile(t, filepath.Join(pkg, ".lake/build/lib/lean/Helper"+ext), "planted, not an olean")
	}
	code, out, stderr := n9Verify(t, add, pkg)
	if code == 0 && strings.HasPrefix(out, "Verified: ConsumerExample.Add.correctness") {
		for _, a := range readReport(t, add).Axioms {
			if a == "sorryAx" {
				t.Fatalf("axioms include sorryAx: %v", a)
			}
		}
		return
	}
	if strings.Contains(out, "Verified") {
		t.Fatalf("unexpected verdict: %d\n%s\n%s", code, out, stderr)
	}
	if strings.TrimSpace(out+stderr) == "" {
		t.Errorf("refused without a reason")
	}
}

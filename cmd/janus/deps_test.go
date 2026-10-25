package main

import (
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Tests for extra (non-janus) dependencies of consumer packages: a small spec library in a
// local git repository, required by its file:// URL and pinned to a commit. The rejection tests
// lay out .lake/packages and lake-manifest.json by hand (no Lean); TestConsumerExtraDep runs
// lake update and janus verify end to end. TestConsumerMathlib (JANUS_TEST_MATHLIB=1) does the
// same with Mathlib.

func gitIn(t *testing.T, dir string, args ...string) string {
	t.Helper()
	cmd := exec.Command("git", append([]string{"-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false",
		"-c", "init.defaultBranch=main", "-c", "protocol.file.allow=always"}, args...)...)
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("git %v: %v\n%s", args, err, out)
	}
	return strings.TrimSpace(string(out))
}

func needGit(t *testing.T) {
	t.Helper()
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git not installed")
	}
}

// The spec library: a word type, an operation, a lemma — and the things a statement must not
// use from a dependency: an instance that makes `*` mean `+`, an opaque and an axiom.
var wordLibFiles = map[string]string{
	"lakefile.toml": "name = \"wordlib\"\ndefaultTargets = [\"WordLib\"]\n\n[[lean_lib]]\nname = \"WordLib\"\n",
	"WordLib.lean":  "import WordLib.Basic\n",
	"WordLib/Basic.lean": `namespace WordLib

/-- A 64-bit machine word, as a spec library might define it. -/
structure Word where
  val : BitVec 64

/-- Wrapping addition of words. -/
def Word.add (a b : Word) : Word := ⟨a.val + b.val⟩

theorem Word.add_val (a b : Word) : (Word.add a b).val = a.val + b.val := rfl

/-- Misleading on purpose: ` + "`*`" + ` on words is addition. -/
instance : Mul Word := ⟨Word.add⟩

/-- An opaque constant (its value is hidden from the kernel). -/
opaque secret : BitVec 64

end WordLib
`,
	"WordLib/Bad.lean": "namespace WordLib\naxiom cheat : False\nend WordLib\n",
}

// makeWordLib creates the spec library as a git repository with one commit.
func makeWordLib(t *testing.T) (repo, rev string) {
	t.Helper()
	needGit(t)
	repo = filepath.Join(t.TempDir(), "wordlib")
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	for p, b := range wordLibFiles {
		writeFile(t, filepath.Join(repo, p), b)
	}
	writeFile(t, filepath.Join(repo, "lean-toolchain"), fw.Toolchain+"\n")
	writeFile(t, filepath.Join(repo, ".gitignore"), ".lake/\n")
	gitIn(t, repo, "init", "-q")
	gitIn(t, repo, "add", "-A")
	gitIn(t, repo, "commit", "-q", "-m", "wordlib")
	return repo, gitIn(t, repo, "rev-parse", "HEAD")
}

func manifestWith(name, janusDir string, extra ...map[string]any) string {
	pkgs := []map[string]any{{"type": "path", "scope": "", "name": "janus", "manifestFile": "lake-manifest.json",
		"inherited": false, "dir": janusDir, "configFile": "lakefile.toml"}}
	pkgs = append(pkgs, extra...)
	b, _ := json.MarshalIndent(map[string]any{"version": "1.2.0", "packagesDir": ".lake/packages", "name": name,
		"lakeDir": ".lake", "fixedToolchain": false, "packages": pkgs}, "", " ")
	return string(b)
}

func gitEntry(name, url, rev, inputRev string, inherited bool) map[string]any {
	return map[string]any{"type": "git", "scope": "", "name": name, "url": url, "rev": rev, "inputRev": inputRev,
		"subDir": nil, "manifestFile": "lake-manifest.json", "inherited": inherited, "configFile": "lakefile.toml"}
}

// Validation of extra dependencies that fails (or passes) before any Lean runs.
func TestExtraDepRejects(t *testing.T) {
	t.Setenv("JANUS_ROOT", "")
	fw, err := loadFramework("")
	if err != nil {
		t.Fatal(err)
	}
	janusDir := copyFramework(t, fw)
	repo, rev := makeWordLib(t)
	url := "file://" + filepath.ToSlash(repo)

	// setup lays out a consumer package with wordlib cloned into .lake/packages at rev.
	setup := func(t *testing.T, entry map[string]any) string {
		t.Helper()
		root := t.TempDir()
		writeFile(t, filepath.Join(root, "lakefile.toml"), "name = \"c\"\n[[lean_lib]]\nname = \"C\"\n")
		writeFile(t, filepath.Join(root, "lean-toolchain"), fw.Toolchain+"\n")
		writeFile(t, filepath.Join(root, "C/A.lean"), "import Extracted\nimport WordLib\n")
		writeFile(t, filepath.Join(root, "lake-manifest.json"), manifestWith("c", janusDir, entry))
		pkgs := filepath.Join(root, ".lake", "packages")
		os.MkdirAll(pkgs, 0o755)
		gitIn(t, pkgs, "clone", "-q", repo, "wordlib")
		gitIn(t, filepath.Join(pkgs, "wordlib"), "checkout", "-q", "--detach", rev)
		return root
	}
	expect := func(t *testing.T, root string, lo loadOpts, want string) {
		t.Helper()
		_, err := loadConsumer(root, fw, nil, lo)
		d, ok := err.(*diag)
		if !ok || !d.Invalid || d.Stage != "consumer manifest" || !strings.Contains(d.Msg, want) || d.Next == "" {
			t.Fatalf("want consumer manifest / %q, got %#v", want, err)
		}
	}

	t.Run("pinned and clean", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		// a build directory inside the dependency is not a modification
		writeFile(t, filepath.Join(root, ".lake/packages/wordlib/.lake/build/x.olean"), "")
		pkg, err := loadConsumer(root, fw, nil, loadOpts{})
		if err != nil {
			t.Fatal(err)
		}
		if len(pkg.Deps) != 1 {
			t.Fatalf("deps %+v", pkg.Deps)
		}
		d := pkg.Deps[0]
		if d.Info.Name != "wordlib" || d.Info.Type != "git" || d.Info.URL != url || d.Info.Rev != rev || d.Config != "lakefile.toml" ||
			d.Info.Sha256 != treeSha(d.Files) || d.Info.Files != len(d.Files) {
			t.Fatalf("dependency %+v", d.Info)
		}
		for _, f := range []string{"lakefile.toml", "lean-toolchain", "WordLib.lean", "WordLib/Basic.lean", ".gitignore"} {
			if _, ok := d.Files[f]; !ok {
				t.Errorf("snapshot lacks %s", f)
			}
		}
		for p := range pkg.Files {
			if strings.HasPrefix(p, ".lake") {
				t.Errorf("consumer snapshot includes %s", p)
			}
		}
	})
	t.Run("lakefile asks for a branch", func(t *testing.T) {
		expect(t, setup(t, gitEntry("wordlib", url, rev, "main", false)), loadOpts{}, "wordlib is not pinned to a full revision: the lakefile asks for main")
	})
	t.Run("manifest rev not a full revision", func(t *testing.T) {
		expect(t, setup(t, gitEntry("wordlib", url, rev[:12], rev[:12], false)), loadOpts{}, "not pinned to a full revision in lake-manifest.json")
	})
	t.Run("inherited requirement on a branch", func(t *testing.T) {
		// a dependency's own requirement may name a branch; the manifest's rev pins it
		if _, err := loadConsumer(setup(t, gitEntry("wordlib", url, rev, "main", true)), fw, nil, loadOpts{}); err != nil {
			t.Fatal(err)
		}
	})
	t.Run("not checked out", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		os.RemoveAll(filepath.Join(root, ".lake", "packages", "wordlib"))
		expect(t, root, loadOpts{}, "is not checked out")
	})
	t.Run("not a git checkout", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		os.RemoveAll(filepath.Join(root, ".lake", "packages", "wordlib", ".git"))
		expect(t, root, loadOpts{}, "is not a git checkout")
	})
	t.Run("modified file", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		writeFile(t, filepath.Join(root, ".lake/packages/wordlib/WordLib/Basic.lean"), "namespace WordLib\ndef x := 1\nend WordLib\n")
		expect(t, root, loadOpts{}, "has local modifications:\n  M WordLib/Basic.lean")
	})
	t.Run("untracked file", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		writeFile(t, filepath.Join(root, ".lake/packages/wordlib/WordLib/Extra.lean"), "def y := 2\n")
		expect(t, root, loadOpts{}, "?? WordLib/Extra.lean")
	})
	t.Run("modification hidden from git status", func(t *testing.T) {
		// assume-unchanged hides the edit from git status; the blob hashes still catch it
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		dep := filepath.Join(root, ".lake/packages/wordlib")
		gitIn(t, dep, "update-index", "--assume-unchanged", "WordLib/Basic.lean")
		writeFile(t, filepath.Join(dep, "WordLib/Basic.lean"), "namespace WordLib\ndef x := 1\nend WordLib\n")
		if st := gitIn(t, dep, "status", "--porcelain"); st != "" {
			t.Fatalf("status not hidden: %q", st)
		}
		expect(t, root, loadOpts{}, "differs from its pinned revision")
	})
	t.Run("checkout at another commit", func(t *testing.T) {
		root := setup(t, gitEntry("wordlib", url, rev, rev, false))
		dep := filepath.Join(root, ".lake/packages/wordlib")
		writeFile(t, filepath.Join(dep, "WordLib/More.lean"), "def z := 3\n")
		gitIn(t, dep, "add", "-A")
		gitIn(t, dep, "commit", "-q", "-m", "more")
		expect(t, root, loadOpts{}, "lake-manifest.json pins "+rev)
	})
	t.Run("path dependency", func(t *testing.T) {
		entry := map[string]any{"type": "path", "scope": "", "name": "wordlib", "manifestFile": "lake-manifest.json",
			"inherited": false, "dir": repo, "configFile": "lakefile.toml"}
		root := setup(t, entry)
		expect(t, root, loadOpts{}, "only janus may be a path dependency")
		pkg, err := loadConsumer(root, fw, nil, loadOpts{AllowPathDeps: true})
		if err != nil {
			t.Fatal(err)
		}
		if d := pkg.Deps[0].Info; d.Type != "path" || d.Dir != repo || d.Sha256 == "" {
			t.Fatalf("path dependency %+v", d)
		}
	})
}

// Module identity across the framework, consumer and dependency build directories.
func TestCheckModuleLayout(t *testing.T) {
	base := t.TempDir()
	lib := func(name string, mods ...string) string {
		d := filepath.Join(base, name)
		os.MkdirAll(d, 0o755)
		for _, m := range mods {
			writeFile(t, filepath.Join(d, filepath.FromSlash(strings.ReplaceAll(m, ".", "/"))+".olean"), "")
		}
		return d
	}
	janusFiles := map[string][]byte{"Janus.lean": nil, "Janus/Spec.lean": nil}
	tool := lib("toolchain", "Init", "Init.Prelude", "Lean")
	janus := lib("janus", "Janus", "Janus.Spec", "Extracted", "JanusTrusted")
	roots, err := checkModuleLayout(janus, janusFiles, lib("c-ok", "C", "C.A"), map[string]string{"wordlib": lib("w-ok", "WordLib", "WordLib.Basic")}, tool)
	if err != nil || strings.Join(roots, ",") != "WordLib" {
		t.Fatalf("good layout: %v %v", roots, err)
	}
	bad := []struct {
		name     string
		janus, c string
		dep      string
		want     string
	}{
		{"stray framework module", lib("janus-bad", "Janus", "Janus.Spec", "Janus.Evil"), lib("c1", "C"), lib("w1", "WordLib"), "Janus.Evil.olean, which is not a framework module"},
		{"consumer Janus module", janus, lib("c2", "C", "Janus.Evil"), lib("w2", "WordLib"), "root Janus is reserved"},
		{"dependency Lean module", janus, lib("c3", "C"), lib("w3", "WordLib", "Lean.Evil"), "root Lean is reserved"},
		{"shared root", janus, lib("c4", "C", "WordLib.Fake"), lib("w4", "WordLib"), "used by both the consumer package and the dependency wordlib"},
		{"duplicate module", janus, lib("c5", "C"), lib("w5", "WordLib", "C"), "provided by both the consumer package and the dependency wordlib"},
	}
	for _, c := range bad {
		_, err := checkModuleLayout(c.janus, janusFiles, c.c, map[string]string{"wordlib": c.dep}, tool)
		d, ok := err.(*diag)
		if !ok || d.Stage != "module identity" || !strings.Contains(d.Msg, c.want) {
			t.Errorf("%s: want %q, got %v", c.name, c.want, err)
		}
	}
}

// wordConsumer is a consumer package requiring janus (this checkout, by path) and wordlib
// (from git by its file:// URL at rev), resolved with lake update.
func wordConsumer(t *testing.T, repo, rev string) string {
	t.Helper()
	fw, _ := loadFramework("")
	pkg := filepath.Join(t.TempDir(), "wordproofs")
	writeFile(t, filepath.Join(pkg, "lean-toolchain"), fw.Toolchain+"\n")
	writeFile(t, filepath.Join(pkg, "lakefile.toml"), fmt.Sprintf(`name = "wordProofs"

[[require]]
name = "janus"
path = %s

[[require]]
name = "wordlib"
git = %s
rev = %q

[[lean_lib]]
name = "WordProofs"
`, tomlString(repoRoot), tomlString("file://"+filepath.ToSlash(repo)), rev))
	writeFile(t, filepath.Join(pkg, "WordProofs", "Add.lean"), `import Extracted
import WordLib
import WordLib.Bad

/-! example.com/basic.Add, specified with the external WordLib.Word type. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace WordProofs.Add

/-- The bridge: a register value as a library word. -/
def toWord (v : BitVec 64) : WordLib.Word := ⟨v⟩

theorem correctness : ∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = (WordLib.Word.add (toWord x) (toWord y)).val) := by
  intro x y ret hret s hs _
  janus_intro hs
  janus_run [toWord, WordLib.Word.add_val]

/-- The same theorem with the dependency's instance: it reads "x * y", it means x + y. -/
theorem smuggled : ∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = (toWord x * toWord y).val) := correctness

/-- A dependency's opaque in the statement. -/
theorem withOpaque : (∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = (WordLib.Word.add (toWord x) (toWord y)).val)) ∧ WordLib.secret = WordLib.secret :=
  ⟨correctness, rfl⟩

/-- A false claim proved with the dependency's axiom. -/
theorem viaAxiom : ∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = x * y) := WordLib.cheat.elim

end WordProofs.Add
`)
	lake, _ := findLake()
	cmd := exec.Command(lake, "update")
	cmd.Dir = pkg
	cmd.Env = append(os.Environ(), "GIT_CONFIG_COUNT=1", "GIT_CONFIG_KEY_0=protocol.file.allow", "GIT_CONFIG_VALUE_0=always")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("lake update: %v\n%s", err, out)
	}
	return pkg
}

// TestConsumerExtraDep: a proof whose statement uses a pinned git dependency's word type and
// lemma verifies; the dependency is recorded and replayed; its instance, opaque and axiom are
// rejected; a dirty checkout and a path dependency are rejected (the latter accepted and
// recorded with --allow-path-deps).
func TestConsumerExtraDep(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	repo, rev := makeWordLib(t)
	pkg := wordConsumer(t, repo, rev)
	add := mustExtract(t, "example.com/basic.Add")
	verify := func(thm string, extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", add, "--proof", filepath.Join(pkg, "WordProofs", "Add.lean"), "--proof-root", pkg,
			"--theorem", "WordProofs.Add." + thm}, extra...)...)
	}

	code, out, stderr := verify("correctness")
	if code != 0 || !strings.HasPrefix(out, "Verified: WordProofs.Add.correctness\n") {
		t.Fatalf("correctness: %d\n%s\n%s", code, out, stderr)
	}
	if !strings.Contains(out, "Dependency: wordlib git file://") || !strings.Contains(out, "WordLib.Word.add (def, WordLib.Basic)") {
		t.Errorf("verify output:\n%s", out)
	}
	r := readReport(t, add)
	if r.Consumer == nil || len(r.Consumer.Dependencies) != 1 {
		t.Fatalf("report %+v", r.Consumer)
	}
	d := r.Consumer.Dependencies[0]
	if d.Name != "wordlib" || d.Type != "git" || d.URL != "file://"+filepath.ToSlash(repo) || d.Rev != rev || d.Sha256 == "" {
		t.Errorf("dependency %+v", d)
	}
	want := map[string]bool{"WordLib.Word.add (def, WordLib.Basic)": false, "WordLib.Word.mk (constructor, WordLib.Basic)": false,
		"WordLib.Word.val (def, WordLib.Basic)": false}
	for _, c := range r.DependencyConsts {
		if _, ok := want[c]; ok {
			want[c] = true
		}
	}
	for c, seen := range want {
		if !seen {
			t.Errorf("dependencyConstants %v lacks %s", r.DependencyConsts, c)
		}
	}
	replayed := strings.Join(r.KernelReplay.Modules, " ")
	for _, m := range []string{"WordProofs.Add", "WordLib", "WordLib.Basic", "WordLib.Bad"} {
		if !strings.Contains(" "+replayed+" ", " "+m+" ") {
			t.Errorf("kernel replay %v lacks %s", r.KernelReplay.Modules, m)
		}
	}
	if !strings.Contains(r.Statement, "(WordProofs.Add.toWord x).add (WordProofs.Add.toWord y)).val") || strings.Contains(r.Statement, "*") {
		t.Errorf("statement %q", r.Statement)
	}
	if code, out, _ := runJanus(t, "explain", add); code != 0 || !strings.Contains(out, "Other dependencies (1)") ||
		!strings.Contains(out, "wordlib") || !strings.Contains(out, rev) || !strings.Contains(out, "WordLib.Word.add (def, WordLib.Basic)") {
		t.Errorf("explain:\n%s", out)
	}

	rejected := []struct{ thm, stage, want string }{
		{"smuggled", "statement identity", "an instance declared in dependency module WordLib.Basic"},
		{"withOpaque", "statement identity", "WordLib.secret, an opaque declared in dependency module WordLib.Basic"},
		{"viaAxiom", "axiom audit", "disallowed axioms: WordLib.cheat"},
	}
	for _, c := range rejected {
		t.Run(c.thm, func(t *testing.T) {
			code, out, stderr := verify(c.thm)
			if code != 1 || out != "" || !strings.Contains(stderr, c.want) || !strings.Contains(stderr, "Stage: "+c.stage) {
				t.Fatalf("got %d\n%s\n%s", code, out, stderr)
			}
			if _, err := os.Stat(filepath.Join(add, "verified.json")); err == nil {
				t.Fatal("verified.json survived a failed verification")
			}
		})
	}

	t.Run("dirty checkout", func(t *testing.T) {
		f := filepath.Join(pkg, ".lake", "packages", "wordlib", "WordLib", "Basic.lean")
		b, _ := os.ReadFile(f)
		os.WriteFile(f, append(b, []byte("\ntheorem extra : True := trivial\n")...), 0o644)
		defer os.WriteFile(f, b, 0o644)
		code, _, stderr := verify("correctness")
		if code != 1 || !strings.Contains(stderr, "Stage: consumer manifest") || !strings.Contains(stderr, "has local modifications") {
			t.Fatalf("got %d\n%s", code, stderr)
		}
	})

	t.Run("unpinned", func(t *testing.T) {
		gitIn(t, repo, "branch", "-f", "pinme", rev)
		lf := filepath.Join(pkg, "lakefile.toml")
		b, _ := os.ReadFile(lf)
		os.WriteFile(lf, []byte(strings.Replace(string(b), fmt.Sprintf("rev = %q", rev), `rev = "pinme"`, 1)), 0o644)
		defer os.WriteFile(lf, b, 0o644)
		lake, _ := findLake()
		cmd := exec.Command(lake, "update", "wordlib")
		cmd.Dir = pkg
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake update: %v\n%s", err, out)
		}
		code, _, stderr := verify("correctness")
		if code != 1 || !strings.Contains(stderr, "Stage: consumer manifest") || !strings.Contains(stderr, "the lakefile asks for pinme") {
			t.Fatalf("got %d\n%s", code, stderr)
		}
	})
}

// TestConsumerPathDep: the spec library as a path dependency is rejected unless
// --allow-path-deps, which records it as such.
func TestConsumerPathDep(t *testing.T) {
	defer parallel(t)()
	needLeanSlow(t)
	useTestCache(t)
	repo, rev := makeWordLib(t)
	pkg := wordConsumer(t, repo, rev)
	lf := filepath.Join(pkg, "lakefile.toml")
	b, _ := os.ReadFile(lf)
	s := strings.Replace(string(b), "git = "+tomlString("file://"+filepath.ToSlash(repo))+"\nrev = "+fmt.Sprintf("%q", rev), "path = "+tomlString(repo), 1)
	os.WriteFile(lf, []byte(s), 0o644)
	os.Remove(filepath.Join(pkg, "lake-manifest.json"))
	os.RemoveAll(filepath.Join(pkg, ".lake"))
	lake, _ := findLake()
	cmd := exec.Command(lake, "update")
	cmd.Dir = pkg
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("lake update: %v\n%s", err, out)
	}
	add := mustExtract(t, "example.com/basic.Add")
	args := []string{"verify", add, "--proof", filepath.Join(pkg, "WordProofs", "Add.lean"), "--proof-root", pkg, "--theorem", "WordProofs.Add.correctness"}
	if code, _, stderr := runJanus(t, args...); code != 1 || !strings.Contains(stderr, "only janus may be a path dependency") ||
		!strings.Contains(stderr, "--allow-path-deps") {
		t.Fatalf("path dependency accepted: %d %s", code, stderr)
	}
	code, out, stderr := runJanus(t, append(args, "--allow-path-deps")...)
	if code != 0 {
		t.Fatalf("--allow-path-deps: %d\n%s\n%s", code, out, stderr)
	}
	r := readReport(t, add)
	if !r.Consumer.AllowPathDeps || len(r.Consumer.Dependencies) != 1 || r.Consumer.Dependencies[0].Type != "path" ||
		r.Consumer.Dependencies[0].Dir != repo {
		t.Fatalf("report %+v", r.Consumer)
	}
	if _, out, _ := runJanus(t, "explain", add); !strings.Contains(out, "PATH DEPENDENCY accepted with --allow-path-deps") {
		t.Errorf("explain:\n%s", out)
	}
}

// TestConsumerMathlib verifies a proof whose statement uses a Mathlib definition, with Mathlib
// (and its own dependencies) pinned in the consumer package. Gated: JANUS_TEST_MATHLIB=1. It
// clones Mathlib (network) unless JANUS_TEST_MATHLIB_DIR names a directory to keep the package
// in across runs, and builds the needed part of Mathlib from source in the verification
// workspace (no cache download). JANUS_TEST_MATHLIB_REV overrides the revision (default: the
// v4.34.1 tag, matching the framework's toolchain).
func TestConsumerMathlib(t *testing.T) {
	defer parallel(t)()
	if os.Getenv("JANUS_TEST_MATHLIB") != "1" {
		t.Skip("set JANUS_TEST_MATHLIB=1 to build Mathlib and verify against it")
	}
	needLeanSlow(t)
	needGit(t)
	useTestCache(t)
	rev := os.Getenv("JANUS_TEST_MATHLIB_REV")
	if rev == "" {
		rev = "d13f23b723b8a846827a245b89c10fc7d3f11612" // tag v4.34.1
	}
	pkg := os.Getenv("JANUS_TEST_MATHLIB_DIR")
	if pkg == "" {
		pkg = filepath.Join(t.TempDir(), "mathlib-consumer")
	}
	fw, _ := loadFramework("")
	writeFile(t, filepath.Join(pkg, "lean-toolchain"), fw.Toolchain+"\n")
	writeFile(t, filepath.Join(pkg, "lakefile.toml"), fmt.Sprintf(`name = "mathlibConsumer"

[[require]]
name = "janus"
path = %s

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = %q

[[lean_lib]]
name = "MathlibConsumer"
`, tomlString(repoRoot), rev))
	writeFile(t, filepath.Join(pkg, "MathlibConsumer", "Add.lean"), `import Extracted
import Mathlib.Logic.Function.Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace MathlibConsumer.Add

/-- example.com/basic.Add returns x + y, and for each x that is a bijection in y
(Function.Bijective is a Mathlib definition). -/
theorem correctness :
    (∀ x y : BitVec 64, Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y)) ∧
    ∀ x : BitVec 64, Function.Bijective (fun y : BitVec 64 => x + y) := by
  refine ⟨?_, fun x => ⟨fun a b h => (BitVec.add_right_inj x).mp h,
    fun z => ⟨z - x, by simp only; rw [BitVec.add_comm]; exact BitVec.sub_add_cancel z x⟩⟩⟩
  intro x y ret hret s hs _
  janus_intro hs
  janus_run

end MathlibConsumer.Add
`)
	if _, err := os.Stat(filepath.Join(pkg, ".lake", "packages", "mathlib", ".git")); err != nil {
		lake, _ := findLake()
		cmd := exec.Command(lake, "update")
		cmd.Dir = pkg
		cmd.Env = append(os.Environ(), "MATHLIB_NO_CACHE_ON_UPDATE=1")
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("lake update: %v\n%s", err, out)
		}
	}
	add := mustExtract(t, "example.com/basic.Add")
	code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "MathlibConsumer", "Add.lean"), "--proof-root", pkg,
		"--theorem", "MathlibConsumer.Add.correctness")
	if code != 0 {
		t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
	}
	t.Log(out)
	r := readReport(t, add)
	names := map[string]bool{}
	for _, d := range r.Consumer.Dependencies {
		names[d.Name] = true
		if d.Type != "git" || !fullRevRE.MatchString(d.Rev) || d.URL == "" {
			t.Errorf("dependency %+v", d)
		}
	}
	for _, n := range []string{"mathlib", "batteries", "aesop", "Qq", "plausible", "proofwidgets", "LeanSearchClient", "importGraph"} {
		if !names[n] {
			t.Errorf("dependencies %v lack %s", names, n)
		}
	}
	found := false
	for _, c := range r.DependencyConsts {
		if strings.HasPrefix(c, "Function.Bijective (def, Mathlib.") {
			found = true
		}
	}
	if !found {
		t.Errorf("dependencyConstants %v", r.DependencyConsts)
	}
}

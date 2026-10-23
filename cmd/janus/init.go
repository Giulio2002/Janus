package main

// janus init: scaffold a consumer package.

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"unicode"
)

func cmdInit(args []string, stdout, stderr io.Writer) error {
	args, flags := takeBoolFlags(args, "no-update")
	pos, opts, err := parseArgs(args, "name", "rev", "janus-path", "janus-root")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 1 {
		return usageErr("init takes exactly one directory")
	}
	dir := pos[0]
	if opts["rev"] != "" && opts["janus-path"] != "" {
		return usageErr("pass either --rev or --janus-path, not both")
	}
	if entries, err := os.ReadDir(dir); err == nil && len(entries) > 0 {
		return &diag{Msg: fmt.Sprintf("%s exists and is not empty.", displayPath(dir)), Stage: "command line",
			Next: "Choose a new directory; janus init never overwrites files."}
	}
	abs, err := filepath.Abs(dir)
	if err != nil {
		return err
	}
	lib := opts["name"]
	if lib == "" {
		lib = libName(filepath.Base(abs))
	}
	if !regexp.MustCompile(`^[A-Z][A-Za-z0-9_]*$`).MatchString(lib) || lib == "Janus" || lib == "Extracted" {
		return usageErr("--name must be a capitalised Lean identifier other than Janus and Extracted, got %q", lib)
	}
	fw, err := loadFramework(opts["janus-root"])
	if err != nil {
		return err
	}

	// The requirement: a local checkout, or the git revision this binary carries.
	var require, depNote string
	if p := opts["janus-path"]; p != "" {
		pabs, err := filepath.Abs(p)
		if err != nil {
			return err
		}
		if err := compareFramework(pabs, fw); err != nil {
			return err
		}
		require = fmt.Sprintf("[[require]]\nname = \"janus\"\npath = %s\n", tomlString(filepath.ToSlash(pabs)))
		depNote = "path " + pabs
	} else {
		rev := opts["rev"]
		if rev == "" {
			rev, err = currentRevision(fw)
			if err != nil {
				return err
			}
		}
		if !fullRevRE.MatchString(rev) {
			return usageErr("--rev must be a full 40-hex commit, got %q", rev)
		}
		require = fmt.Sprintf("[[require]]\nname = \"janus\"\ngit = %s\nrev = %s\n", tomlString(janusRepoURL), tomlString(rev))
		depNote = janusRepoURL + " @ " + rev
	}

	pkgName := strings.ToLower(lib[:1]) + lib[1:]
	files := scaffold(lib, pkgName, require, fw.Toolchain)
	for name, body := range files {
		p := filepath.Join(abs, filepath.FromSlash(name))
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
			return &diag{Msg: fmt.Sprintf("Cannot write %s: %v", displayPath(p), err), Stage: "writing files"}
		}
	}
	fmt.Fprintf(stdout, "Created consumer package %s (library %s, janus %s)\n", displayPath(abs), lib, depNote)
	fmt.Fprintf(stdout, "  lakefile.toml, lean-toolchain (%s), %s.lean, %s/Spec.lean, %s/Add.lean, go/, README.md\n", fw.Toolchain, lib, lib, lib)
	if !flags["no-update"] {
		lake, err := findLake()
		if err != nil {
			return err
		}
		cmd := exec.Command(lake, "update")
		cmd.Dir = abs
		out, err := cmd.CombinedOutput()
		if err != nil {
			return &diag{Invalid: true, Msg: "lake update failed in " + displayPath(abs) + ": " + err.Error(), Stage: "consumer manifest",
				Next: "Fix the error and run lake update there (the files are written).", Details: string(out)}
		}
		fmt.Fprintln(stdout, "  Resolved dependencies: lake-manifest.json")
	} else {
		fmt.Fprintf(stdout, "  Next: cd %s && lake update\n", displayPath(abs))
	}
	fmt.Fprintf(stdout, "See %s for the first verification.\n", filepath.Join(displayPath(abs), "README.md"))
	return nil
}

// currentRevision is the full commit of the framework this binary carries.
func currentRevision(fw *framework) (string, error) {
	fi := fw.info()
	if fi.Modified {
		return "", &diag{Msg: "This janus was built from a modified checkout, so no Janus commit has its framework.", Stage: "framework identity",
			Next: "Pass --janus-path <your checkout> (a path dependency), or --rev with the commit you will verify against."}
	}
	if fullRevRE.MatchString(fi.Revision) {
		return fi.Revision, nil
	}
	if fi.Revision != "" {
		// A pseudo-version names 12 hex digits; find the full commit among the remote refs.
		out, err := exec.Command("git", "ls-remote", janusRepoURL).Output()
		if err == nil {
			for _, line := range strings.Split(string(out), "\n") {
				if f := strings.Fields(line); len(f) == 2 && strings.HasPrefix(f[0], fi.Revision) {
					return f[0], nil
				}
			}
		}
	}
	_, _, version := buildRevision()
	if regexp.MustCompile(`^v\d+\.\d+\.\d+$`).MatchString(version) {
		out, err := exec.Command("git", "ls-remote", janusRepoURL, "refs/tags/"+version+"^{}", "refs/tags/"+version).Output()
		if err == nil {
			if f := strings.Fields(string(out)); len(f) >= 2 && fullRevRE.MatchString(f[0]) {
				return f[0], nil
			}
		}
	}
	return "", &diag{Msg: "Cannot tell which Janus commit this binary carries.", Stage: "framework identity",
		Next: "Pass --rev <40-hex commit> (janus framework shows what is known), or --janus-path <checkout>."}
}

func libName(base string) string {
	var sb strings.Builder
	up := true
	for _, r := range base {
		if !unicode.IsLetter(r) && !unicode.IsDigit(r) {
			up = true
			continue
		}
		if r > unicode.MaxASCII {
			continue
		}
		if up {
			r = unicode.ToUpper(r)
			up = false
		}
		sb.WriteRune(r)
	}
	s := sb.String()
	if s == "" || unicode.IsDigit(rune(s[0])) {
		s = "Proofs" + s
	}
	return s
}

func tomlString(s string) string {
	b, _ := json.Marshal(s)
	return string(b)
}

func scaffold(lib, pkg, require, toolchain string) map[string]string {
	r := strings.NewReplacer("LIB", lib, "PKG", pkg, "REQUIRE", require)
	files := map[string]string{
		"lakefile.toml": r.Replace(`# A Lake package of proofs about compiled Go, checked by janus verify.
name = "PKG"
defaultTargets = ["LIB"]

REQUIRE
# LIB.lean imports the modules that do not depend on an extraction (specifications and
# lemmas), so lake build builds and checks them. Theorem modules import Extracted, which
# janus verify supplies from an artifact directory: check those with janus verify.
[[lean_lib]]
name = "LIB"
`),
		"lean-toolchain": toolchain + "\n",
		"LIB.lean": r.Replace(`-- The library root: extraction-independent modules (lake build builds these).
-- Theorem modules such as LIB.Add import Extracted and are checked by janus verify.
import LIB.Spec
`),
		"LIB/Spec.lean": r.Replace(`import Janus

/-! Specifications and lemmas shared by the theorem modules. This module does not import
Extracted, so janus reuses its build across extractions. -/

open Janus Janus.GoABI

namespace LIB

/-- What go/main.go's Add computes: wrapping 64-bit addition. -/
def addSpec (x y : BitVec 64) : BitVec 64 := x + y

/-- For all 64-bit x and y, a Go call of entry with x in X0 and y in X1 (everything else
arbitrary) returns, obeys the Go ABI, and leaves f x y in X0. -/
def Computes (p : Program) (entry : Nat) (f : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ x y : BitVec 64, Ensures p entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = f x y)

theorem addSpec_toNat (x y : BitVec 64) : (addSpec x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  BitVec.toNat_add x y

end LIB
`),
		"LIB/Add.lean": r.Replace(`import Extracted
import LIB.Spec

/-! The compiled arm64 code of main.Add (go/main.go) computes addSpec. Verify with

    janus verify artifacts/Add --proof LIB/Add.lean --proof-root . --theorem LIB.Add.correctness
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace LIB.Add

theorem correctness : Computes Extracted.program Extracted.entry addSpec := by
  intro x y ret hret s hs _
  janus_intro hs
  janus_run [addSpec]

end LIB.Add
`),
		"go/go.mod": "module example.com/hello\n\ngo 1.22\n",
		"go/main.go": `// A Go program with one function to verify. Build it for linux/arm64:
//
//	cd go && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o ../artifacts/hello-arm64 .
package main

import (
	"fmt"
	"os"
)

// Add is kept out of line so it is a function of its own in the binary.
//
//go:noinline
func Add(x, y uint64) uint64 { return x + y }

func main() {
	fmt.Println(Add(uint64(len(os.Args)), 41))
}
`,
		".gitignore": ".lake/\nartifacts/\n",
		"README.md": r.Replace("# LIB: proofs about compiled Go\n\n" +
			"A Lake package of Lean proofs about Go machine code, checked by\n" +
			"[janus](https://github.com/Giulio2002/Janus). It depends on the `janus` Lean library\n" +
			"(see `lakefile.toml`); `janus verify` checks that the dependency is exactly the framework\n" +
			"the verifier carries.\n\n" +
			"## First verification\n\n" +
			"```sh\n" +
			"mkdir -p artifacts\n" +
			"(cd go && CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -o ../artifacts/hello-arm64 .)\n" +
			"janus list artifacts/hello-arm64 --filter main.\n" +
			"janus extract artifacts/hello-arm64 main.Add artifacts/Add\n" +
			"janus verify artifacts/Add --proof LIB/Add.lean --proof-root . --theorem LIB.Add.correctness\n" +
			"janus explain artifacts/Add/verified.json\n" +
			"```\n\n" +
			"## Layout\n\n" +
			"* `LIB/Spec.lean`: specifications and lemmas. It does not import `Extracted`; `lake build`\n" +
			"  builds it, and janus reuses its build for every extraction.\n" +
			"* `LIB/Add.lean`: the theorem about `main.Add`. It imports `Extracted`, the module\n" +
			"  `janus verify` generates from `artifacts/Add`; build it with `janus verify`, not `lake build`.\n" +
			"* Add a module per function. To check several at once, list them in a requests file for\n" +
			"  `janus verify-batch` (see docs/CONSUMERS.md in the Janus repository).\n\n" +
			"Do not add an `Extracted.lean` here: that module name is reserved for the extraction.\n" +
			"After changing the janus revision in `lakefile.toml`, run `lake update janus`.\n"),
	}
	out := map[string]string{}
	for k, v := range files {
		out[strings.ReplaceAll(k, "LIB", lib)] = v
	}
	return out
}

func cmdFramework(args []string, stdout, stderr io.Writer) error {
	args, flags := takeBoolFlags(args, "json")
	pos, opts, err := parseArgs(args, "janus-root")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 0 {
		return usageErr("framework takes no arguments")
	}
	fw, err := loadFramework(opts["janus-root"])
	if err != nil {
		return err
	}
	fi := fw.info()
	_, _, version := buildRevision()
	if flags["json"] {
		b, _ := json.MarshalIndent(map[string]any{"framework": fi, "goVersion": version, "cache": cacheRoot(),
			"repository": janusRepoURL, "extractorVersion": extractorVersion}, "", "  ")
		fmt.Fprintf(stdout, "%s\n", b)
		return nil
	}
	rev := fi.Revision
	switch {
	case rev == "":
		rev = "unknown (not built from a Janus checkout or module version)"
	case fi.Modified:
		rev += " (modified: no commit has exactly these sources)"
	}
	fmt.Fprintf(stdout, "Janus framework: %s\n", fw.Source)
	if fw.Dir != "" {
		fmt.Fprintf(stdout, "  Directory: %s\n", displayPath(fw.Dir))
	}
	fmt.Fprintf(stdout, "  SHA-256: %s (%d files: Janus.lean, Janus/**/*.lean, lakefile.toml, lean-toolchain)\n", fi.Sha256, fi.Files)
	fmt.Fprintf(stdout, "  Toolchain: %s\n", fi.Toolchain)
	fmt.Fprintf(stdout, "  Revision: %s\n", rev)
	if version != "" {
		fmt.Fprintf(stdout, "  Module version: %s\n", version)
	}
	fmt.Fprintf(stdout, "  Cache: %s\n", displayPath(cacheRoot()))
	fmt.Fprintf(stdout, "  Require it with: [[require]] name = \"janus\", git = %q, rev = <the revision>\n", janusRepoURL)
	return nil
}

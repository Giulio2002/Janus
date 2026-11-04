package main

import (
	"os"
	"path"
	"path/filepath"
	"strings"
	"testing"
)

// Round 15a (audit/round15a): Lake configurations whose sources or settings the result-cache key
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
		"srcDir in .lake":      "srcDir = \".lake/pre\"\n",
		"srcDir in .git":       "srcDir = \".git/x\"\n",
		"srcDir hidden":        "srcDir = \".hidden\"\n",
		"srcDir artifacts":     "srcDir = \"artifacts\"\n",
		"srcDir generated":     "srcDir = \"generated/x\"\n",
		"srcDir bin":           "srcDir = \"bin\"\n",
		"srcDir obj":           "srcDir = \"obj\"\n",
		"srcDir dotted deep":   "srcDir = \"a/.b/c\"\n",
		"srcDir leading dot/":  "srcDir = \"./.lake\"\n",
		"srcDir dir symlink":   "srcDir = \"a//.lake\"\n",
		"buildDir":             "buildDir = \"/x\"\n",
		"leanLibDir":           "leanLibDir = \"/x\"\n",
		"irDir":                "irDir = \"/x\"\n",
		"packagesDir":          "packagesDir = \"/x\"\n",
		"testDriver":           "testDriver = \"x\"\n",
		"extraDepTargets":      "extraDepTargets = [\"x\"]\n",
		"needs":                "needs = [\"x\"]\n",
		"nativeFacets":         "nativeFacets = [\"shared\"]\n",
		"leanArgs":             "leanArgs = [\"--load-dynlib=/x\"]\n",
		"server opts":          "moreServerOptions = [\"x\"]\n",
		"weak.debug":           "\n[leanOptions]\nweak.debug.skipKernelTC = true\n",
		"weak.weak.debug":      "\n[leanOptions]\nweak.weak.debug.skipKernelTC = true\n",
		"leanOptions plugin":   "\n[leanOptions]\nweak.plugin = 1\n",
		"leanOptions dotdot":   "\n[leanOptions]\npp..x = 1\nlinter..y=true\ndebug.x=1\n",
		"Lean.ofReduceBool":    "\n[leanOptions]\ndebug.moduleNameAtTimeout = false\n",
		"leanOptions as inline": "leanOptions = {debug.skipKernelTC = true}\n",
		"table in table":       "\n[lean_lib.x]\nname=\"y\"\n",
		"BOM":                  "\xef\xbb\xbf" + base,
		"NUL":                  "name = \"p\x00\"\n",
		"tab key":              "\tsrcDir\t=\t\"/abs\"\n",
		"lone CR in comment":   "# a\rsrcDir = \"/abs\"\n",
		"form feed":            "\fsrcDir = \"/abs\"\n",
		"vertical tab":         "\vsrcDir = \"/abs\"\n",
		"unicode key":          "srcDir = \"/abs\"\n",
		"line sep":             "name = \"a\" srcDir = \"/abs\"\n",
		"escaped quote":        "srcDir = \"a\\\"b\"\n",
		"literal backslash":    "srcDir = 'a\\..\\b'\n",
		"literal dotdot":       "srcDir = '..'\n",
		"srcDir empty":         "srcDir = \"\"\n",
		"srcDir colon":         "srcDir = \"a:b\"\n",
		"dotdot not first":     "srcDir = \"a/b/../../..\"\n",
		"integer srcDir":       "srcDir = 1\n",
		"bool srcDir":          "srcDir = true\n",
		"roots nul":            "roots = [\"A\x00\"]\n",
		"root ..":              "root = \"..\"\n",
		"name ..":              "name = \"..\"\n",
		"defaultTargets ..":    "defaultTargets = [\"../x\"]\n",
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

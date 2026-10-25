package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Round 10 F1: a --janus-root checkout is built in place. If its framework sources change while
// Lake builds (a `git checkout` in another terminal), the build must not be stamped as the build
// of the sources janus read at the start: the next run with those sources would reuse modules
// compiled from others and report the first framework's SHA-256.
func TestFrameworkSourcesChangeDuringBuild(t *testing.T) {
	dir := t.TempDir()
	write := func(rel, s string) {
		p := filepath.Join(dir, rel)
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(p, []byte(s), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	write("lakefile.toml", "name = \"janus\"\n")
	write("lake-manifest.json", "{}\n")
	write("lean-toolchain", "leanprover/lean4:v4.34.1\n")
	write("Janus.lean", "import Janus.A\n")
	write("Janus/A.lean", "def a : Nat := 5\n")
	// A fake lake: "builds" the library (one module, the auditor) and, meanwhile, the sources change.
	lake := filepath.Join(t.TempDir(), "lake")
	if err := os.WriteFile(lake, []byte(`#!/bin/sh
mkdir -p .lake/build/lib/lean .lake/build/bin
mkdir -p .lake/build/lib/lean/Janus
echo "def a : Nat := 6" > Janus/A.lean
cat Janus.lean > .lake/build/lib/lean/Janus.olean
cat Janus/A.lean > .lake/build/lib/lean/Janus/A.olean
echo exe > .lake/build/bin/janus-audit
`), 0o755); err != nil {
		t.Fatal(err)
	}
	fw, err := loadFramework(dir)
	if err != nil {
		t.Fatal(err)
	}
	lease, err := fw.acquire(dir, lake, nil, nil)
	if err == nil {
		lease.release()
		// the sources go back; janus reads them as the first framework again
		write("Janus/A.lean", "def a : Nat := 5\n")
		fw2, _ := loadFramework(dir)
		t.Fatalf("a build whose sources changed during Lake's run was accepted (ready for %s: %v)",
			fw2.Sha256[:12], fw2.ready(dir, nil))
	}
	if !strings.Contains(err.Error(), "changed") {
		t.Fatalf("unexpected error: %v", err)
	}
}

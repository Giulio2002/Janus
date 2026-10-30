package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The framework build runs `lake build` as a child while janus holds the framework lock EXCLUSIVELY. A lock-taking lake wrapper
// (scripts/lib/lanelake/lake) waits for that lock unless the child is told its parent holds it: leanRunner.heldFW puts it in
// JANUS_FRAMEWORK_LOCK_HELD_X; without heldFW the variable is absent, even if the caller's own environment has one (a claim is
// never inherited). scripts/lib/test-lanelake.sh checks the wrapper's side (it hangs without the claim and is not weakened).
func TestLeanRunnerClaimsTheFrameworkLockOnlyWhenHeld(t *testing.T) {
	dir := t.TempDir()
	fake := filepath.Join(dir, "lake")
	if err := os.WriteFile(fake, []byte("#!/bin/sh\necho \"claim=${JANUS_FRAMEWORK_LOCK_HELD_X:-none}\"\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_FRAMEWORK_LOCK_HELD_X", "/inherited/janus-framework.lock")
	out, err := (&leanRunner{lake: fake, root: dir}).run("build")
	if err != nil || strings.TrimSpace(out) != "claim=none" {
		t.Fatalf("without heldFW: %q %v (an inherited claim must be dropped)", out, err)
	}
	lock := filepath.Join(dir, ".lake", "janus-framework.lock")
	out, err = (&leanRunner{lake: fake, root: dir, heldFW: lock}).run("build")
	if err != nil || strings.TrimSpace(out) != "claim="+lock {
		t.Fatalf("with heldFW: %q %v", out, err)
	}
}

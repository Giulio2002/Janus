package main

import (
	"os/exec"
	"path/filepath"
	"testing"
)

// TestAuditRoundsPrebuiltGuard: no audit round runs `lake build` outside a JANUS_AUDIT_PREBUILT guard,
// and test/redteam/run-rounds.sh's shared build covers every target a round needs (scripts/lib/test-prebuilt-guard.sh).
func TestAuditRoundsPrebuiltGuard(t *testing.T) {
	out, err := exec.Command("bash", filepath.Join(repoRoot, "scripts", "lib", "test-prebuilt-guard.sh"), repoRoot).CombinedOutput()
	if err != nil {
		t.Fatalf("%v\n%s", err, out)
	}
}

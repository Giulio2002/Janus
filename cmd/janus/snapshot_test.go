package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The consumer run checks the snapshot taken at the start: editing a file under --proof-root during the run does not
// make the result "stale"; a source of the workspace copy that no longer matches the snapshot does.
func TestWsMatchesSnapshot(t *testing.T) {
	root := t.TempDir()
	files := map[string][]byte{"A.lean": []byte("a"), "B/C.lean": []byte("c")}
	for rel, b := range files {
		p := filepath.Join(root, filepath.FromSlash(rel))
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(p, b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if err := wsMatchesSnapshot(root, files); err != nil {
		t.Fatalf("unchanged workspace: %v", err)
	}
	// the live package (a different directory) changing is irrelevant: only the workspace copy is compared
	live := t.TempDir()
	if err := os.WriteFile(filepath.Join(live, "A.lean"), []byte("edited"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := wsMatchesSnapshot(root, files); err != nil {
		t.Fatalf("live edit must not matter: %v", err)
	}
	// a source rewritten in the workspace, or missing, is stale input
	if err := os.WriteFile(filepath.Join(root, "A.lean"), []byte("tampered"), 0o644); err != nil {
		t.Fatal(err)
	}
	err := wsMatchesSnapshot(root, files)
	if d, ok := err.(*diag); !ok || d.Stage != "stale input" || !strings.Contains(d.Msg, "workspace") {
		t.Fatalf("rewritten workspace source: %v", err)
	}
	if err := os.WriteFile(filepath.Join(root, "A.lean"), []byte("a"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.Remove(filepath.Join(root, "B", "C.lean")); err != nil {
		t.Fatal(err)
	}
	if err := wsMatchesSnapshot(root, files); err == nil {
		t.Fatal("missing workspace source accepted")
	}
}

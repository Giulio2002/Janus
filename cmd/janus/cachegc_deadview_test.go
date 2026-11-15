package main

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

// mkView makes a replay view in root/v1/run with a payload file, aged by age, locked (a live owner) or with a free .lock
// (a dead owner) or without a .lock (an older janus).
func mkView(t *testing.T, root, name string, age time.Duration, lock string) string {
	t.Helper()
	d := filepath.Join(root, "v1", "run", name)
	if err := os.MkdirAll(d, 0o755); err != nil {
		t.Fatal(err)
	}
	f := filepath.Join(d, "A.olean")
	if err := os.WriteFile(f, make([]byte, 1<<16), 0o644); err != nil {
		t.Fatal(err)
	}
	if lock != "" {
		if err := os.WriteFile(filepath.Join(d, viewLockName), nil, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	old := time.Now().Add(-age)
	for _, p := range []string{f, filepath.Join(d, viewLockName), d} {
		os.Chtimes(p, old, old)
	}
	return d
}

func TestGCReplayViews(t *testing.T) {
	f := newGCFixture(t)
	root := f.root
	live := mkView(t, root, "replay-view-live", time.Hour, "lock")
	dead := mkView(t, root, "replay-view-dead", time.Hour, "lock")
	fresh := mkView(t, root, "replay-view-fresh", time.Minute, "lock")
	legacy := mkView(t, root, "replay-view-legacy", time.Hour, "")
	oldLegacy := mkView(t, root, "replay-view-oldlegacy", 30*time.Hour, "")
	lk, err := lockFileMode(filepath.Join(live, viewLockName), false, true) // the live owner
	if err != nil {
		t.Fatal(err)
	}
	defer lk.unlock()
	s := scanCache(root)
	for _, e := range s.entries {
		e.inUse = e.probeInUse()
	}
	var dv int
	for _, e := range s.entries {
		if e.View && !e.inUse {
			dv++
		}
	}
	if dv != 2 { // dead and fresh (fresh is merely not yet collectable)
		t.Fatalf("dead views reported = %d, want 2", dv)
	}
	if _, err := collectCache(gcOptions{Max: -1, Grace: time.Minute, Now: time.Now(), All: true}, true); err != nil {
		t.Fatal(err)
	}
	exists := func(p string) bool { _, err := os.Lstat(p); return err == nil }
	if !exists(live) {
		t.Error("a view whose lock is held (live owner) was collected")
	}
	if exists(dead) {
		t.Error("a view whose lock is free and old enough (dead owner) was kept")
	}
	if !exists(fresh) {
		t.Error("a view younger than the dead-view grace was collected")
	}
	if !exists(legacy) {
		t.Error("a legacy view (no .lock) under 24 h was collected")
	}
	if exists(oldLegacy) {
		t.Error("a legacy view (no .lock) over 24 h was kept")
	}
}

package main

import (
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// TestVerifyStageBudgets: the fixed per-verification overhead of a tiny proof is bounded stage by
// stage (JANUS_TIMINGS), so a slowdown of the audit, the kernel replay, the workspace or the Lake
// calls is caught the day it lands (the audit once went from 1.3 s to 10 s through a call of
// `EnvironmentHeader.moduleNames` per constant, found only by accident). The budgets are about 2.5x
// the warm baselines measured on a loaded host (audit 1.3-1.7 s, replay 0.15 s, Lake build of an
// unchanged proof 0.2 s, workspace open 0.7 s, total 3.7 s); a stage is judged on the better of two
// unchanged verifications so that one noisy run does not fail it. Not parallel: it sets the
// environment of the verifier.
func TestVerifyStageBudgets(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	t.Setenv("JANUS_TIMINGS", "1")
	t.Setenv("JANUS_RESULT_CACHE", "off")
	pkg := consumerCopy(t, "toml")
	add := mustExtract(t, "example.com/basic.Add")
	line := regexp.MustCompile(`janus-timing: (.+?)\s+([0-9.]+)s\s*$`)
	verify := func() map[string]float64 {
		t.Helper()
		code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"),
			"--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness")
		if code != 0 {
			t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
		}
		st := map[string]float64{}
		for _, l := range strings.Split(stderr, "\n") {
			if m := line.FindStringSubmatch(l); m != nil {
				v, _ := strconv.ParseFloat(m[2], 64)
				name := m[1]
				if strings.HasPrefix(name, "ws: ") {
					name = "workspace open"
				}
				st[name] += v
			}
		}
		return st
	}
	verify() // builds the proof and fills every cache
	a, b := verify(), verify()
	best := map[string]float64{}
	for k, v := range a {
		best[k] = v
		if w, ok := b[k]; ok && w < v {
			best[k] = w
		}
	}
	// stage name prefix -> budget in seconds
	budgets := []struct {
		prefix string
		secs   float64
	}{
		{"theorem audit", 4.5},
		{"kernel replay", 2},
		{"lake build of the proof modules", 3},
		{"workspace open", 3},
		{"lake query", 2},
		{"total", 12},
	}
	for _, bd := range budgets {
		found := false
		for k, v := range best {
			if strings.HasPrefix(k, bd.prefix) {
				found = true
				if v > bd.secs {
					t.Errorf("stage %q took %.2f s (budget %.1f s); all stages: %v", k, v, bd.secs, best)
				}
			}
		}
		if !found {
			t.Errorf("no timing line for the stage %q (the timings changed?): %v", bd.prefix, best)
		}
	}
}

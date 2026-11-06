package main

import (
	"os"
	"path/filepath"
	"regexp"
	"runtime"
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
	line := regexp.MustCompile(`janus-timing: (.+?)\s+([0-9.]+)s(?:\s+cpu\s+([0-9.]+)s)?\s*$`)
	// verify returns each stage's wall seconds and CPU seconds (user+sys of janus and the children it waited for)
	verify := func() (wall, cpu map[string]float64) {
		t.Helper()
		code, out, stderr := runJanus(t, "verify", add, "--proof", filepath.Join(pkg, "ConsumerExample", "Add.lean"),
			"--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness")
		if code != 0 {
			t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
		}
		wall, cpu = map[string]float64{}, map[string]float64{}
		for _, l := range strings.Split(stderr, "\n") {
			if m := line.FindStringSubmatch(l); m != nil {
				name := m[1]
				if strings.HasPrefix(name, "ws: ") {
					name = "workspace open"
				}
				v, _ := strconv.ParseFloat(m[2], 64)
				wall[name] += v
				if m[3] != "" {
					c, _ := strconv.ParseFloat(m[3], 64)
					cpu[name] += c
				}
			}
		}
		return wall, cpu
	}
	verify() // builds the proof and fills every cache
	aw, ac := verify()
	bw, bc := verify()
	// a stage is judged on the better of the two unchanged verifications
	better := func(a, b map[string]float64) map[string]float64 {
		best := map[string]float64{}
		for k, v := range a {
			best[k] = v
			if w, ok := b[k]; ok && w < v {
				best[k] = w
			}
		}
		return best
	}
	bestWall, bestCPU := better(aw, bw), better(ac, bc)
	// stage name prefix -> budget in CPU seconds (about 3x the warm baselines: audit 0.71, replay 0.6, lake query 0.55,
	// workspace open 3.2 (it also holds the CPU of the concurrent replay), total 7.8; repeat runs agree within 2%)
	// stage name prefix -> budget in CPU seconds (user+sys of the stage's processes: it does not move with host load, so a
	// busy host cannot fail the guard, while a slowdown of the work does) and in wall seconds (the old budgets, enforced
	// only when the host is quiet: wall time under load measures the load)
	budgets := []struct {
		prefix    string
		cpu, wall float64
	}{
		{"theorem audit", 2.0, 4.5},
		{"kernel replay", 1.8, 2},
		{"lake build of the proof modules", 1.0, 3},
		{"workspace open", 9, 3},
		{"lake query", 1.6, 2},
		{"total", 22, 12},
	}
	quiet := hostQuiet()
	if !quiet {
		t.Logf("host is busy (load1 >= half the cores): the wall-time budgets are logged, not enforced; the CPU budgets are")
	}
	for _, bd := range budgets {
		found := false
		for k, v := range bestCPU {
			if strings.HasPrefix(k, bd.prefix) {
				found = true
				if v > bd.cpu {
					t.Errorf("stage %q used %.2f s of CPU (budget %.1f s); cpu: %v wall: %v", k, v, bd.cpu, bestCPU, bestWall)
				}
			}
		}
		for k, v := range bestWall {
			if strings.HasPrefix(k, bd.prefix) && v > bd.wall {
				if quiet {
					t.Errorf("stage %q took %.2f s of wall time on a quiet host (budget %.1f s); wall: %v", k, v, bd.wall, bestWall)
				} else {
					t.Logf("stage %q took %.2f s of wall time (budget %.1f s, not enforced on a busy host)", k, v, bd.wall)
				}
			}
		}
		if !found {
			t.Errorf("no CPU timing for the stage %q (the timings changed?): %v", bd.prefix, bestCPU)
		}
	}
	t.Logf("best CPU seconds per stage: %v", bestCPU)
	t.Logf("best wall seconds per stage: %v", bestWall)
}

// hostQuiet: the 1-minute load average is below half the cores.
func hostQuiet() bool {
	b, err := os.ReadFile("/proc/loadavg")
	if err != nil {
		return false
	}
	f := strings.Fields(string(b))
	if len(f) == 0 {
		return false
	}
	l, err := strconv.ParseFloat(f[0], 64)
	return err == nil && l < float64(runtime.NumCPU())/2
}

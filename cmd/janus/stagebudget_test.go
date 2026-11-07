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
	// A recompile of the proof in the sandbox (a comment added to it): its total CPU is budgeted too. JANUS_STAGEBUDGET_SPIN=1
	// adds a spinning #eval to that proof, the self-check that the guard fails on a slowdown inside the sandboxed compile.
	proofFile := filepath.Join(pkg, "ConsumerExample", "Add.lean")
	origProof, err := os.ReadFile(proofFile)
	if err != nil {
		t.Fatal(err)
	}
	edit := "\n-- stage budget recompile\n"
	if os.Getenv("JANUS_STAGEBUDGET_SPIN") != "" {
		edit = "\n#eval Id.run do\n  let mut x : Nat := 0\n  for i in [0:60000000] do\n    x := x + i % 7\n  return x\n" + edit
	}
	writeFile(t, proofFile, string(origProof)+edit)
	_, rc := verify()
	if recompile := rc["total"]; recompile > 22 {
		t.Errorf("a recompile of the proof used %.1f s of CPU (budget 22 s; baseline 11-15 s, idle to loaded)", recompile)
	} else {
		t.Logf("recompile of the proof: %.1f s of CPU", recompile)
	}
	// stage name prefix -> budget in CPU seconds (about 2.5x the warm baselines, with the CPU of the sandboxed Lean processes counted: audit 3.1-3.5, replay 0.7,
	// lake query 0.65, workspace open 3.4-3.9 (it also holds the CPU of the concurrent replay), total 11.2-11.9, recompile of the
	// proof 11-15; repeat runs agree within 6%)
	// stage name prefix -> budget in CPU seconds (user+sys of the stage's processes: it does not move with host load, so a
	// busy host cannot fail the guard, while a slowdown of the work does) and in wall seconds (the old budgets, enforced
	// only when the host is quiet: wall time under load measures the load)
	budgets := []struct {
		prefix    string
		cpu, wall float64
	}{
		{"theorem audit", 7.5, 4.5},
		{"kernel replay", 1.8, 2},
		{"lake build of the proof modules", 1.0, 3},
		{"workspace open", 9, 3},
		{"lake query", 1.6, 2},
		{"total", 26, 12},
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

// TestVerifyStageBudgetsSeesSandboxedCPU: the negative control of the CPU budgets. The CPU of Lean running in the sandbox (and in a
// systemd scope of the memory guard, where it is not a child janus waits for) must show in the CPU the timings report, or the
// guard would be blind to a slowdown of exactly the processes that do the work. The proof is edited twice (a comment, forcing a
// recompile in the sandbox), the second time with a spinning #eval added to it; the run's CPU must grow by the spin.
func TestVerifyStageBudgetsSeesSandboxedCPU(t *testing.T) {
	needLeanSlow(t)
	useTestCache(t)
	t.Setenv("JANUS_TIMINGS", "1")
	t.Setenv("JANUS_RESULT_CACHE", "off")
	pkg := consumerCopy(t, "toml")
	add := mustExtract(t, "example.com/basic.Add")
	proof := filepath.Join(pkg, "ConsumerExample", "Add.lean")
	orig, err := os.ReadFile(proof)
	if err != nil {
		t.Fatal(err)
	}
	total := regexp.MustCompile(`janus-timing: total\s+[0-9.]+s\s+cpu\s+([0-9.]+)s`)
	verify := func(src string) float64 {
		t.Helper()
		writeFile(t, proof, src)
		code, out, stderr := runJanus(t, "verify", add, "--proof", proof, "--proof-root", pkg, "--theorem", "ConsumerExample.Add.correctness")
		if code != 0 {
			t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
		}
		m := total.FindStringSubmatch(stderr)
		if m == nil {
			t.Fatalf("no total CPU in the timings:\n%s", stderr)
		}
		c, _ := strconv.ParseFloat(m[1], 64)
		return c
	}
	verify(string(orig)) // builds everything the runs below share
	plain := verify(string(orig) + "\n-- sandbox cpu control, plain\n")
	spin := verify(string(orig) + "\n#eval Id.run do\n  let mut x : Nat := 0\n  for i in [0:20000000] do\n    x := x + i % 7\n  return x\n-- sandbox cpu control, spin\n")
	t.Logf("CPU of a recompile of the proof: %.2f s plain, %.2f s with a spinning #eval", plain, spin)
	if spin-plain < 2 {
		t.Errorf("a spinning #eval in the sandboxed proof compile added only %.2f s of CPU (%.2f -> %.2f): the sandbox's CPU is not accounted", spin-plain, plain, spin)
	}
}

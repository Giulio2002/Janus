package main

// Opt-in per-stage timing of janus verify (JANUS_TIMINGS=1): one line per stage on stderr,
// "janus-timing: <stage> <wall>s  cpu <user+sys>s" (spans of concurrent stages: wall only), plus the total. Used to profile the verifier
// (docs/TESTING.md); it changes nothing else.

import (
	"fmt"
	"io"
	"os"
	"sync"
	"syscall"
	"time"
)

// cpuSeconds is the CPU time (user+sys) this process and the children it has waited for have used so far. A
// stage's CPU delta does not move with host load the way its wall time does (a regression in the work shows
// in both; a busy host only in the wall time), so the speed-regression guard (stagebudget_test.go) budgets it.
func cpuSeconds() float64 {
	var s, c syscall.Rusage
	if syscall.Getrusage(syscall.RUSAGE_SELF, &s) != nil || syscall.Getrusage(syscall.RUSAGE_CHILDREN, &c) != nil {
		return 0
	}
	tv := func(t syscall.Timeval) float64 { return float64(t.Sec) + float64(t.Usec)/1e6 }
	return tv(s.Utime) + tv(s.Stime) + tv(c.Utime) + tv(c.Stime)
}

type stageTimer struct {
	mu    sync.Mutex
	w     io.Writer
	start time.Time
	last  time.Time
	cpu0  float64 // cpuSeconds at start
	cpuL  float64 // cpuSeconds at the last mark
}

// newStageTimer returns a timer writing to w when JANUS_TIMINGS is set, else a no-op timer.
func newStageTimer(w io.Writer) *stageTimer {
	if os.Getenv("JANUS_TIMINGS") == "" || w == nil {
		return &stageTimer{}
	}
	now := time.Now()
	c := cpuSeconds()
	return &stageTimer{w: w, start: now, last: now, cpu0: c, cpuL: c}
}

// mark records that stage just ended (its time is measured from the previous mark).
func (t *stageTimer) mark(stage string) {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	now := time.Now()
	c := cpuSeconds()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs  cpu %7.3fs\n", stage, now.Sub(t.last).Seconds(), c-t.cpuL)
	t.last, t.cpuL = now, c
}

// span records a stage that ran for d (for stages timed separately, e.g. concurrently).
func (t *stageTimer) span(stage string, d time.Duration) {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs\n", stage, d.Seconds()) // concurrent: no CPU split
}

func (t *stageTimer) total() {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs  cpu %7.3fs\n", "total", time.Since(t.start).Seconds(), cpuSeconds()-t.cpu0)
}

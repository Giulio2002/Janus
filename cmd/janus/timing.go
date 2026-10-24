package main

// Opt-in per-stage timing of janus verify (JANUS_TIMINGS=1): one line per stage on stderr,
// "janus-timing: <stage> <seconds>s", plus the total. Used to profile the verifier
// (docs/TESTING.md); it changes nothing else.

import (
	"fmt"
	"io"
	"os"
	"sync"
	"time"
)

type stageTimer struct {
	mu    sync.Mutex
	w     io.Writer
	start time.Time
	last  time.Time
}

// newStageTimer returns a timer writing to w when JANUS_TIMINGS is set, else a no-op timer.
func newStageTimer(w io.Writer) *stageTimer {
	if os.Getenv("JANUS_TIMINGS") == "" || w == nil {
		return &stageTimer{}
	}
	now := time.Now()
	return &stageTimer{w: w, start: now, last: now}
}

// mark records that stage just ended (its time is measured from the previous mark).
func (t *stageTimer) mark(stage string) {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	now := time.Now()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs\n", stage, now.Sub(t.last).Seconds())
	t.last = now
}

// span records a stage that ran for d (for stages timed separately, e.g. concurrently).
func (t *stageTimer) span(stage string, d time.Duration) {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs\n", stage, d.Seconds())
}

func (t *stageTimer) total() {
	if t == nil || t.w == nil {
		return
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	fmt.Fprintf(t.w, "janus-timing: %-28s %7.3fs\n", "total", time.Since(t.start).Seconds())
}

package main

// Memory budget of the kernel replays of one janus process.
//
// A parallel framework replay runs several leanchecker workers, each in its own memory-guard
// cgroup with the per-job limit; but the whole janus process (and every other replay of the same
// process: tests run with -parallel, a gate shard sits in one enclosing cgroup) lives below an
// enclosing limit that those per-job limits do not add up to. So the budget is the EFFECTIVE
// limit (the smallest of the host's memory, every cgroup memory.max from this process's cgroup up
// to the root, and the guard's per-job limit), and half of it is shared by all replays of the
// process through one admission: a worker starts only when its estimated peak fits in what the
// running workers left, else it waits (more serial, never an OOM). A single worker larger than
// the whole budget is admitted alone.

import (
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
)

// Measured peaks of one leanchecker worker of the framework replay (RSS, GiB): 2.6 to 4.6 with 2
// threads, 6.6 to 9.2 with 4 threads; the estimates add margin.
const (
	workerPeak2Threads = 5 * gib
	workerPeak4Threads = 10 * gib
)

// workerPeak is the budget one worker with the given thread count asks for.
func workerPeak(threads int) int64 {
	if threads >= 4 {
		return workerPeak4Threads
	}
	return workerPeak2Threads
}

// cgroupChainLimit is the smallest memory.max from dir up to (excluding) root; 0 if none is set.
func cgroupChainLimit(dir, root string) int64 {
	var limit int64
	for p := filepath.Clean(dir); strings.HasPrefix(p, filepath.Clean(root)+"/") || p == filepath.Clean(root); p = filepath.Dir(p) {
		if b, err := os.ReadFile(filepath.Join(p, "memory.max")); err == nil {
			if v, err := strconv.ParseInt(strings.TrimSpace(string(b)), 10, 64); err == nil && v > 0 && (limit == 0 || v < limit) {
				limit = v
			}
		}
		if p == filepath.Clean(root) || p == "/" || p == "." {
			break
		}
	}
	return limit
}

// effectiveLimit combines the limits: the smallest positive one.
func effectiveLimit(memTotal, cgroupLimit, guardLimit int64) int64 {
	var out int64
	for _, v := range []int64{memTotal, cgroupLimit, guardLimit} {
		if v > 0 && (out == 0 || v < out) {
			out = v
		}
	}
	return out
}

// effectiveMemLimit is the effective limit of this process (0: unknown).
func effectiveMemLimit() int64 {
	var cg int64
	if d, err := ownCgroup(); err == nil {
		cg = cgroupChainLimit(d, cgroupRoot)
	}
	return effectiveLimit(memInfo("MemTotal"), cg, guardLimitBytes())
}

// replaySizing chooses the workers and threads of one framework replay for an effective limit:
// at most want workers, with 4 threads each only when the workers' estimates fit in half of the
// limit; else 2 threads and as many workers as fit (at least one).
func replaySizing(want int, effective, guard int64) (workers, threads int) {
	if n, err := strconv.Atoi(os.Getenv("JANUS_REPLAY_THREADS")); err == nil && n > 0 {
		threads = n
	}
	if want < 1 {
		want = 1
	}
	half := effective / 2
	if effective <= 0 {
		return want, replayThreadsOr(threads)
	}
	if threads == 0 {
		threads = replayThreads()
		if effective >= workerWideMinTotal && int64(want)*workerPeak4Threads <= half && (guard == 0 || guard >= workerWideThreadsMem) {
			threads = 4
		}
	}
	fit := int(half / workerPeak(threads))
	if fit < 1 {
		fit = 1
	}
	if want > fit {
		want = fit
	}
	return want, threads
}

func replayThreadsOr(n int) int {
	if n > 0 {
		return n
	}
	return replayThreads()
}

// memBudget is the process-wide admission.
type memBudget struct {
	mu    sync.Mutex
	cond  *sync.Cond
	total int64
	used  int64
}

func newMemBudget(total int64) *memBudget {
	b := &memBudget{total: total}
	b.cond = sync.NewCond(&b.mu)
	return b
}

// acquire waits until n bytes fit (a request above the total is admitted alone) and returns the
// release. A budget of 0 or less admits everything.
func (b *memBudget) acquire(n int64) func() {
	if b == nil || b.total <= 0 {
		return func() {}
	}
	if n > b.total {
		n = b.total
	}
	b.mu.Lock()
	for b.used+n > b.total {
		b.cond.Wait()
	}
	b.used += n
	b.mu.Unlock()
	return func() {
		b.mu.Lock()
		b.used -= n
		b.mu.Unlock()
		b.cond.Broadcast()
	}
}

var (
	globalBudgetOnce sync.Once
	globalBudget     *memBudget
)

// replayBudget is the budget shared by all replays of this process: half the effective limit.
func replayBudget() *memBudget {
	globalBudgetOnce.Do(func() { globalBudget = newMemBudget(effectiveMemLimit() / 2) })
	return globalBudget
}

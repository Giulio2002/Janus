package main

import (
	"strings"
	"sync"
	"testing"
	"time"
)

// Longest first under -parallel (docs/TESTING.md "Go tests"). The testing package starts the
// paused parallel tests in no particular order, so a long test that happens to start last
// stretches the whole run. Every parallel test of this package therefore starts with
//
//	defer parallel(t)()
//
// which calls t.Parallel and then waits for a slot of this package's own scheduler: at most
// testSlots tests (the -parallel value: memory- and core-bounded by defaultTestParallel, or the
// -parallel flag) hold a slot at once, and a free slot goes to the waiting test with the longest
// measured duration (testDurations, from `go test -json`; unknown tests count as 30 s). The slot
// is released when the test function returns, as the testing package releases its own: a test's
// parallel subtests then take slots of their own. testing's -parallel is raised so that it never
// binds before this scheduler does.

// testDurations are measured wall times (seconds, go test -json on the 48-core host, 2026-10-25;
// docs/TESTING.md) of the long tests; the order matters, not the exact values.
var testDurations = map[string]float64{
	"TestCacheGCConcurrentVerify": 250, "TestForeignFrameworkWriteDetected": 180, "TestR1ForgedFrameworkLemma": 116,
	"TestResultCache": 114, "TestConcurrentVerify": 90, "TestAmd64Blockers": 80, "TestSandboxRecorded": 70,
	"TestDataLarge": 68, "TestInstallOutsideRepo": 64, "TestR1FrameworkTamper": 64, "TestVerify": 60,
	"TestInlineInstanceRejected": 37, "TestVerifyBatch": 33, "TestConsumerExtraDep": 30, "TestBoundInstanceRejected": 28,
}

const unknownTestDuration = 30

var testSlots = 1 // set by TestMain

type testScheduler struct {
	mu      sync.Mutex
	cond    *sync.Cond
	running int
	waiting map[*testing.T]float64
	// lastArrival: a free slot is granted only once no test has asked for one for settle, so that
	// the tests the testing package releases together are all queued before the first grant.
	lastArrival time.Time
}

const settle = 100 * time.Millisecond

var sched = func() *testScheduler {
	s := &testScheduler{waiting: map[*testing.T]float64{}}
	s.cond = sync.NewCond(&s.mu)
	return s
}()

func testPriority(name string) float64 {
	if d, ok := testDurations[name]; ok {
		return d
	}
	// A subtest: rank it by its parent.
	if i := strings.IndexByte(name, '/'); i > 0 {
		if d, ok := testDurations[name[:i]]; ok {
			return d / 4
		}
	}
	return unknownTestDuration
}

// parallel marks t parallel and waits for a scheduler slot (longest first); the returned function
// releases the slot (defer it).
func parallel(t *testing.T) func() {
	t.Helper()
	t.Parallel()
	s := sched
	s.mu.Lock()
	s.waiting[t] = testPriority(t.Name())
	s.lastArrival = time.Now()
	time.AfterFunc(settle+5*time.Millisecond, func() { s.mu.Lock(); s.cond.Broadcast(); s.mu.Unlock() })
	for !(s.running < testSlots && s.best() == t && time.Since(s.lastArrival) >= settle) {
		s.cond.Wait()
	}
	delete(s.waiting, t)
	s.running++
	s.cond.Broadcast() // the next best may take another free slot
	s.mu.Unlock()
	return func() {
		s.mu.Lock()
		s.running--
		s.cond.Broadcast()
		s.mu.Unlock()
	}
}

// best is the waiting test with the highest priority (ties: the smallest name, for determinism).
func (s *testScheduler) best() *testing.T {
	var bt *testing.T
	bp := -1.0
	for t, p := range s.waiting {
		if p > bp || (p == bp && t.Name() < bt.Name()) {
			bt, bp = t, p
		}
	}
	return bt
}

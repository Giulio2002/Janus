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

// testDurations are measured wall times (seconds, go test -json -parallel 8 on the 48-core host at load 30-50, 2026-10-29, the largest of three runs;
// docs/TESTING.md) of the long tests; the order matters, not the exact values.
var testDurations = map[string]float64{
	"TestCacheGCConcurrentVerify": 744, "TestR1ForgedFrameworkLemma": 721, "TestResultCache": 421,
	"TestConcurrentVerify": 416, "TestBoundInstanceRejected": 269, "TestVerifyManyTheorems": 261,
	"TestVerifyManyCacheIsolation": 256, "TestConsumerVerify": 241, "TestRound6StatementNames": 228,
	"TestUnshareFallbackVerifies": 214, "TestVerifyManySharedFailure": 212, "TestSeedFramework": 206,
	"TestRoundTripRejectsAmbiguousPrint": 205, "TestMemGuardNormalVerify": 200, "TestMemguardShell": 199,
	"TestInitEndToEnd": 199, "TestMemGuardKillsHungryProof": 191, "TestHardeningB1": 184,
	"TestConsumerTwoCheckouts": 182, "TestConsumerVerifyMany": 180, "TestHardeningAttacks": 139,
	"TestConsumerPathDep": 139, "TestConsumerExtraDep": 135, "TestConsumerLakefileLean": 122, "TestVerifyBatch": 121,
	"TestConsumerGit": 119, "TestInlineInstanceRejected": 105, "TestConsumerAuditorLease": 100, "TestDataLarge": 91,
	"TestBlockers": 73, "TestBatchRequestErrors": 72, "TestVerify": 72, "TestForeignFrameworkWriteDetected": 50,
}

const unknownTestDuration = 30

var testSlots = 1 // set by TestMain

type testScheduler struct {
	mu      sync.Mutex
	cond    *sync.Cond
	running int
	waiting map[*testing.T]float64
	// holders: top-level tests that hold a slot. Their subtests run on the parent's slot instead
	// of waiting for one, because a parent that waits for its parallel subtests (a t.Run group)
	// while holding the last slot would otherwise deadlock (seen with testSlots = 1 under load).
	holders map[string]int
	// lastArrival: a free slot is granted only once no test has asked for one for settle, so that
	// the tests the testing package releases together are all queued before the first grant.
	lastArrival time.Time
}

const settle = 100 * time.Millisecond

var sched = func() *testScheduler {
	s := &testScheduler{waiting: map[*testing.T]float64{}, holders: map[string]int{}}
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
	if i := strings.IndexByte(t.Name(), '/'); i > 0 && s.holders[t.Name()[:i]] > 0 {
		// The top-level test holds a slot: run on it.
		s.mu.Unlock()
		return func() {}
	}
	s.waiting[t] = testPriority(t.Name())
	s.lastArrival = time.Now()
	time.AfterFunc(settle+5*time.Millisecond, func() { s.mu.Lock(); s.cond.Broadcast(); s.mu.Unlock() })
	for !(s.running < testSlots && s.best() == t && time.Since(s.lastArrival) >= settle) {
		s.cond.Wait()
	}
	delete(s.waiting, t)
	s.running++
	top := t.Name()
	if i := strings.IndexByte(top, '/'); i > 0 {
		top = top[:i]
	}
	s.holders[top]++
	s.cond.Broadcast() // the next best may take another free slot
	s.mu.Unlock()
	return func() {
		s.mu.Lock()
		s.holders[top]--
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

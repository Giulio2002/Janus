package main

import (
	"fmt"
	"os"
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
// measured duration (testDurations, measured; unknown tests count as 1 s). The slot
// is released when the test function returns, as the testing package releases its own: a test's
// parallel subtests then take slots of their own. testing's -parallel is raised so that it never
// binds before this scheduler does.

// testDurations are measured running times (seconds, 2026-10-31, go test -parallel 4 on the 48-core host at load 10-15) of the
// tests that take 1 s or more: for a test that calls parallel(t) the time it HELD its slot (JANUS_TEST_DURATIONS, recordHold
// below; `go test -v` reports a parallel test's duration including its wait for a slot, which is meaningless with few slots),
// for the others their -v duration. scripts/gotest-shards.sh balances the shards with them; the scheduler below orders by them.
// The order matters, not the exact values. To remeasure: JANUS_TEST_DURATIONS=file go test -v -parallel 4 ./cmd/janus (docs/TESTING.md).
// The four tests that dominate (a framework kernel replay each, ~210 s: TestCacheGCConcurrentVerify, TestR1ForgedFrameworkLemma,
// TestResultCache, TestConcurrentVerify) are about 1100 of the 2150 s of the whole package.
var testDurations = map[string]float64{
	"TestCacheGCConcurrentVerify": 469, "TestR1ForgedFrameworkLemma": 462, "TestResultCache": 232,
	"TestConcurrentVerify": 223, "TestRTBuildCacheScripts": 83, "TestSelfTestIsolation": 52, "TestR1FrameworkTamper": 45,
	"TestConsumerVerify": 43, "TestDataLarge": 37, "TestJ1PrestartMatchesClassic": 29, "TestVerifyBatch": 27,
	"TestConsumerTwoCheckouts": 27, "TestGateCancelLib": 26, "TestLaneLakeLib": 25, "TestConsumerVerifyMany": 24,
	"TestDagLib": 24, "TestInlineInstanceRejected": 22, "TestVerifierIdentityRealBuilds": 22, "TestConsumerExtraDep": 19,
	"TestBoundInstanceRejected": 18, "TestHardeningAttacks": 17, "TestForeignFrameworkWriteDetected": 15,
	"TestPoolLib": 13, "TestConsumerAuditorLease": 12, "TestRound6StatementNames": 12, "TestPoolMemLib": 12,
	"TestVerifyManyCacheIsolation": 12, "TestVerify": 12, "TestInitEndToEnd": 9, "TestConsumerPathDep": 9,
	"TestTreeLockLib": 9, "TestConsumerGit": 9, "TestConsumerLakefileLean": 8, "TestVerifyManyTheorems": 7,
	"TestSandboxRecorded": 6, "TestTheoremsLib": 6, "TestMemGuardNormalVerify": 6, "TestItemTimeoutLib": 5,
	"TestInstallOutsideRepo": 5, "TestMemguardShell": 5, "TestVerifierIdentityEmbeddedFiles": 4,
	"TestSoftFloatRuntimeAgreesWithIEEE": 4, "TestMemGuardKillsHungryProof": 3,
	"TestRT07AssemblyFileIsPartOfTheIdentity": 3, "TestRT08OverlayBuildDoesNotClaimTheOriginalIdentity": 3,
	"TestUnshareFallbackVerifies": 3, "TestSeedFramework": 2, "TestJ1ServeInitializerNotRun": 2,
	"TestRoundTripRejectsAmbiguousPrint": 2, "TestHardeningB1": 2, "TestRTIncrScripts": 2, "TestArtifactsLib": 2,
	"TestRT10ConcurrentWritersAndReadersNeverSeeAPartialRecord": 2, "TestFrameworkReplayOnce": 1,
	"TestVerifyManySharedFailure": 1, "TestVerifierIdentityGoSource": 1, "TestObjdumpCrossCheck": 1,
	"TestBuildModeMsan": 1,
}

const unknownTestDuration = 1

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
	held := time.Now()
	return func() {
		recordHold(t.Name(), time.Since(held))
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

// recordHold appends "name seconds" to the file named by JANUS_TEST_DURATIONS: the time a test held its slot, i.e. its
// own running time. `go test -v` reports a parallel test's duration INCLUDING the wait for a slot of this scheduler
// (the wait is after t.Parallel returns), so with few slots it says nothing about the test; this does, and
// scripts/gotest-shards.sh balances with these figures (docs/TESTING.md "Go tests").
func recordHold(name string, d time.Duration) {
	path := os.Getenv("JANUS_TEST_DURATIONS")
	if path == "" {
		return
	}
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_APPEND|os.O_CREATE, 0o600)
	if err != nil {
		return
	}
	fmt.Fprintf(f, "%s\t%.1f\n", name, d.Seconds())
	f.Close()
}

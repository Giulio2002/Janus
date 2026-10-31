package main

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// The prebuilt framework fixture (docs/TESTING.md "Go tests"). A framework build is expensive (the
// embedded framework's Lake build, and a kernel replay of it by `leanchecker Janus` for the embedded
// build and for this checkout's own build), and every test run used to repeat it in a fresh or shared
// cache. The fixture is a cache directory of its own, outside the user's cache (so no collector or
// other agent evicts it), keyed by the framework hash inside: built once per framework version by the
// first test run, under a lock, with `janus` itself (its Lake build, its sandboxed replay recording
// the verdicts); every later run copies the ready build and the authentic verdicts out of it into its
// own per-run test cache (seedFramework / seedCheckoutVerdict: the copy must hash as stamped, a
// verdict is accepted only if its MAC verifies under the fixture's key). The fixture is only read
// by the tests; a test that needs a mutable framework works on a copy (seededCache), and a test that
// checks the cold path (TestFrameworkReplayOnce, TestSeedFramework, ...) builds its own caches.
//
// JANUS_TEST_FIXTURE_DIR names the fixture directory (default <cache dir>/janus-test-fixture);
// "off" disables it (seeding then comes straight from the user's cache, JANUS_TEST_SEED_CACHE).

// fixturePart is JANUS_TEST_FIXTURE_PART: "" (the whole fixture), "embedded" (only the embedded framework's build and
// verdict: see ensureFixture), or "checkout" (the rest, after "embedded": the checkout's replay verdict, carried from the
// user's cache when it holds an authentic one, else replayed; the user's cache is never used for the framework build).
func fixturePart() string { return os.Getenv("JANUS_TEST_FIXTURE_PART") }

func fixtureDir() string {
	v := os.Getenv("JANUS_TEST_FIXTURE_DIR")
	if v == "off" {
		return ""
	}
	if v != "" {
		if abs, err := filepath.Abs(v); err == nil {
			return abs
		}
		return v
	}
	return filepath.Join(filepath.Dir(resolveTestCacheDir("")), "janus-test-fixture")
}

// ensureFixture makes fixture hold a ready build of the embedded framework and the replay verdicts
// of the embedded build and of this checkout's build, building what is missing under the fixture's
// lock. It changes JANUS_CACHE_DIR while it works and restores it. userSeed (a cache, or "") seeds
// a missing framework build before a cold one is built.
func ensureFixture(fixture, userSeed, exampleBin string) error {
	embeddedOnly := fixturePart() == "embedded"
	if embeddedOnly {
		// Only what depends on neither this checkout's build nor the user's cache: the embedded framework's build and its
		// replay verdict, built cold in the fixture. This is the gate's pre-fixture-emb stage, which starts at t=0 while
		// pre-lake, pre-stamp and pre-warm still write the checkout's build and the user's cache (scripts/lib/dag.sh).
		userSeed = ""
	}
	if err := os.MkdirAll(fixture, 0o755); err != nil {
		return err
	}
	lk, err := lockFileMode(filepath.Join(fixture, ".fixture.lock"), false, true)
	if err != nil {
		return err
	}
	defer lk.unlock()
	prev, had := os.LookupEnv("JANUS_CACHE_DIR")
	os.Setenv("JANUS_CACHE_DIR", fixture)
	defer func() {
		if had {
			os.Setenv("JANUS_CACHE_DIR", prev)
		} else {
			os.Unsetenv("JANUS_CACHE_DIR")
		}
	}()
	fw, err := loadFramework("")
	if err != nil {
		return err
	}
	lake, err := findLake()
	if err != nil {
		return err
	}
	// Other framework versions in the fixture are stale: remove them (this version's entry stays).
	if ents, err := os.ReadDir(filepath.Join(fixture, "v1", "framework")); err == nil {
		for _, e := range ents {
			if !strings.HasPrefix(e.Name(), fw.Sha256[:24]) {
				_ = os.RemoveAll(filepath.Join(fixture, "v1", "framework", e.Name()))
			}
		}
	}
	if fixturePart() != "checkout" && userSeed != "" && userSeed != "off" && filepath.Clean(userSeed) != filepath.Clean(fixture) {
		if _, err := seedFramework(userSeed, fixture); err != nil {
			fmt.Fprintf(os.Stderr, "janus tests: not seeding the fixture from %s: %v\n", userSeed, err)
		}
	}
	lease, err := fw.frameworkBase(lake, nil)
	if err != nil {
		return fmt.Errorf("building the fixture's framework: %w", err)
	}
	lease.release()
	embeddedKey := func() string {
		dir := filepath.Join(fixture, "v1", "framework", fw.Sha256[:24])
		tc, err := findToolchain(lake, dir)
		if err != nil {
			return ""
		}
		pins, err := frameworkPins(filepath.Join(dir, ".lake", "build", "lib", "lean"), fw.Files)
		if err != nil || len(pins.want) == 0 {
			return ""
		}
		return frameworkVerdictKey(tc.cacheID(), pins)
	}
	checkoutKey := func() string {
		if embeddedOnly {
			return ""
		}
		cfw, err := loadFramework(repoRoot)
		if err != nil {
			return ""
		}
		tc, err := findToolchain(lake, repoRoot)
		if err != nil {
			return ""
		}
		pins, err := frameworkPins(filepath.Join(repoRoot, ".lake", "build", "lib", "lean"), cfw.Files)
		if err != nil || len(pins.want) == 0 {
			return ""
		}
		return frameworkVerdictKey(tc.cacheID(), pins)
	}
	if !embeddedOnly && userSeed != "" && userSeed != "off" && filepath.Clean(userSeed) != filepath.Clean(fixture) {
		// The checkout's own replay verdict, when the user's cache holds an authentic one (pre-stamp's sandboxed
		// --janus-root verification recorded it there): carried (MAC checked under the user's key), not replayed again.
		seedCheckoutVerdict(userSeed, fixture)
	}
	var todo [][]string
	if k := embeddedKey(); k != "" && !hasFrameworkVerdict(k) {
		todo = append(todo, nil)
	}
	if k := checkoutKey(); k != "" && !hasFrameworkVerdict(k) {
		todo = append(todo, []string{"--janus-root", repoRoot})
	}
	if len(todo) == 0 {
		return nil
	}
	// One throwaway verification per missing verdict (a sandboxed run without --fresh records it).
	tmp, err := os.MkdirTemp(filepath.Dir(fixture), "janus-test-fixture-work-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(tmp)
	art := filepath.Join(tmp, "art")
	var o, e bytes.Buffer
	if code := run([]string{"extract", exampleBin, "example.com/basic.Add", art}, &o, &e); code != 0 {
		return fmt.Errorf("fixture: extract Add: %s", e.String())
	}
	for _, extra := range todo {
		o.Reset()
		e.Reset()
		args := append([]string{"verify", art, "--proof", filepath.Join(repoRoot, "examples", "proofs", "Add.lean")}, extra...)
		if code := run(args, &o, &e); code != 0 {
			return fmt.Errorf("fixture: verify %v: %s%s", extra, o.String(), e.String())
		}
	}
	return nil
}

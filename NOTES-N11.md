# NOTES-N11 (JN-INT handover)

Goal: integ/n11 = n10 edcc7b3b + agent/silent-dep 9ca511b1 + agent/implapart-lint 7d78716c + agent/up2-cache-orphan 944f8895 (rebased), full gate green.

Merge order / decisions:
1. silent-dep: `git merge --no-ff` (clean).
2. implapart-lint: `git merge --no-ff` (clean; touches verify.go + dynamic.go only).
3. up2-cache-orphan 944f8895 (based on 51d592da): `git cherry-pick` onto 1+2 -> da1197f3, NO textual conflicts (consumer.go/verify.go hunks are disjoint). Semantic check: replay now takes runIn(view,...) in both asl.go and consumer.go; silent-dep's lakeBuildGuarded touches different code in consumer.go.
4. Test fixes: JANUS_FRAMEWORK_STORE is a cache location (like GOCACHE/JANUS_POOL_DIR) -> incrEnvSkip (not the keyed list: its value is a per-host path, an entry is HMAC'd, re-hashed, pin-checked, kernel-replayed; any doubt = full compile), plus the pin in TestRT04EnvSkipListIsPinned. TestConsumerVerify "Max rebuilt": cause = shared content-keyed olean store of the process-wide test cache; another parallel consumer test (TestConsumerGit/ResultCache/...) compiled the identical Max.lean against the identical extraction first, so Max was a store hit, not listed in Rebuilt. Fix: test appends a per-test comment to Add.lean/Max.lean so its module keys are its own.
5. Found by the full gate (also fails on n10 as shipped): arm64 examples WriteTo and CountThenWrite had Witness.nonvacuous but no Witness.returns, while the sweep (verify-examples.sh / verify-amd64-examples.sh) demands both. Added `theorem returns` on both ISAs from correctness + the existing nonvacuous witness data; verified (correctness + nonvacuous + returns) with the n11 binary, all 4 files.

Scratch: /srv/janus-ops/work.n11 (gate logs, patch/). Gate: scripts/check-merge.sh -j 2 under heavy-run -s 2, memcap 96G, out dir /srv/janus-ops/work.n11/gate-out2.

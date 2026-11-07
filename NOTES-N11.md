# NOTES-N11 (JN-INT handover)

Goal: integ/n11 = n10 edcc7b3b + agent/silent-dep 9ca511b1 + agent/implapart-lint 7d78716c + agent/up2-cache-orphan 944f8895 (rebased), full gate green.

Merge order / decisions:
1. silent-dep: `git merge --no-ff` (clean).
2. implapart-lint: `git merge --no-ff` (clean; touches verify.go + dynamic.go only).
3. up2-cache-orphan 944f8895 (based on 51d592da): `git cherry-pick` onto 1+2 -> da1197f3, NO textual conflicts (consumer.go/verify.go hunks are disjoint). Semantic check: replay now takes runIn(view,...) in both asl.go and consumer.go; silent-dep's lakeBuildGuarded touches different code in consumer.go.
4. Test fixes: JANUS_FRAMEWORK_STORE is a cache location (like GOCACHE/JANUS_POOL_DIR) -> incrEnvSkip (not the keyed list: its value is a per-host path, an entry is HMAC'd, re-hashed, pin-checked, kernel-replayed; any doubt = full compile), plus the pin in TestRT04EnvSkipListIsPinned. TestConsumerVerify "Max rebuilt": cause = shared content-keyed olean store of the process-wide test cache; another parallel consumer test (TestConsumerGit/ResultCache/...) compiled the identical Max.lean against the identical extraction first, so Max was a store hit, not listed in Rebuilt. Fix: test appends a per-test comment to Add.lean/Max.lean so its module keys are its own.
5. Found by the full gate (also fails on n10 as shipped): arm64 examples WriteTo and CountThenWrite had Witness.nonvacuous but no Witness.returns, while the sweep (verify-examples.sh / verify-amd64-examples.sh) demands both. Added `theorem returns` on both ISAs from correctness + the existing nonvacuous witness data; verified (correctness + nonvacuous + returns) with the n11 binary, all 4 files.

Scratch: /srv/janus-ops/work.n11 (gate logs, patch/). Gate: scripts/check-merge.sh -j 2 under heavy-run -s 2, memcap 96G, out dir /srv/janus-ops/work.n11/gate-out2.

## U-ICALL-STACK relaxation (commit a73aa4e9, Janus/Tools/Audit.lean `onlyLowerBounded`/`belowFree`)
Why: n10's rule rejected 15 verified examples (AlgMemhash*, AlgF*hash, AlgC*hash, Alg*interhash, AlgStrequal, AlgMemequalVarlen, Mbar*) whose statements say `d' + F <= d`.
Rule for a size variable v (stack/d/above/nargs argument of a contract): every premise mentioning v is (a) a contract hypothesis, (b) a numeral lower bound `c <= v` / `c < v` (c < limit), or NEW (c) `v <= w`, `v < w`, `v + c <= w` (Nat, c a closed numeral < limit) where w is:
 - a variable bound by the statement, not a runtime variable (impl, rt, R, H ...), not itself a size argument of any contract, and w != v;
 - mentioned ONLY by premises of the shape `X <= w` / `X < w` (Nat, w alone on the right, X free of w). Any other premise on w (=, w <= ..., w + .. <= .., an existential/conjunction, a pin through another variable) makes w ineligible, and then the premise on v is rejected.
Reasoning: w is only bounded from below, so it can be chosen after v; nothing can pin v from above through it. Known conservative limit: occurrences of w in the conclusion or in contract hypotheses are not inspected (a contract hypothesis mentioning w is skipped like for v).
Regression rows (JanusTests/ICallAudit.lean): accepted shapes plus adversarial rejects: chain pin (m = 2^48, m <= k), alias pin, existential pin, two lower bounders with one pinned, m <= k /\ k <= m, k+48<=m<=k+48, bound via another variable pinned, self-bound, and the same on above, nargs and the NewobjectContract d family. Controls: the 15 real examples, verified in the sweep (verify lane) and round 11 L1_ctl_AlgMemhash16.
Gap that let edcc7b3b ship "green": only build/SAT/axiom/lint/vet were run there; the example sweep (check-merge verify lane) and audit round r11 were NOT, and both catch it. Close it: any change to Janus/Tools/Audit.lean must trigger the verify sweep + rounds before a head is called green.

## Gate result
check-merge (verify+gotest+rounds+axiom+govet), -j 2, head a73aa4e9: GATE PASS 2h08m17s (gotest 29m08s, rounds 1h01m41s). Earlier runs failed for the reasons fixed above (WriteTo/CountThenWrite returns, ErrWrap literal, U-ICALL-STACK shape, TestRT04 pin).

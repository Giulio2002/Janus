# NOTES-N12 (JN-INT handover) -- branch agent/integ-n12, worktree /srv/janus-integ-n12
n12 = n11 b8ac6cca + agent/up4-sandbox 217f0136 + agent/up3-vacuity (INTERIM 364b7ac6; take UP3c's final head once green, then fast-forward/merge and rerun check-merge + SAT).

## Merge decisions
- up4 is based on b8ac6cca: merged --no-ff, clean. NOTE: up4's last commit (217f0136) committed a 23 MB build artifact `janus-up4` at the repo root; removed in the integration commit and added to .gitignore (audit/up4/run-hermetic.sh rebuilds it when missing). Tell UP4 owner.
- up3-vacuity: one textual conflict, .gitignore (up4 `audit/up4/work` vs up3 `.sw/`, `bin/`): kept all. No conflicts in cmd/janus (sandbox.go/consumer.go vs nonvacuity.go/verify.go merged automatically; hunks disjoint: consumer.go +Refutation field only). audit/run-all.sh had no conflict.
- Result-cache key (cmd/janus/resultcache.go, both the single and the consumer key): contains literal `sandbox hermetic-v2 <mode> <bwrap>` (up4) AND the verifier identity (content hash of the janus source, which includes nonvacuity.go) AND `auditor <auditExeSha>` (the Lean audit exe, which carries the witness rule in Janus/Tools/Audit.lean). So the witness-rule version is keyed through the auditor + verifier hashes; there is no separate constant. NonVacuity fields are "set after the run, never cached". 
- Behaviour changes from up3 to be aware of: `--allow-no-witness` replaced by `--audit-only` (not a verification; prints "Audit-only:"), dev hook JANUS_STOP_AFTER_AUDIT=1 (reports failure with AUDIT-STAGE-OK, never a verification), new report field `refutation`.

## Evidence log
(filled in below as jobs finish; scratch /srv/janus-ops/work.n12)

### 2026-11-08 12:24 go test ./cmd/janus on 7297a8e7 (n11 + up4 217f0136 + up3 531bf915): FAIL, 42 tests, wall 4796s
Root cause seen in the log: the UP3 policy "EVERY main theorem is verified ONLY together with a verified Witness.nonvacuous that carries the returning run; --allow-no-witness is ignored" fails the Go test fixtures that verify the plain Add/ConsumerExample proofs (fixture build itself: "fixture: verify ... has no kernel-checked non-vacuity witness"), so everything depending on the fixture/priming verify fails (TestVerify, TestConsumerVerify, TestVerifyBatch, TestResultCache, TestConcurrentVerify, TestRound5/6, TestJ1*, TestRound15aPlantedOlean, TestVerifyStageBudgets*, TestCacheGC*, ...). up3 has moved on since 531bf915 (1b256ba7 "run-free main statements exempt (runFree)", bef54b41, 66f9e956 rtmisc witnesses), which likely changes this; NOT edited here. Next: take UP3c's final head, rerun go test. Full log: /srv/janus-ops/work.n12/gotest.log.

# UP2 handover
Branch agent/up2-cache-orphan off 51d592da. Two commits: replay closure view (U-ORPHAN-OLEAN), Extracted-reaching module keys (U-CACHE-EXTRACT).
Tests: TestClosureViewExact, TestOrphanOleanIgnored, TestOwnModuleKeyExtraction, TestConsumerMidAcrossExtractions.
Gate: go test ./cmd/... : only failures are pre-existing on n10 (TestIncr2EveryGateExportIsClassified, TestIncr2ExportScanCatchesEveryForm, TestConsumerVerify "Max rebuilt [Extracted]" under parallel). Lean untouched.
Not rebased onto icall-stack (not merged into n10 yet when handed in).

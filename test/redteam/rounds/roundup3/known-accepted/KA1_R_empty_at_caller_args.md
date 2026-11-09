# KA1 (known-accepted / post-release): R empty only at the arguments of a call no witness run takes
Statement: the Ensures precondition pins `¬ R a b c d e f g` for the SPECIFIC argument values the caller passes to the callee (not `∀`), so the
real call can never return and the post holds vacuously on that path. The witness exhibits a tied call-site state `s_c` (U-WITNESS-CALLSITE) at the
callee entry with the contract pre holding, but at DIFFERENT argument registers where R is non-empty, and proves the contract for a concrete
callee. Nothing requires that the caller's path reaches the call with the pinned arguments, so the witness is accepted.
Status: ACCEPTED, documented limitation (docs/SOUNDNESS.md "UP3: known limitation"). Universal pins (R01: `∀ a…g, ¬R …`) ARE rejected.
Post-release queue: optional reachability witnesses (a `Steps` prefix from `s` to `s_c`) for rows where it is cheap.

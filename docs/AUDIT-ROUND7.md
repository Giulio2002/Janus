# Audit round 7: the verification-result cache

`janus verify` records the result of a successful sandboxed verification and prints it again,
marked `Cached:`, when every input is the same (docs/SOUNDNESS.md, "Verification-result cache").
That makes the cache a trusted component: a forged or stale entry would print `Verified` for a
proof that was never checked. This round attacks it. Runner: `audit/round7/run-round7.sh`
(attack files in `audit/round7/attacks/`, the lakefile attack is the `resultcache` mode of
`audit/attacks/R1_pkg`).

| Row | Attack | Expected | Result |
|---|---|---|---|
| RC1_proof_probe_bwrap | a proof's `#eval` reads `$JANUS_CACHE_DIR/v1/result/.key`, lists the entries, writes `planted-by-proof` (bubblewrap) | blocked: the directory is an empty tmpfs inside the sandbox (the proof compiles and verifies, sees nothing), nothing reaches the host | blocked |
| RC1_proof_probe_unshare | the same under the unshare fallback | blocked (the script mounts the same tmpfs, strictly) | blocked |
| RC2_lakefile_probe | a consumer lakefile does the same while Lake elaborates it | blocked: Lake runs sandboxed, sees an empty directory | blocked |
| RC3_tampered_entry | a recorded entry is edited on disk so its statement reads `x * y` | blocked: the HMAC does not verify, the entry is ignored, the verification runs and prints `x + y` | blocked |
| RC4_stale_framework | an entry recorded with a `--janus-root` framework is looked up after a framework source changes | blocked: the framework's hash (and its rebuilt pins) are part of the key | blocked |
| RC5_fresh_bypasses | `--fresh` | never uses the cache | blocked |
| RC6_unsandboxed_bypasses | `--unsafe-no-sandbox` | never uses the cache | blocked |

`TestResultCache` (cmd/janus) checks the same properties in `go test`: a hit prints exactly the
fresh output plus `Cached:`, an edited proof misses, a tampered entry is ignored, `--fresh` and
`--unsafe-no-sandbox` bypass the cache.

Not attacked here, because they are outside the threat model (docs/SOUNDNESS.md): a user who
can write `~/.cache/janus` directly (they can equally replace the framework build), and a proof
run with `--unsafe-no-sandbox` (it runs with the user's privileges).

There is no verification daemon, so there is no row for one (docs/TESTING.md explains why).

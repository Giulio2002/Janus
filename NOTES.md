
## ASLOBJ2 checkpoint
- Merged main (clean, no conflicts). Tests pass: test_asl_obj_cache, test_asl_mod_cache, test-restamp, test-bcache, test-dag.
- Review: key = armasl key (toolchain content incl. clang/leanc, flags, env, machine) + sha of every emitted .c; HMAC manifest; Lake trace re-judges each object.
- Measurement running in /srv/janus-ops/work.jIKT (log: log); delete when result recorded.
- jasl scope added (second armobj entry); warm asl-build 58 s (was 1220-1520 s cold-obj, 612 s with arm scope only). Work dir deleted.

Round-2 amd64 audit: LOCK atomics, fences, REP string ops, SSE moves (commit 4738a73 and
later; audited tree = agent/redteam2 at 8bf7610). Nothing here edits the framework.

Run everything from a COPY of the repo (never inside /srv worktrees):

  cp -a /srv/janus-rt2 $X/j && cd $X/j
  lake build Janus
  PATH=$PATH:/usr/local/go/bin scripts/build-examples-amd64.sh     # artifacts/amd64/*

Files
-----
Probe.lean          decoder acceptance/rejection of ~80 encodings (prefix combinations on
                    string ops, LOCK on every form, SSE/AVX/fences/FS/GS/67).
                    lake env lean audit/round2/amd64/Probe.lean
ExecProbe.lean      executor on concrete states (IMUL/IDIV signs, CMPXCHG 32-bit RAX
                    write-back on success/failure, CMPXCHG8B, XADD AH, REP with RCX = 0 and
                    unmapped pointers, overlapping REP MOVSB, BSF/LZCNT/TZCNT, MOVAPS/XORPS/
                    CMPXCHG16B alignment, 87 C0 vs 90).
                    lake env lean audit/round2/amd64/ExecProbe.lean
host/probe.c        the same cases on the host CPU (plus DF = 1 REP MOVSB copying backwards):
                    gcc -O1 -o /tmp/probe host/probe.c && /tmp/probe
                    All values agree with ExecProbe (host: Intel Xeon Gold 5412U).
host/splitlock.c    LOCK XADDQ across a 64-byte line: #AC split-lock trap (dmesg), SIGBUS
                    under split_lock_detect=fatal.
build-controls.sh   compiles Extracted + the shipped Proof for AtomicAdd AtomicMax CopyWords
                    CopyBlock ClearWords into work/<E>/ and checks controls/<E>_witness.lean:
                    audit/round2/amd64/build-controls.sh          (all five; ~2 min, ClearWords
                    proof is the slow one)
controls/*_witness.lean
                    positive controls: an explicit call state satisfying CallSetup + the
                    precondition, the theorem instantiated, and a concrete conclusion
                    (AtomicAdd 40+2 -> 42; AtomicMax max(40,50); CopyWords n = 2 and the words;
                    CopyBlock the 128 source bytes; ClearWords 300 words through REP STOSQ with
                    HasERMS = 1, plus an #eval of the model run). None is vacuous.
                    AtomicAdd_witness also instantiates the theorem at a cache-line-straddling
                    p = 0x203C (finding R2-A1).
controls/DFMemmove.lean
                    finding R2-A2: a kernel-checked, `janus verify`-accepted theorem about
                    runtime.memmove's REP MOVSQ at 0x47d6e9 (right after STD) saying it copies
                    forward; on hardware every state at that PC has DF = 1.
                    after build-controls.sh:
                    LEAN_PATH=$PWD/audit/round2/amd64/work/CopyBlock:$(lake env printenv LEAN_PATH) \
                      lake env lean audit/round2/amd64/controls/DFMemmove.lean
                    bin/janus verify artifacts/amd64/CopyBlock \
                      --proof audit/round2/amd64/controls/DFMemmove.lean \
                      --theorem DFRepro.memmove_backward_rep_copies_forward   # prints Verified

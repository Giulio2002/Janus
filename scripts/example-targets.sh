#!/usr/bin/env bash
# Print the extra `janus extract` arguments of an examples/basic function, one per line: the
# dynamic call targets its theorem states, or the runtime contracts it leaves out (docs/PROOFS.md, "Dynamic calls"). Nothing for most
# functions. Used by scripts/verify-examples.sh and scripts/build-examples-amd64.sh.
case "$1" in
  HashWith) # the static itabs of the two Hasher implementations
    printf '%s\n' --targets \
      'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher,go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher' ;;
  MapSum) # the closure AffineSum passes to it
    printf '%s\n' --targets example.com/basic.AffineSum.func1 ;;
  # heap allocation (docs/RUNTIME-CONTRACTS.md): the runtime functions left out as contracts
  NewPair|MakeSlice|AppendOne)
    printf '%s\n' --contract runtime.mallocgc --contract runtime.newobject \
      --contract runtime.makeslice --contract runtime.growslice ;;
  SetNext) # the write barrier's fast path is executed; only its buffer flush is left out
    printf '%s\n' --contract runtime.wbBufFlush ;;
  MallocFast) # runtime.mallocgc's slow paths, unreachable under the theorem's precondition
    printf '%s\n' --contract runtime.mallocgcTiny --contract 'runtime.mallocgcSmallScan*' \
      --contract runtime.mallocgcLarge --contract runtime.deductAssistCredit \
      --contract runtime.preMallocgcDebug --contract runtime.postMallocgcDebug \
      --contract runtime.throw --contract 'runtime.(*mcache).nextFree' \
      --contract runtime.memclrNoHeapPointers --contract runtime.gcmarknewobject \
      --contract runtime.profilealloc --contract runtime.gcTrigger.test --contract runtime.gcStart ;;
esac

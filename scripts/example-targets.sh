#!/usr/bin/env bash
# Print the extra `janus extract` arguments of an examples/basic function, one per line: the
# dynamic call targets its theorem states, or the runtime contracts it leaves out (docs/PROOFS.md, "Dynamic calls"). Nothing for most
# functions. Used by scripts/verify-examples.sh and scripts/build-examples-amd64.sh.
case "$1" in
  # stack growth (R7, docs/RUNTIME-CONTRACTS.md "Stack growth"): the functions' pclntab frame
  # records (SP deltas, stack maps), which the theorems' frame tables agree with
  BigLocal|SumRec|HoldPtr) printf '%s\n' --frames ;;
  HashWith) # the static itabs of the two Hasher implementations
    printf '%s\n' --targets \
      'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher,go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher' ;;
  MapSum) # the closure AffineSum passes to it
    printf '%s\n' --targets example.com/basic.AffineSum.func1 ;;
  # the generic shape function total[go.shape.uint64] calls Scale through the instantiation's
  # dictionary (examples/basic/zconstructs.go)
  TotalMeters) printf '%s\n' --targets example.com/basic.Meters.Scale ;;
  TotalFeet) printf '%s\n' --targets example.com/basic.Feet.Scale ;;
  # heap allocation (docs/RUNTIME-CONTRACTS.md): the runtime functions left out as contracts
  NewPair|MakeSlice|AppendOne|MakeAdder)
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
  # the map examples (examples/basic/maps.go): the Go 1.26 map runtime entry points they call
  # (Janus/Contracts/Map.lean, Janus/Contracts/MapAmd64.lean)
  Lookup) printf '%s\n' --contract runtime.mapaccess2_fast64 ;;
  Insert) printf '%s\n' --contract runtime.mapassign_fast64 ;;
  InsertGet) printf '%s\n' --contract runtime.mapassign_fast64 --contract runtime.mapaccess1_fast64 ;;
  Delete) printf '%s\n' --contract runtime.mapdelete_fast64 ;;
  SumValues) printf '%s\n' --contract runtime.mapIterStart --contract runtime.mapIterNext ;;
  LookupKey16) printf '%s\n' --contract runtime.mapaccess2 ;;
  NewMap) printf '%s\n' --contract runtime.makemap_small ;;
  ClearMap) printf '%s\n' --contract runtime.mapclear ;;
  # the interface examples (examples/basic/iface.go): the Go 1.26 interface runtime entry points
  # they call (Janus/Contracts/Iface.lean, IfaceAmd64.lean; pinned to the runtime's code), and
  # the static itab the assertion and switch theorems name
  Box) printf '%s\n' --contract runtime.convT64 ;;
  AsHasher) printf '%s\n' --contract runtime.typeAssert --targets \
      'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher' ;;
  Classify) printf '%s\n' --contract runtime.interfaceSwitch --targets \
      'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher' ;;
  Equal) printf '%s\n' --contract runtime.efaceeq ;;
  # the panic/defer/recover examples (examples/basic/rtpanic.go): PanicIf, IndexAt and LoadField
  # need no extra arguments (they reach runtime.gopanic / runtime.panicBounds as panic stubs, or
  # fault); DeferInc's open-coded closure is inferred. The heap-defer and recover functions leave
  # the Go 1.26 panic runtime out as pinned contracts (Janus/Contracts/Panic.lean).
  DeferLoop|DeferTwice) printf '%s\n' --contract 'runtime.deferproc*' --contract runtime.deferreturn ;;
  RecoverSet) printf '%s\n' --contract runtime.gopanic --contract runtime.gorecover \
      --contract runtime.deferreturn ;;
esac

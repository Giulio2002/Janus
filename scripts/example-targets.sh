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
  # the string and slice examples (examples/basic/zstr.go): Janus/Contracts/String.lean,
  # Slice.lean (and the runtime functions proved to meet their contracts)
  Concat) printf '%s\n' --contract runtime.concatstring2 ;;
  ToBytes) printf '%s\n' --contract runtime.stringtoslicebyte ;;
  FromBytes) printf '%s\n' --contract runtime.slicebytetostring ;;
  SumRunes|Countrunes) printf '%s\n' --contract runtime.decoderune ;;
  RuneLen) printf '%s\n' --contract runtime.countrunes ;;
  AppendPoint) printf '%s\n' --contract runtime.growslice ;;
  CopyNodes) printf '%s\n' --contract runtime.typedslicecopy ;;
  WriteBarrier) printf '%s\n' --targets runtime.gcWriteBarrier2,runtime.gcWriteBarrier3,runtime.gcWriteBarrier4,runtime.gcWriteBarrier5,runtime.gcWriteBarrier6,runtime.gcWriteBarrier7,runtime.gcWriteBarrier8 \
    --contract runtime.wbBufFlush ;;
esac

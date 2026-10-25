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
  # the equality, hashing and typed-memory examples (examples/basic/rteq.go;
  # Janus/Contracts/Mem*.lean, Hash*.lean; pinned to the runtime's code)
  StrEq) printf '%s\n' --contract runtime.memequal ;;
  CopyTrees) printf '%s\n' --contract runtime.typedmemmove ;;
  ClearTrees) printf '%s\n' --contract runtime.memclrHasPointers ;;
  LookupStr) printf '%s\n' --contract runtime.mapaccess2_faststr ;;
  LookupFKey) printf '%s\n' --contract runtime.mapaccess1 ;;
  HashFKey) printf '%s\n' --contract runtime.f64hash --contract runtime.strhash ;;
  EqFKey) printf '%s\n' --contract runtime.memequal ;;
  # the runtime's equality, hashing and typed-memory functions verified from their machine code,
  # with the runtime functions they call as contracts
  AlgStrequal|AlgMemequalVarlen) printf '%s\n' --contract runtime.memequal ;;
  AlgInterequal) printf '%s\n' --contract runtime.ifaceeq ;;
  AlgNilinterequal) printf '%s\n' --contract runtime.efaceeq ;;
  AlgF32hash|AlgF64hash) printf '%s\n' --contract runtime.rand --contract runtime.memhash ;;
  AlgC64hash) printf '%s\n' --contract runtime.f32hash ;;
  AlgC128hash) printf '%s\n' --contract runtime.f64hash ;;
  AlgMemhash8|AlgMemhash16|AlgMemhash128|AlgMemhashVarlen) printf '%s\n' --contract runtime.memhash ;;
  AlgInterhash|AlgNilinterhash) printf '%s\n' --contract runtime.typehash \
      --contract runtime.rtype.string --contract runtime.concatstring2 --contract runtime.convTstring ;;
  MbarTypedmemmove) printf '%s\n' --contract runtime.memmove --contract runtime.bulkBarrierPreWrite ;;
  MbarTypedmemclr|MbarMemclrHasPointers) printf '%s\n' --contract runtime.memclrNoHeapPointers \
      --contract runtime.bulkBarrierPreWrite ;;
esac

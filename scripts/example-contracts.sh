# Sourced by the example scripts: the `janus extract --contract` flags of each example function
# (docs/RUNTIME-CONTRACTS.md). Functions not listed are extracted without contracts.
example_contracts() {
  case "$1" in
    NewPair|MakeSlice|AppendOne)
      echo --contract runtime.mallocgc --contract runtime.newobject --contract runtime.makeslice --contract runtime.growslice ;;
    SetNext)
      # The write barrier's fast path (gcWriteBarrier2, gcWriteBarrier) is extracted and
      # executed; only its buffer-flush slow path is left out.
      echo --contract runtime.wbBufFlush ;;
    MallocFast)
      # runtime.mallocgc's small pointer-free fast path is executed; every slow path is a
      # contract, unreachable under the theorem's precondition (MCacheOK).
      echo --contract runtime.mallocgcTiny --contract 'runtime.mallocgcSmallScan*' \
        --contract runtime.mallocgcLarge --contract runtime.deductAssistCredit \
        --contract runtime.preMallocgcDebug --contract runtime.postMallocgcDebug \
        --contract runtime.throw --contract 'runtime.(*mcache).nextFree' \
        --contract runtime.memclrNoHeapPointers --contract runtime.gcmarknewobject \
        --contract runtime.profilealloc --contract runtime.gcTrigger.test --contract runtime.gcStart ;;
  esac
}

# The symbol an example proves things about (default: example.com/basic.<Name>).
example_symbol() {
  case "$1" in
    MallocFast) echo runtime.mallocgc ;;
    *) echo "example.com/basic.$1" ;;
  esac
}

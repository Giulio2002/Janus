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
  esac
}

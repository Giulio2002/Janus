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
    # The map examples (examples/basic/maps.go): the Go 1.26 map runtime entry points they call
    # (Janus/Contracts/Map.lean, Janus/Contracts/MapAmd64.lean).
    Lookup) echo --contract runtime.mapaccess2_fast64 ;;
    Insert) echo --contract runtime.mapassign_fast64 ;;
    InsertGet) echo --contract runtime.mapassign_fast64 --contract runtime.mapaccess1_fast64 ;;
    Delete) echo --contract runtime.mapdelete_fast64 ;;
    SumValues) echo --contract runtime.mapIterStart --contract runtime.mapIterNext ;;
    LookupKey16) echo --contract runtime.mapaccess2 ;;
    NewMap) echo --contract runtime.makemap_small ;;
    ClearMap) echo --contract runtime.mapclear ;;
  esac
}
